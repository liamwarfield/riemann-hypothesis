module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP.Height
private theorem matrix_map_smul {R S : Type*} [CommRing R] [CommRing S] {d : ℕ} (F : R →+* S) (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map F = F c • M.map F := by
  ext i j; simp

private theorem frobenius_height_matrix_relation {R D : Type*} [CommRing R] [CommRing D] {d : ℕ} (t : R →+* D)
    (ht : Function.Injective t) (φ : R →+* R) (Φ : D →+* D) (hΦ : ∀ a, Φ (t a) = t (φ a)) (n k m : ℕ) (a b : R)
    (Af Ag x : Matrix (Fin d) (Fin d) R) (ε : Matrix (Fin d) (Fin d) D) (hx : x.map t = (n : D) ^ k • ε)
    (key : t b ^ m • (Af.map t * ε.map Φ) = t a ^ m • (ε * Ag.map t)) :
    b ^ m • (Af * x.map φ) = a ^ m • (x * Ag) := by
  have hxφ : (x.map φ).map t = (n : D) ^ k • ε.map Φ := by
    have h1 : (x.map φ).map t = (x.map t).map Φ := by
      ext i j; simp only [Matrix.map_apply]; exact (hΦ (x i j)).symm
    rw [h1, hx]; ext i j; simp
  apply Matrix.map_injective ht
  simp only [Matrix.map_mul, matrix_map_smul, map_pow]
  rw [hxφ, hx, Matrix.mul_smul, Matrix.smul_mul, smul_comm _ ((n : D) ^ k), smul_comm _ ((n : D) ^ k), key]

theorem phi_eq_of_rel_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)), ht.Rel (BK.hf f X) f g ε → x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε → BK.hf g bk.E ^ (ht.a + s.N) • (ht.A.map (BK.hf f) * x.map B.D.φ) = BK.hf f bk.E ^ (ht.a + s.N) • (x * ht.A.map (BK.hf g)) := by
  intro l _ K bk d ρ τ s ht hper B f g ι hb k x ε hrel hx
  obtain ⟨hinj, hE, -, -⟩ := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι hb
  have hφ : ‖toDisc l (BK.hf f X) bk.ρ₀ (B.D.φ (BK.hf f X))‖ ≤ bk.ρ₀ := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f f).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ :=
    ⟨_, isDiscMap_map B.D.φ hφ⟩
  exact frobenius_height_matrix_relation _ hinj B.D.φ Φ hΦ.ext l k _ _ _ _ _ x ε hx
    (GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hE f g ε hrel Φ hΦ)

end GlobalTheory.BSP.Height
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEqOfPowSmulComparisonMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)), ht.Rel (BK.hf f X) f g ε → x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε → BK.hf g bk.E ^ (ht.a + s.N) • (ht.A.map (BK.hf f) * x.map B.D.φ) = BK.hf f bk.E ^ (ht.a + s.N) • (x * ht.A.map (BK.hf g)) := by
  first | exact @GlobalTheory.BSP.Height.phi_eq_of_rel_pow | exact GlobalTheory.BSP.Height.phi_eq_of_rel_pow | (intros; apply GlobalTheory.BSP.Height.phi_eq_of_rel_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHom
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.Height

theorem isDiscMap_comp' {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A'']
    {u : A} {u' : A'} {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''}
    {F : Disc l u ρ →+* Disc l u' ρ'} {G : Disc l u' ρ' →+* Disc l u'' ρ''}
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hG : IsDiscMap (l := _) (u := _) (ρ := _) g G) : IsDiscMap (l := _) (u := _) (ρ := _) (g.comp f) (G.comp F) :=
  ⟨fun a => by simp [hF.ext, hG.ext], fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem rel_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  intro l _ K bk d ρ τ s ht B B' f₀ f g f₀' k ε hrel
  have hk : ‖toDisc l (BK.hf f₀' X) bk.ρ₀ (k.f (BK.hf f₀ X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B' f₀' (k.comp f₀)).1
  refine ⟨⟨Disc.map k.f hk, isDiscMap_map k.f hk⟩, ?_⟩
  intro Fk hFk Ff' Fg' hf' hg'
  have hff := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ f).1
  have hgg := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ g).1
  have h := congrArg (fun M => Matrix.map M Fk)
    (hrel _ _ (isDiscMap_map (BK.hf f) hff) (isDiscMap_map (BK.hf g) hgg))
  have e1 : Fk.comp (Disc.map (BK.hf f) hff) = Ff' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf f) hff) hFk).unique hf'
  have e2 : Fk.comp (Disc.map (BK.hf g) hgg) = Fg' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf g) hgg) hFk).unique hg'
  subst e1 e2
  ext i j
  have h2 := congrFun (congrFun h i) j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_mul, map_pow, map_sum, smul_eq_mul,
    hFk.ext, RingHom.comp_apply] at h2 ⊢
  exact h2

end GlobalTheory.BSP.Height
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriod_comparison_relation_map_prismHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  first | exact @GlobalTheory.BSP.Height.rel_map | exact GlobalTheory.BSP.Height.rel_map | (intros; apply GlobalTheory.BSP.Height.rel_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDisc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem comparisonMatrix_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  intro l _ K bk d ρ τ s ht hper B f g ι tb ε hrel
  have hnorm := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f g
  let Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀ := Disc.map B.D.φ hnorm.2
  have hΦ : IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ := isDiscMap_map _ _
  have hreg := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι tb
  have hpair := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  have heq := GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hreg.2.1 f g ε hrel Φ hΦ
  have hQ : ht.A.map (BK.hf g) * ht.A'.map (BK.hf g) =
      BK.hf g bk.E ^ ht.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
    rw [← Matrix.map_mul (f := BK.hf g), ht.A_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  obtain ⟨h, c, hc⟩ := GlobalTheory.T.matrix_phi_equation_to_family_equation B.A (Disc l (BK.hf f X) bk.ρ₀) (toDisc l (BK.hf f X) bk.ρ₀) Φ
    (BK.hf f bk.E) (BK.hf g bk.E) hpair.2.1 d d (ht.a + s.N) (ht.a + s.N) ht.b (ht.A.map (BK.hf f))
    (ht.A.map (BK.hf g)) (ht.A'.map (BK.hf g)) hQ ε heq
  have hφX : B.D.φ (BK.hf f X) = BK.hf f X ^ l := by
    have h1 : B.D.φ (f.f X) = f.f (bk.prism.D.φ X) := (f.f_φ X).symm
    have h2 : bk.prism.D.φ X = X ^ l := frobS_X l bk.a
    exact h1.trans ((congrArg f.f h2).trans (map_pow f.f _ l))
  have key := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk B.A (BK.hf f) ι tb B.D.φ hφX Φ hΦ (Fin d × Fin d) c
    (fun _ _ => Set.toFinite _) h (fun j => ε j.1 j.2)
  have htend : Filter.Tendsto (fun j : Fin d × Fin d => ε j.1 j.2) Filter.cofinite
      (nhds (0 : Disc l (BK.hf f X) bk.ρ₀)) := by
    simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  have hsum : ∀ j : Fin d × Fin d, HasSum (fun i => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
      (toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2) := fun j => by
    have hs := hasSum_fintype (fun i : Fin d × Fin d => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
    have e : toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2 =
        ∑ k : Fin d × Fin d, Φ (ε k.1 k.2) * toDisc l (BK.hf f X) bk.ρ₀ (c k j) := hc j
    convert hs using 1
  have k2 := key htend hsum
  obtain ⟨k, v, hv, -⟩ := k2
  refine ⟨k, Matrix.of fun i j => v (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (i, j)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  first | exact @GlobalTheory.BSP.comparisonMatrix_bounded | exact GlobalTheory.BSP.comparisonMatrix_bounded | (intros; apply GlobalTheory.BSP.comparisonMatrix_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdGaloisComparisonMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdGaloisComparisonMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_dvd_map_of_smul_eq {A D W : Type} [CommRing A] [CommRing D] [CommRing W] {n : Type} [Fintype n]
    [DecidableEq n] (i : A →+* D) (hi : Function.Injective i) (j : A →+* W) (t t' : A) (N l k : ℕ)
    (M Y y : Matrix n n A) (ε : Matrix n n D) (h : i t ^ N • M.map i = i t' ^ N • (Y.map i * ε))
    (hy : y.map i = (l : D) ^ k • ε) (ht : IsUnit (j t')) (hY : IsUnit (Y.map j)) (a b : n) :
    (l : W) ^ k ∣ j (y a b) := by
  have h1 : ((l : A) ^ k * t ^ N) • M = t' ^ N • (Y * y) := by
    apply Matrix.map_injective hi
    change (((l : A) ^ k * t ^ N) • M).map i = (t' ^ N • (Y * y)).map i
    have e1 : (((l : A) ^ k * t ^ N) • M).map i = (l : D) ^ k • (i t ^ N • M.map i) := by
      ext p q; simp [mul_assoc]
    have e2 : (t' ^ N • (Y * y)).map i = i t' ^ N • (Y.map i * y.map i) := by
      rw [← Matrix.map_mul]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    rw [e1, e2, h, hy, Matrix.mul_smul, smul_comm]
  have h2 : (l : W) ^ k • (j t ^ N • M.map j) = j t' ^ N • (Y.map j * y.map j) := by
    have e := congrArg (fun Z : Matrix n n A => Z.map j) h1
    rw [← Matrix.map_mul]
    ext p q
    have := congrFun (congrFun e p) q
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast, mul_assoc]
      using this
  obtain ⟨u, hu⟩ := hY
  obtain ⟨v, hv⟩ := ht.pow N
  have h3 : y.map j = (l : W) ^ k • ((↑v⁻¹ : W) • ((↑u⁻¹ : Matrix n n W) * (j t ^ N • M.map j))) := by
    rw [smul_comm, ← Matrix.mul_smul, h2, ← hu, ← hv, Matrix.mul_smul, ← mul_assoc, Units.inv_mul, one_mul,
      smul_smul, Units.inv_mul, one_smul]
  exact ⟨_, congrFun (congrFun h3 a) b⟩

theorem pow_dvd_of_rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  intro l _ K bk d ρ τ s ht hτ _ g ε hε k y hy i j
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨-, hu, hsat⟩ := GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ
  exact hsat k _ (pow_dvd_map_of_smul_eq bk.iA (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1 (inclW l) τ _ s.N l k
    _ ht.Y y ε (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g ε hε) hy (hu g) ht.unit i j)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowDvdGaloisComparisonMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_dvd_galoisComparison_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → ∀ (k : ℕ) (y : Matrix (Fin d) (Fin d) (Ainf l)), y.map bk.iA = ((l : ℕ) : bk.DA bk.ρ₀) ^ k • ε → ∀ i j, ((l : ℕ) : Ainf l) ^ k ∣ y i j := by
  first | exact @GlobalTheory.BSP.pow_dvd_of_rel_gal | exact GlobalTheory.BSP.pow_dvd_of_rel_gal | (intros; apply GlobalTheory.BSP.pow_dvd_of_rel_gal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDisc
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RelEx

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m n : Type} (a : R)
    (M : Matrix m n R) : (a • M).map φ = φ a • M.map φ := by
  ext i j; simp

theorem alg {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (N : ℕ)
    (A Zf Zfi G Y Zg : Matrix n n R) (gE fE wi c lam : R) (hZ : Zf * Zfi = 1) (hAG : A * G = lam • Y)
    (hw : gE * wi = fE) (hc : c * lam = 1) :
    gE ^ N • (A * Zf * ((wi ^ N * c) • (Zfi * G * Zg))) = fE ^ N • (Y * Zg) := by
  have h1 : A * Zf * (Zfi * G * Zg) = lam • (Y * Zg) := by
    rw [Matrix.mul_assoc A Zf, ← Matrix.mul_assoc Zf, ← Matrix.mul_assoc Zf, hZ, Matrix.one_mul,
      ← Matrix.mul_assoc, hAG, Matrix.smul_mul]
  rw [Matrix.mul_smul, h1, smul_smul, smul_smul]
  congr 1
  calc gE ^ N * (wi ^ N * c) * lam = (gE * wi) ^ N * (c * lam) := by ring
    _ = fE ^ N := by rw [hw, hc, mul_one]

theorem cancel {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (Xf X'f Y G : Matrix n n R)
    (e lk lc : R) (he : e ∈ nonZeroDivisors R) (hXX : Xf * X'f = (lc * e) • 1) (hG : e • G = lk • (X'f * Y)) :
    Xf * G = (lk * lc) • Y := by
  have h2 : e • (Xf * G) = e • ((lk * lc) • Y) := by
    rw [← Matrix.mul_smul, hG, Matrix.mul_smul, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, smul_smul]
    congr 1; ring
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  exact (mul_cancel_left_mem_nonZeroDivisors he).1 h3

theorem map_unit_eq {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (a b : R) (w : Rˣ) (hw : a * w = b) :
    T b * T (↑w⁻¹ : R) = T a := by
  rw [← hw, ← map_mul, mul_assoc, Units.mul_inv, mul_one]

theorem inv_pow_map {R S : Type} [CommRing R] [CommRing S] (T : R →+* S) (x : R) (li : S) (h : li * T x = 1)
    (m : ℕ) : li ^ m * T (x ^ m) = 1 := by
  rw [map_pow, ← mul_pow, h, one_pow]

end GlobalTheory.BSP.RelEx

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}
  {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {τ : Ainf l} {s : Seed bk d ρ τ} (ht : Height s)

theorem bas_map_disc {B : Obj l ↥(OL K)} (u : B.A) (h : Hom bk.prism B) (F : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀)
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) F) :
    ht.bas.map F = (s.X.map (BK.hf h)).map (toDisc l u bk.ρ₀) * ht.Z.map F := by
  rw [Height.bas, Matrix.map_mul]
  congr 1
  ext i j
  simp only [Matrix.map_apply]
  exact hF.ext _

theorem rel_exists_of {B : Obj l ↥(OL K)} (u : B.A) (f g : Hom bk.prism B)
    (Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀) (hF : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) Fg)
    (w : B.Aˣ) (hw : BK.hf f bk.E * w = BK.hf g bk.E) (G : Matrix (Fin d) (Fin d) B.A) (m : ℕ)
    (hAG : s.X.map (BK.hf f) * G = (l : B.A) ^ m • s.X.map (BK.hf g)) :
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  obtain ⟨Z', hZ'⟩ : ∃ Z', ht.Z * Z' = 1 := by
    obtain ⟨U, hU⟩ := ht.Z_unit
    exact ⟨↑U⁻¹, by rw [← hU]; exact U.mul_inv⟩
  obtain ⟨li, hli⟩ : ∃ li : Disc l u bk.ρ₀, li * toDisc l u bk.ρ₀ (l : B.A) = 1 :=
    ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l u bk.ρ₀) (l : B.A)).map (ofPre l u bk.ρ₀)).exists_left_inv
  have key : toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (ht.bas.map Ff *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
        (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg))) =
      toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • ht.bas.map Fg := by
    have e1 := ht.bas_map_disc u f Ff hF
    have e2 := ht.bas_map_disc u g Fg hG
    have h4 := alg s.N ((s.X.map (BK.hf f)).map (toDisc l u bk.ρ₀)) (ht.Z.map Ff) (Z'.map Ff)
      (G.map (toDisc l u bk.ρ₀)) ((s.X.map (BK.hf g)).map (toDisc l u bk.ρ₀)) (ht.Z.map Fg)
      (toDisc l u bk.ρ₀ (BK.hf g bk.E)) (toDisc l u bk.ρ₀ (BK.hf f bk.E))
      (toDisc l u bk.ρ₀ (↑w⁻¹ : B.A)) (li ^ m) (toDisc l u bk.ρ₀ ((l : B.A) ^ m))
      (by rw [← Matrix.map_mul, hZ', Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← Matrix.map_mul, hAG, map_smul_ring])
      (map_unit_eq _ _ _ w hw)
      (inv_pow_map _ _ li hli m)
    exact (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf g bk.E) ^ s.N • (M *
      ((toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) • (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg)))) e1).trans
      (h4.trans (congrArg (fun M => toDisc l u bk.ρ₀ (BK.hf f bk.E) ^ s.N • M) e2.symm))
  refine ⟨(toDisc l u bk.ρ₀ (↑w⁻¹ : B.A) ^ s.N * li ^ m) •
    (Z'.map Ff * G.map (toDisc l u bk.ρ₀) * ht.Z.map Fg), ?_⟩
  unfold Height.Rel
  intro Ff' Fg' hF' hG'
  have e1 : Ff' = Ff := (hF.unique hF').symm
  have e2 : Fg' = Fg := (hG.unique hG').symm
  subst e1 e2
  exact key

end GlobalTheory.BSP.Height

namespace GlobalTheory.BSP.Height

open GlobalTheory.BSP.RelEx

theorem rel_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B),
    ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  intro l _ K bk d ρ τ s ht B u f g
  by_cases hex : ∃ Ff Fg : bk.DS bk.ρ₀ →+* Disc l u bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf f) Ff ∧ IsDiscMap (BK.hf g) Fg
  swap
  · refine ⟨0, ?_⟩
    unfold Height.Rel
    intro Ff Fg hF hG
    exact (hex ⟨Ff, Fg, hF, hG⟩).elim
  obtain ⟨Ff, Fg, hF, hG⟩ := hex
  obtain ⟨hreg, ⟨w, hw⟩, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  obtain ⟨k, hk⟩ := s.nopole f g
  choose G hGc using hk
  have hXX : s.X.map (BK.hf f) * s.X'.map (BK.hf f) = ((l : B.A) ^ s.c₂ * BK.hf f bk.E ^ (2 * s.N)) • 1 := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _)]
    simp
  have hGm : BK.hf f bk.E ^ (2 * s.N) • Matrix.of G = (l : B.A) ^ k • (s.X'.map (BK.hf f) * s.X.map (BK.hf g)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact (hGc i j).symm
  have hAG : s.X.map (BK.hf f) * Matrix.of G = (l : B.A) ^ (k + s.c₂) • s.X.map (BK.hf g) := by
    rw [pow_add]
    exact cancel _ _ _ _ _ _ _ (pow_mem hreg _) (by rw [hXX, mul_comm]) hGm
  exact ht.rel_exists_of u f g Ff Fg hF hG w hw (Matrix.of G) (k + s.c₂) hAG

end GlobalTheory.BSP.Height
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonMatrix_exists_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B), ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  first | exact @GlobalTheory.BSP.Height.rel_exists | exact GlobalTheory.BSP.Height.rel_exists | (intros; apply GlobalTheory.BSP.Height.rel_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproduct
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_toDisc_eq_of_dvd {l : ℕ} {A : Type} [CommRing A] (u : A) (r : ℝ≥0) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε)
    (h : ∀ j : n × n, ((l : ℕ) : A) ^ k ∣ x j.1 j.2) : ∃ y : Matrix n n A, y.map (toDisc l u r) = ε := by
  choose y hy using h
  refine ⟨Matrix.of fun i j => y (i, j), ?_⟩
  ext i j
  have e := congrFun (congrFun hx i) j
  have e2 : x i j = _ := hy (i, j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, e2, map_mul, map_pow, map_natCast] at e
  exact ((isUnit_l_disc l _ _).pow k).mul_left_cancel e

theorem IsDiscMap.map_eq_smul {l : ℕ} {A A' : Type} [CommRing A] [CommRing A'] {u : A} {u' : A'} {r r' : ℝ≥0}
    {f : A →+* A'} {F : Disc l u r →+* Disc l u' r'} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε) :
    (x.map f).map (toDisc l u' r') = ((l : ℕ) : Disc l u' r') ^ k • ε.map F := by
  ext i j
  have e := congrArg F (congrFun (congrFun hx i) j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast] at e ⊢
  rw [← e, hF.ext]

theorem map_mul_map_eq_smul_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (A A' : Matrix (Fin d) (Fin d) R) (e : R) (b : ℕ) (h : A * A' = e ^ b • (1 : Matrix (Fin d) (Fin d) R)) :
    A.map f * A'.map f = f e ^ b • (1 : Matrix (Fin d) (Fin d) S) := by
  rw [← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]

theorem Height.dvd_at_section (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (B : Obj l ↥(OL K)) (f f' : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)) (hε : ht.Rel (BK.hf f X) f f' ε) (k : ℕ)
    (x : Matrix (Fin d) (Fin d) B.A)
    (hx : x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε)
    (g : ↥(GK K)) (σ : Hom B (ainfObj K)) (h1 : σ.comp f = bk.ι) (h2 : σ.comp f' = (ainfHom K g).comp bk.ι)
    (j : Fin d × Fin d) : ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j.1 j.2) := by
  obtain ⟨⟨F, hF⟩, hrel⟩ := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht B (ainfObj K) f f f' bk.ι σ ε hε
  have hr := hrel F hF
  rw [h1, h2] at hr
  exact GlobalTheory.T.pow_dvd_galoisComparison_matrix l K bk d ρ τ s ht hτ hρ g (ε.map F) hr k (x.map σ.f) (hF.map_eq_smul k x ε hx) j.1 j.2

theorem matrix_phi_eq_entries {R : Type} [CommRing R] (φ : R →+* R) (e e' : R) (he : Associated e e') (d a b : ℕ)
    (P Q Q' : Matrix (Fin d) (Fin d) R) (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R))
    (x : Matrix (Fin d) (Fin d) R) (hx : e' ^ a • (P * x.map φ) = e ^ a • (x * Q)) :
    ∃ (h : ℕ) (c : Fin d × Fin d → Fin d × Fin d → R),
      ∀ j : Fin d × Fin d, e ^ h * x j.1 j.2 = ∑ i : Fin d × Fin d, φ (x i.1 i.2) * c i j :=
  GlobalTheory.T.matrix_phi_equation_to_family_equation R R (RingHom.id R) φ e e' he d d a a b P Q Q' hQ x hx

theorem Height.exists_rel_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) :
    ∃ ε : Matrix (Fin d) (Fin d) En.Q.A,
      ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  have tb : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have h₁ := GlobalTheory.T.comparisonMatrix_exists_on_disc l K bk d ρ τ s ht En.Q (BK.hf En.inl X) En.inl En.inr
  obtain ⟨εD, hεD⟩ := h₁
  have h₂ := GlobalTheory.T.prism_comparisonMatrix_pow_smul_bounded_on_disc l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb εD hεD
  obtain ⟨k, x, hx⟩ := h₂
  have hφ := GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb k x εD hεD hx
  have h₃ := matrix_phi_eq_entries En.Q.D.φ (BK.hf En.inl bk.E) (BK.hf En.inr bk.E)
    (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk En.Q En.inl En.inr).2.1 d (ht.a + s.N) ht.b (ht.A.map (BK.hf En.inl))
    (ht.A.map (BK.hf En.inr)) (ht.A'.map (BK.hf En.inr))
    (map_mul_map_eq_smul_one (BK.hf En.inr) _ _ _ _ ht.A_mul) x hφ
  obtain ⟨h, c, hc⟩ := h₃
  have hdiv := GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd l K bk En (Fin d × Fin d) c h k (fun j => x j.1 j.2) hc
    (Height.dvd_at_section l K bk d ρ τ s ht hτ hρ En.Q En.inl En.inr εD hεD k x hx)
  have h₄ := map_toDisc_eq_of_dvd (BK.hf En.inl X) bk.ρ₀ k x εD hx hdiv
  obtain ⟨y, hy⟩ := h₄
  subst hy
  exact ⟨y, hεD⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproductStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparison_matrix_prismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → (∀ g, IsUnit (ρ g)) → ∀ (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)), ∃ ε : Matrix (Fin d) (Fin d) En.Q.A, ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  first | exact @GlobalTheory.BSP.Height.exists_rel_env | exact GlobalTheory.BSP.Height.exists_rel_env | (intros; apply GlobalTheory.BSP.Height.exists_rel_env <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentities
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mem_nonZeroDivisors_of_associated' {R : Type} [CommRing R] {a b : R} (h : Associated a b)
    (ha : a ∈ nonZeroDivisors R) : b ∈ nonZeroDivisors R := by
  obtain ⟨v, rfl⟩ := h
  exact mul_mem_nonZeroDivisors.mpr ⟨ha, v.isUnit.mem_nonZeroDivisors⟩

theorem mul_cancel_of_rel {R : Type} [CommRing R] {n : Type} [Fintype n] {N : ℕ} {ef eg eh : R}
    (hg : eg ∈ nonZeroDivisors R) (hh : eh ∈ nonZeroDivisors R) {Pf Pg Ph ε₁ ε₂ ε₃ : Matrix n n R}
    (r1 : eg ^ N • (Pf * ε₁) = ef ^ N • Pg) (r2 : eh ^ N • (Pg * ε₂) = eg ^ N • Ph)
    (r3 : eh ^ N • (Pf * ε₃) = ef ^ N • Ph) : Pf * (ε₁ * ε₂) = Pf * ε₃ := by
  have key : (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂)) = (eg ^ N * eh ^ N) • (Pf * ε₃) := by
    calc (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂))
        = eh ^ N • ((eg ^ N • (Pf * ε₁)) * ε₂) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = eh ^ N • ((ef ^ N • Pg) * ε₂) := by rw [r1]
      _ = ef ^ N • (eh ^ N • (Pg * ε₂)) := by
          rw [Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
      _ = ef ^ N • (eg ^ N • Ph) := by rw [r2]
      _ = eg ^ N • (ef ^ N • Ph) := by rw [smul_smul, smul_smul, mul_comm]
      _ = eg ^ N • (eh ^ N • (Pf * ε₃)) := by rw [r3]
      _ = (eg ^ N * eh ^ N) • (Pf * ε₃) := by rw [smul_smul]
  have hc : eg ^ N * eh ^ N ∈ nonZeroDivisors R :=
    mul_mem_nonZeroDivisors.mpr ⟨pow_mem hg _, pow_mem hh _⟩
  ext i j
  have e := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  exact (mul_cancel_left_mem_nonZeroDivisors hc).mp e

theorem rel_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  intro l _ K bk d ρ τ s ht B f₀ h0 f g h ε₁ ε₂ ε₃ h1 h2 h3
  have hn : ∀ k : Hom bk.prism B, ‖toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k X)‖ ≤ bk.ρ₀ := fun k =>
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ k).1
  have hE : ∀ k : Hom bk.prism B,
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := fun k =>
    mem_nonZeroDivisors_of_associated' ((GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ k).2.1.map (toDisc l (BK.hf f₀ X) bk.ρ₀)) h0
  have mf := isDiscMap_map (BK.hf f) (hn f)
  have mg := isDiscMap_map (BK.hf g) (hn g)
  have mh := isDiscMap_map (BK.hf h) (hn h)
  have hF : Disc.map (BK.hf f) (hn f) (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈
      nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    rw [mf.ext]; exact hE f
  exact GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht (Disc l (BK.hf f₀ X) bk.ρ₀) _ hF _ _
    (mul_cancel_of_rel (hE g) (hE h) (h1 _ _ mf mg) (h2 _ _ mg mh) (h3 _ _ mf mh))

end GlobalTheory.BSP.Height
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriod_comparison_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  first | exact @GlobalTheory.BSP.Height.rel_mul | exact GlobalTheory.BSP.Height.rel_mul | (intros; apply GlobalTheory.BSP.Height.rel_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentities
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem height_rel_unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f₀) bk.J ι →
    (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
    ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
      k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hε B f₀ ι tb
  have H := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f₀) ι tb
  have hinj := H.1
  have hE := H.2.1
  have key : ∀ k : Hom En.Q B, ht.Rel (BK.hf f₀ X) (k.comp En.inl) (k.comp En.inr)
      ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
    intro k
    have H2 := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q B En.inl En.inl En.inr f₀ k (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    refine H2.1.elim fun Fk hFk => ?_
    have h := H2.2
    have e : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk =
        (ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀) := Matrix.ext fun i j => hFk.ext (ε i j)
    exact e ▸ h Fk hFk
  have inj : ∀ M N : Matrix (Fin d) (Fin d) B.A, M.map (toDisc l (BK.hf f₀ X) bk.ρ₀) =
      N.map (toDisc l (BK.hf f₀ X) bk.ρ₀) → M = N := fun M N h =>
    Matrix.ext fun i j => hinj (congrFun (congrFun h i) j)
  have tr : ∀ (f f' g g' : Hom bk.prism B) (M : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)),
      f = f' → g = g' → ht.Rel (BK.hf f₀ X) f g M → ht.Rel (BK.hf f₀ X) f' g' M := fun _ _ _ _ _ hf hg h =>
    hf ▸ hg ▸ h
  refine ⟨fun k hk => ?_, fun k₁ k₂ k₃ h₁ h₂ h₃ => ?_⟩
  · have h : ht.Rel (BK.hf f₀ X) (k.comp En.inr) (k.comp En.inr)
        ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ hk rfl (key k)
    have e := GlobalTheory.T.discPeriod_comparison_matrix_mul l K bk d ρ τ s ht B f₀ hE _ _ _ 1 1 _ (ht.rel_one _ _) (ht.rel_one _ _) h
    exact inj _ _ ((e.symm.trans (mul_one 1)).trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  · have e1 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inl)
        ((ε.map k₁.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ rfl h₁ (key k₁)
    have e3 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inr)
        ((ε.map k₃.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ h₂.symm h₃.symm (key k₃)
    have e := GlobalTheory.T.discPeriod_comparison_matrix_mul l K bk d ρ τ s ht B f₀ hE _ _ _ _ _ _ e1 (key k₂) e3
    exact inj _ _ (Matrix.map_mul.trans e)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinCoproductUnitCocycleIdentitiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinCoproduct_unit_cocycle_identities : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A), ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f₀) bk.J ι → (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  first | exact @GlobalTheory.BSP.height_rel_unit_cocycle | exact GlobalTheory.BSP.height_rel_unit_cocycle | (intros; apply GlobalTheory.BSP.height_rel_unit_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrism
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.StratCocycle

variable {l : ℕ} {R : Type} [CommRing R]

theorem comp_assoc {P P' P'' P''' : Obj l R} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P') :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext' rfl

theorem comp_id {P P' : Obj l R} (f : Hom P P') : f.comp (Hom.id P) = f := Hom.ext' rfl

theorem map_comp {P P' P'' : Obj l R} {d : ℕ} (ε : Matrix (Fin d) (Fin d) P.A) (g : Hom P' P'') (f : Hom P P') :
    ε.map (g.comp f).f = (ε.map f.f).map g.f := by
  rw [Matrix.map_map]; rfl

theorem unit_of_codiag {P Q B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (h1 : ∀ Δ : Hom Q P, Δ.comp inl = Δ.comp inr → ε.map Δ.f = 1)
    (k : Hom Q B) (hk : k.comp inl = k.comp inr) : ε.map k.f = 1 := by
  obtain ⟨Δ, ⟨hΔl, hΔr⟩, -⟩ := univ P (Hom.id _) (Hom.id _)
  have hk' : k = (k.comp inl).comp Δ := by
    refine (univ B (k.comp inl) (k.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔl).trans (comp_id _))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp (k.comp inl)) hΔr).trans ((comp_id _).trans hk))
  calc ε.map k.f = ε.map ((k.comp inl).comp Δ).f := congrArg (fun k : Hom Q B => ε.map k.f) hk'
    _ = (ε.map Δ.f).map (k.comp inl).f := map_comp ε _ Δ
    _ = (1 : Matrix (Fin d) (Fin d) P.A).map (k.comp inl).f :=
        congrArg (fun M : Matrix (Fin d) (Fin d) P.A => M.map (k.comp inl).f) (h1 Δ (hΔl.trans hΔr.symm))
    _ = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem cocycle_of_triple {P Q Q₂ B : Obj l R} {d : ℕ} (inl inr : Hom P Q)
    (univ : ∀ (C : Obj l R) (f g : Hom P C), ∃! h : Hom Q C, h.comp inl = f ∧ h.comp inr = g)
    (i₁ : Hom Q Q₂) (j : Hom P Q₂)
    (univ₂ : ∀ (C : Obj l R) (f : Hom Q C) (g : Hom P C), ∃! h : Hom Q₂ C, h.comp i₁ = f ∧ h.comp j = g)
    (ε : Matrix (Fin d) (Fin d) Q.A)
    (hc : ∀ k₂₃ k₁₃ : Hom Q Q₂, i₁.comp inr = k₂₃.comp inl → i₁.comp inl = k₁₃.comp inl →
      k₂₃.comp inr = k₁₃.comp inr → ε.map i₁.f * ε.map k₂₃.f = ε.map k₁₃.f)
    (k₁ k₂ k₃ : Hom Q B) (h12 : k₁.comp inr = k₂.comp inl) (h13 : k₁.comp inl = k₃.comp inl)
    (h23 : k₂.comp inr = k₃.comp inr) : ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  obtain ⟨k₂₃, ⟨h₂₃l, h₂₃r⟩, -⟩ := univ Q₂ (i₁.comp inr) j
  obtain ⟨k₁₃, ⟨h₁₃l, h₁₃r⟩, -⟩ := univ Q₂ (i₁.comp inl) j
  have hc' := hc k₂₃ k₁₃ h₂₃l.symm h₁₃l.symm (h₂₃r.trans h₁₃r.symm)
  obtain ⟨m, ⟨hml, hmr⟩, -⟩ := univ₂ B k₁ (k₂.comp inr)
  have e₂ : k₂ = m.comp k₂₃ := by
    refine (univ B (k₂.comp inl) (k₂.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inr) hml).trans h12)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₂₃r).trans hmr)
  have e₃ : k₃ = m.comp k₁₃ := by
    refine (univ B (k₃.comp inl) (k₃.comp inr)).unique ⟨rfl, rfl⟩ ⟨?_, ?_⟩
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃l).trans
        ((comp_assoc _ _ _).symm.trans ((congrArg (fun q => Hom.comp q inl) hml).trans h13)))
    · exact (comp_assoc _ _ _).trans ((congrArg (Hom.comp m) h₁₃r).trans (hmr.trans h23))
  subst e₂ e₃ hml
  rw [map_comp ε m i₁, map_comp ε m k₂₃, map_comp ε m k₁₃, ← Matrix.map_mul, hc']

theorem unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
      ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
        k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hrel B
  have cocB := GlobalTheory.T.breuilKisinCoproduct_unit_cocycle_identities l K bk d ρ τ s ht En ε hrel
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  refine ⟨unit_of_codiag En.inl En.inr En.univ ε
    (fun Δ h => (cocB bk.prism (Hom.id _) Unit (TopBasis.self bk.J)).1 Δ h), fun k₁ k₂ k₃ h12 h13 h23 => ?_⟩
  exact (GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk En.Q _ _ (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)).elim fun En₂ =>
    (GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis l K bk En En₂).2.elim fun ι htb => htb.elim fun tb =>
      cocycle_of_triple En.inl En.inr En.univ En₂.inl En₂.inr En₂.univ ε
        (fun k₂₃ k₁₃ a b c => (cocB En₂.Q (En₂.inl.comp En.inl) ι tb).2 En₂.inl k₂₃ k₁₃ a b c)
        k₁ k₂ k₃ h12 h13 h23

end GlobalTheory.BSP.StratCocycle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinComparisonUnitCocycleEveryPrismStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_comparison_unit_cocycle_every_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A), ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) → ∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  first | exact @GlobalTheory.BSP.StratCocycle.unit_cocycle | exact GlobalTheory.BSP.StratCocycle.unit_cocycle | (intros; apply GlobalTheory.BSP.StratCocycle.unit_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRealizationMatrixStratifiedPhiModule
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRealizationMatrixStratifiedPhiModule
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RealMatrix

section Alg

variable {R R' : Type} [CommRing R] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem map_smul_hom (f : R →+* R') (c : R) (M : Matrix n n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_matrix_equation_inverse_scaling (F : R →+* R) (e t v : R) (hv : v * t = 1) (ht : F t = e * t) (a N : ℕ) (Y A : Matrix n n R)
    (h : e ^ a • Y.map F = Y * A) : e ^ (a + N) • (v ^ N • Y).map F = (v ^ N • Y) * A := by
  have h1 : F v * (e * t) = 1 := by rw [← ht, ← map_mul, hv, map_one]
  have h2 : e * F v = v := by linear_combination v * h1 - (e * F v) * hv
  have h3 : e ^ (a + N) * F v ^ N = v ^ N * e ^ a := by
    rw [pow_add, mul_assoc, ← mul_pow, h2, mul_comm]
  rw [map_smul_hom, map_pow, smul_smul, h3, ← smul_smul, h, Matrix.smul_mul]

theorem galois_matrix_equation_inverse_scaling (G : R →+* R) (t v : R) (hv : v * t = 1) (N : ℕ) (P Y ε : Matrix n n R)
    (h : t ^ N • (P * Y.map G) = G t ^ N • (Y * ε)) : P * (v ^ N • Y).map G = (v ^ N • Y) * ε := by
  have h1 : G v * G t = 1 := by rw [← map_mul, hv, map_one]
  have h2 := congrArg (fun M => (v ^ N * G v ^ N) • M) h
  have h3 : v ^ N * G v ^ N * t ^ N = G v ^ N := by
    rw [mul_right_comm, ← mul_pow, hv, one_pow, one_mul]
  have h4 : v ^ N * G v ^ N * G t ^ N = v ^ N := by
    rw [mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  simp only [smul_smul, h3, h4] at h2
  rw [map_smul_hom, map_pow, Matrix.mul_smul, h2, Matrix.smul_mul]

theorem descend (f : R →+* R') (hf : Function.Injective f) (x y : R) (N : ℕ) (M Y ε : Matrix n n R)
    (h : f x ^ N • M.map f = f y ^ N • (Y.map f * ε.map f)) : x ^ N • M = y ^ N • (Y * ε) := by
  apply Matrix.map_injective hf
  simp only []
  rw [map_smul_hom, map_smul_hom, map_pow, map_pow, Matrix.map_mul, h]

theorem push (f : R →+* R') (x y : R) (N : ℕ) (P Q Y ε : Matrix n n R) (h : x ^ N • (P * Q) = y ^ N • (Y * ε)) :
    f x ^ N • (P.map f * Q.map f) = f y ^ N • (Y.map f * ε.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_pow, ← map_pow, ← map_smul_hom, ← map_smul_hom, h]

end Alg

theorem exists_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ S : Strat bk d, S.a = ht.a + s.N → S.A = ht.A → (∀ g : ↥(GK K), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA)) → ∃ T : Matrix (Fin d) (Fin d) (WCb l), MReal S ρ T := by
  intro l _ K bk d ρ τ s ht hτ S ha hA hrel
  obtain ⟨u, hu⟩ := (GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ).1
  have hv : (↑u⁻¹ : WCb l) * inclW l τ = 1 := by rw [← hu, Units.inv_mul]
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine ⟨(↑u⁻¹ : WCb l) ^ s.N • ht.Y.map (inclW l), ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (((Units.isUnit _).pow _).map _).mul ht.unit
  · rw [ha, hA]
    refine frobenius_matrix_equation_inverse_scaling (frobW l : WCb l →+* WCb l) (bk.evW bk.E) (inclW l τ) _ hv ?_ _ _ _ _ ?_
    · change frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ
      rw [frobW_inclW, hτ.1, map_mul]
    · have h := congrArg (fun M => M.map (inclW l)) ht.φ
      try beta_reduce at h
      rw [map_smul_hom, map_pow, Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext1 i j
      exact frobW_inclW _
  · intro g
    have h0 := descend bk.iA hinj _ _ _ _ _ _ (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g _ (hrel g))
    have h := push (inclW l) _ _ _ _ _ _ _ h0
    rw [← galW_inclW] at h
    refine galois_matrix_equation_inverse_scaling (galW l (g : GQ l) : WCb l →+* WCb l) (inclW l τ) _ hv _ _ _ _ ?_
    refine Eq.trans ?_ h
    congr 2
    · ext1 i j
      exact ((inclWA l).commutes _).symm
    · ext1 i j
      exact galW_inclW _ _

end GlobalTheory.BSP.RealMatrix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRealizationMatrixStratifiedPhiModuleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realization_matrix_stratifiedPhiModule : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ S : Strat bk d, S.a = ht.a + s.N → S.A = ht.A → (∀ g : ↥(GK K), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA)) → ∃ T : Matrix (Fin d) (Fin d) (WCb l), MReal S ρ T := by
  first | exact @GlobalTheory.BSP.RealMatrix.exists_mreal | exact GlobalTheory.BSP.RealMatrix.exists_mreal | (intros; apply GlobalTheory.BSP.RealMatrix.exists_mreal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleOfCoproductCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleOfCoproductCocycle
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BSP

theorem strat_of_envCocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) → ∀ ε : Matrix (Fin d) (Fin d) En.Q.A, BK.hf En.inr bk.E ^ a • (A.map (BK.hf En.inl) * ε.map En.Q.D.φ) = BK.hf En.inl bk.E ^ a • (ε * A.map (BK.hf En.inr)) → (∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f) → ∃ S : Strat bk d, S.a = a ∧ S.A = A ∧ ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f := by
  intro l _ K bk En d a b A A' hA ε hφ hε
  have comp_assoc : ∀ {P P' P'' P''' : Obj l ↥(OL K)} (h : Hom P'' P''') (g : Hom P' P'') (f : Hom P P'),
      (h.comp g).comp f = h.comp (g.comp f) := fun _ _ _ => Hom.ext' rfl
  let c : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Hom En.Q B :=
    fun {B} f g => (En.univ B f g).choose
  have hc : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B), (c f g).comp En.inl = f ∧ (c f g).comp En.inr = g :=
    fun {B} f g => (En.univ B f g).choose_spec.1
  have hu : ∀ {B : Obj l ↥(OL K)} (k : Hom En.Q B), c (k.comp En.inl) (k.comp En.inr) = k :=
    fun {B} k => ((En.univ B _ _).choose_spec.2 k ⟨rfl, rfl⟩).symm
  clear_value c
  refine ⟨Strat.mk a b A A' hA (fun f g => ε.map (c f g).f) ?_ ?_ ?_ ?_, rfl, rfl, ?_⟩
  · intro B f
    exact (hε B).1 (c f f) ((hc f f).1.trans (hc f f).2.symm)
  · intro B f g h
    exact (hε B).2 (c f g) (c g h) (c f h) ((hc f g).2.trans (hc g h).1.symm)
      ((hc f g).1.trans (hc f h).1.symm) ((hc g h).2.trans (hc f h).2.symm)
  · intro B B' k f g
    have e : c (k.comp f) (k.comp g) = k.comp (c f g) :=
      (En.univ B' (k.comp f) (k.comp g)).unique (hc _ _)
        ⟨by rw [comp_assoc, (hc f g).1], by rw [comp_assoc, (hc f g).2]⟩
    refine Eq.trans ?_ (congrArg (fun k' : Hom En.Q B' => ε.map k'.f) e).symm
    ext i j
    rfl
  · intro B f g
    have e1 : ∀ x, (c f g).f (BK.hf En.inl x) = BK.hf f x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).1
    have e2 : ∀ x, (c f g).f (BK.hf En.inr x) = BK.hf g x := fun x =>
      congrArg (fun k : Hom bk.prism B => k.f x) (hc f g).2
    have e3 : ∀ x, (c f g).f (En.Q.D.φ x) = B.D.φ ((c f g).f x) := (c f g).f_φ
    ext i j
    have h := congrArg (fun M => (c f g).f (M i j)) hφ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, map_mul, map_pow, map_sum, Matrix.map_apply,
      e1, e2, e3] at h
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply] using h
  · intro B k
    exact congrArg (fun k' : Hom En.Q B => ε.map k'.f) (hu k)

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleOfCoproductCocycleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedPhiModule_of_coproduct_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) → ∀ ε : Matrix (Fin d) (Fin d) En.Q.A, BK.hf En.inr bk.E ^ a • (A.map (BK.hf En.inl) * ε.map En.Q.D.φ) = BK.hf En.inl bk.E ^ a • (ε * A.map (BK.hf En.inr)) → (∀ (B : Obj l ↥(OL K)), (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧ ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl → k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f) → ∃ S : Strat bk d, S.a = a ∧ S.A = A ∧ ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f := by
  first | exact @GlobalTheory.BSP.strat_of_envCocycle | exact GlobalTheory.BSP.strat_of_envCocycle | (intros; apply GlobalTheory.BSP.strat_of_envCocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLattice
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem rel_gal_of_env {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {τ : Ainf l} {d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {s : Seed bk d ρ τ} (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A)
    (hε : ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)))
    (S : Strat bk d)
    (hSε : ∀ (B : Obj l ↥(OL K)) (k : Hom En.Q B), S.ε (k.comp En.inl) (k.comp En.inr) = ε.map k.f)
    (g : ↥(GK K)) :
    ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
      ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA) := by
    obtain ⟨σ, ⟨h1, h2⟩, -⟩ := En.univ (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    have hn := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q (ainfObj K) En.inl En.inl En.inr bk.ι σ
      (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    obtain ⟨Fk, hFk⟩ := hn.1
    have hr := hn.2 Fk hFk
    have hr' : ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)
        ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), ht.Rel (BK.hf bk.ι X) f₁ f₂
          ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) → f₁ = bk.ι → f₂ = (ainfHom K g).comp bk.ι →
          ht.Rel (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk) := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ hr h1 h2
    have e : S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
      have key : ∀ f₁ f₂ : Hom bk.prism (ainfObj K), S.ε f₁ f₂ = ε.map σ.f → f₁ = bk.ι →
          f₂ = (ainfHom K g).comp bk.ι → S.ε bk.ι ((ainfHom K g).comp bk.ι) = ε.map σ.f := by
        rintro f₁ f₂ h rfl rfl; exact h
      exact key _ _ (hSε (ainfObj K) σ) h1 h2
    have hm : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk = (ε.map σ.f).map bk.iA :=
      Matrix.ext fun i j => hFk.ext (ε i j)
    have hM : (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA = (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk :=
      (congrArg (fun M => Matrix.map M bk.iA) e).trans hm.symm
    exact Eq.mpr (congrArg (ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι)) hM) hr'

theorem exists_strat_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : Seed bk d ρ τ),
    Height s → ∃ (S : Strat bk d) (T : Matrix (Fin d) (Fin d) (WCb l)), MReal S ρ T := by
  intro l _ K bk τ hτ d ρ hρ s ht

  obtain ⟨En⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk bk.prism (bk.toP bk.E) (bk.toP X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk bk.prism (Hom.id bk.prism))

  obtain ⟨En₂⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)
    (GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk En.Q En.inl)
  obtain ⟨⟨tb⟩, -⟩ := GlobalTheory.T.breuilKisinEnvelopes_adicTopologicalBasis l K bk En En₂

  obtain ⟨ε, hε⟩ := GlobalTheory.T.exists_comparison_matrix_prismCoproduct l K bk d ρ τ s ht hτ hρ En
  have hφ := GlobalTheory.T.frobenius_eq_of_pow_smul_comparisonMatrix l K bk d ρ τ s ht hτ En.Q En.inl En.inr (Digits l) tb 0 ε
    (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    ((congrArg (fun c => c • ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀))
      (pow_zero ((l : ℕ) : Disc l (BK.hf En.inl X) bk.ρ₀))).trans (one_smul _ _)).symm
  have hc := GlobalTheory.T.breuilKisin_comparison_unit_cocycle_every_prism l K bk d ρ τ s ht En ε hε
  obtain ⟨S, hSa, hSA, hSε⟩ := GlobalTheory.T.stratifiedPhiModule_of_coproduct_cocycle l K bk En d (ht.a + s.N) ht.b ht.A ht.A' ht.A_mul ε hφ hc
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_realization_matrix_stratifiedPhiModule l K bk d ρ τ s ht hτ S hSa hSA (rel_gal_of_env ht En ε hε S hSε)
  exact ⟨S, T, hT⟩

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratified_phiModule_crystalline_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : Seed bk d ρ τ), Height s → ∃ (S : Strat bk d) (T : Matrix (Fin d) (Fin d) (WCb l)), MReal S ρ T := by
  first | exact @GlobalTheory.BSP.exists_strat_mreal | exact GlobalTheory.BSP.exists_strat_mreal | (intros; apply GlobalTheory.BSP.exists_strat_mreal <;> assumption)
end
