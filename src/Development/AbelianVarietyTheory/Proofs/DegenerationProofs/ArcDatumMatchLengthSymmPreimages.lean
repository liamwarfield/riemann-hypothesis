module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimages
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

theorem psi_value_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.X) (hW : Match a f u P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
    (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
        algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (z : Sp F) (y : a.D₀.X) (χ : P.X) (hχ : e y = χ) (j : P.P.L.ι)
    (hj : (P.c χ).left (cpt R) ∈ P.P.L.U j) :
    ∃ v : Rˣ,
      (gm (Out.jFK (R := R) F) z
        (LB.wchart P.P.L (K := PUnit) (fun _ => Out.ptK (P.c χ)) (fun _ => j))
        ((P.psi χ).s (fun _ => j))).val =
      toStk z ((algebraMap (FractionRing R) F (algebraMap R _ u)) ^ (a.be y y / 2) *
        algebraMap (FractionRing R) F (algebraMap R _ v.val)) := by
  subst hχ
  obtain ⟨-, -, -, -, -, hG⟩ := hW
  have hG' := (genRel_iff w _ _ _ z).1 (hG F _ hF rfl y)
  obtain ⟨hp, hv⟩ := hG'
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  let x : Sp R ⟶ P.P.A.left := (P.c (e y)).left
  have hx : Out.jFK (R := R) F ≫ Out.ptK (P.c (e y)) = spMap g ≫ x := by
    have : spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      simp only [g, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [this, Category.assoc]
    rfl
  obtain ⟨j₀, hj₀⟩ := exists_chart a.D₀.P.isLB (φ (x (cpt R)))
  have ht : ⊤ ≤ x ⁻¹ᵁ ((a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 hj₀, hj⟩
  have hz : (Out.jFK (R := R) F ≫ Out.ptK (P.c (e y))) z ∈
      (a.D₀.P.L.pull φ).U (fun _ => j₀) ⊓ P.P.L.U j := by
    rw [hx]
    exact ht (show spMap g z ∈ (⊤ : (Sp R).Opens) from trivial)
  have hz₀ := mem_pull.1 hz.1
  have H1 := hv (fun _ => j) (fun _ => j₀) (fun _ => hz₀) (fun _ => hz.2)
  rw [gm_pullGen', gm_pullGen', Category.id_comp, Category.id_comp, Fintype.prod_unique, zpow_neg_one,
    Units.val_mul, Units.inv_mul_eq_iff_eq_mul] at H1
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap g x _ ht (w.s (fun _ => j₀, j)) z
  have hz₁ : (Out.jFK (R := O') F ≫ Out.ptK (a.D₀.c y)) z ∈ a.D₀.P.L.U j₀ := by
    rw [← hp PUnit.unit]; exact hz₀
  have ht₀ : ⊤ ≤ (𝟙 (Sp (FractionRing O'))) ⁻¹ᵁ
      (LB.wchart a.D₀.P.L (K := PUnit) (fun _ => Out.ptK (a.D₀.c y)) (fun _ => j₀)) :=
    (top_le_iff_mem _ _ (Out.jFK (R := O') F z)).2 (Set.mem_iInter.2 fun _ => hz₁)
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.ThetaShiftProofs.exists_unit_gm_spMap (algebraMap (FractionRing O') F) (𝟙 _) _ ht₀
    ((a.D₀.psi y).s (fun _ => j₀)) z
  obtain ⟨r, s, hs, hr⟩ := IsFractionRing.div_surjective (A := O') u₀.val
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := fun h0 => u₀.ne_zero (by rw [← hr, h0, map_zero, zero_div])
  obtain ⟨r', hr'⟩ := hf r hr0
  obtain ⟨s', hs'⟩ := hf s hs0
  have hq : algebraMap (FractionRing O') F u₀.val = g (r' * s'⁻¹).val := by
    rw [← hr, map_div₀, hF, hF, ← hr', ← hs', Units.val_mul, map_mul, map_units_inv, div_eq_mul_inv]
    rfl
  rw [hq, Category.comp_id] at hu₀
  rw [← hx] at hu₁
  refine ⟨u₁ * (r' * s'⁻¹), H1.trans ?_⟩
  refine (congrArg₂ (· * ·) hu₁ (congrArg _ hu₀)).trans ?_
  simp only [Units.val_mul, map_mul]
  rw [mul_left_comm]
  rfl

theorem pow_eq_of_not_isUnit {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {u : R} (hu : ¬ IsUnit u)
    (v v' : Rˣ) (m n : ℕ) (h0 : u ^ m * v ≠ 0) (h : u ^ m * v = u ^ n * v') : m = n := by
  by_cases hz : u = 0
  · subst hz
    have h0' := h ▸ h0
    have hm : m = 0 := by
      by_contra hm; exact h0 (by rw [zero_pow hm, zero_mul])
    have hn : n = 0 := by
      by_contra hn; exact h0' (by rw [zero_pow hn, zero_mul])
    omega
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨k, t, ht⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
    have hk : k ≠ 0 := by
      rintro rfl
      exact hu (by rw [ht, pow_zero, _root_.mul_one]; exact t.isUnit)
    have := IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ (t ^ m * v) (t ^ n * v') (k * m) (k * n) (by
      rw [ht] at h
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_mul]
      linear_combination h)
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) this

theorem be_self_eq_of_match (a : ArcIn D l β O' b) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (f : O' →+* R) (u : R) (hf : ∀ x, x ≠ 0 → IsUnit (f x)) (hu : ¬ IsUnit u) (P : DegPre R) [Module (𝓞 E) P.X]
    (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X)
    (h₁ : Match a f u P oP φ₁ he₁ w₁ e₁) (h₂ : Match a f u P oP φ₂ he₂ w₂ e₂) (y y' : a.D₀.X) (hy : e₁ y = e₂ y') :
    a.be y y = a.be y' y' := by
  let F := AlgebraicClosure (FractionRing R)
  let g : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R _)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective _ _)
  have hfi : Function.Injective f := (injective_iff_map_eq_zero f).2 fun x hx => by
    by_contra h0
    exact (hf x h0).ne_zero hx
  have hgf : Function.Injective (g.comp f) := hg.comp hfi
  let alg : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hgf).toAlgebra
  have hF : ∀ x, @algebraMap (FractionRing O') F _ _ alg (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x =>
    IsFractionRing.lift_algebraMap hgf x
  have z : Sp F := (default : PrimeSpectrum F)
  obtain ⟨j, hj⟩ := exists_chart P.P.isLB ((P.c (e₁ y)).left (cpt R))
  obtain ⟨v, hv⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₁ he₁ w₁ e₁ h₁
    F _ _ _ alg hF z y _ rfl j hj
  obtain ⟨v', hv'⟩ := @psi_value_of_match E _ _ _ H D l c O _ β O' _ _ b a R _ _ _ f u hf P _ oP φ₂ he₂ w₂ e₂ h₂
    F _ _ _ alg hF z y' _ hy.symm j hj
  have e := (toStk z).injective (hv.symm.trans hv')
  have e0 := fun h => Units.ne_zero _ (hv.trans ((congrArg (toStk z) h).trans (map_zero _)))
  have nn : ∀ y, 0 ≤ a.be y y := fun y => by
    by_cases hy : y = 0
    · subst hy; simp
    · exact (a.be_pos y hy).le
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y) (by norm_num : (0 : ℤ) ≤ 2))
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.ediv_nonneg (nn y') (by norm_num : (0 : ℤ) ≤ 2))
  rw [hm, hn, zpow_natCast, zpow_natCast] at e
  rw [hm, zpow_natCast] at e0
  have e' : u ^ m * v = u ^ n * v' := by
    apply hg
    rw [map_mul, map_mul, map_pow, map_pow]
    exact e
  have e0' : u ^ m * v ≠ 0 := fun h => e0 (by
    have := congrArg g h
    rw [map_mul, map_pow, map_zero] at this
    exact this)
  have hmn : m = n := pow_eq_of_not_isUnit hu v v' m n e0' e'
  have d : (2 : ℤ) ∣ a.be y y := (Dvd.intro _ rfl).trans (a.be_dvd y y)
  have d' : (2 : ℤ) ∣ a.be y' y' := (Dvd.intro _ rfl).trans (a.be_dvd y' y')
  omega

theorem be_symm_eq_of_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _ _ f u hf hu P _ oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ y =>
    be_self_eq_of_match a f u hf hu P oP φ₁ φ₂ he₁ he₂ w₁ w₂ e₁ e₂ h₁ h₂ _ _ (by simp)

end GlobalTheory.LN

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDatumMatchLengthSymmPreimagesStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcDatumMatch_length_symm_preimages : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (O' : Type) [CommRing O'] [IsDomain O'] (b : O →+* O') (a : ArcIn D l β O' b) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : O' →+* R) (u : R), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (P : DegPre R) [Module (𝓞 E) P.X] (oP : letI := H.starRing; P.OAct (𝓞 E)) (φ₁ φ₂ : P.P.A.left ⟶ a.D₀.P.A.left) (he₁ : eSec P.P.A ≫ φ₁ = spMap f ≫ eSec a.D₀.P.A) (he₂ : eSec P.P.A ≫ φ₂ = spMap f ≫ eSec a.D₀.P.A) (w₁ : LB.Iso P.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.P.L (a.D₀.P.L.pull φ₂)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.X), Match a f u P oP φ₁ he₁ w₁ e₁ → Match a f u P oP φ₂ he₂ w₂ e₂ → ∀ y, a.be (e₁.symm y) (e₁.symm y) = a.be (e₂.symm y) (e₂.symm y) := by
  first | exact @GlobalTheory.LN.be_symm_eq_of_match | exact GlobalTheory.LN.be_symm_eq_of_match | (intros; apply GlobalTheory.LN.be_symm_eq_of_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModK
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModK
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.AdaptedBasis

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FamDimension IsLocalRing

theorem exists_basis_of_iso {X Y Y₀ : Scheme.{0}} {n : ℕ} {L : LB X} (hL : L.IsLB) {K K' K₃ : Type} [Fintype K]
    [Fintype K'] [Fintype K₃] (h : Y₀ ⟶ Y) (π : Y ⟶ Y₀) (e₁ : h ≫ π = 𝟙 _) (e₂ : π ≫ h = 𝟙 _)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y₀ ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y₀ ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (hf : FormEq (Sum.elim (fun k => h ≫ φ k) φ₃) (Sum.elim ε ε₃) φ' ε')
    {A : Type} (g : A → Γ(Y₀, ⊤)) (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s, ∃! c : Fin n → A, IsComb b (fun i => π.appTop.hom (g (c i))) s) :
    ∃ b' : Fin n → LB.Sec (LB.LinComb L φ' ε'), ∀ s, ∃! c : Fin n → A, IsComb b' (fun i => g (c i)) s := by
  have h' : FormEq (Sum.elim (fun k => π ≫ φ' k) (fun k => π ≫ φ₃ k)) (Sum.elim ε' fun k => -ε₃ k) φ ε :=
    fun U _ w => by
      have := hf U (fun ψ => w (π ≫ ψ))
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, e₂, Category.id_comp]
        at this ⊢
      rw [← this]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  choose b' hb' using fun i => exists_sec hL hf (pullMulSec (b i) h u hu)
  refine ⟨b', fun s => ?_⟩
  have hu' := pullGen_isGen L _ _ _ (invGen_isGen L _ _ u hu) π
  obtain ⟨t, ht⟩ := exists_sec hL h' (pullMulSec s π (LB.pullGen L _ _ (LB.invGen L _ _ u) π) hu')
  refine (existsUnique_congr fun c => ⟨fun H => ?_, fun H => ?_⟩).1 (hb t)
  · refine (isComb_iff_sval hL _ _ _).2 fun y J hJ => ?_
    have E := SectionScalarValuation.sval_lin _ b H h y hJ
    rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_pull hJ, val_inv, e₁, Units.mul_inv_eq_iff_eq_mul,
      Finset.sum_mul] at E
    refine E.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, Category.id_comp, _root_.mul_assoc]
    congr 1
    exact (gs_pull h π y ⊤ trivial _).trans (by rw [e₁])
  · refine (isComb_iff_sval hL _ _ _).2 fun y J hJ => ?_
    have E := SectionScalarValuation.sval_lin _ b' H π y hJ
    rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_pull hJ, val_inv, Units.mul_inv_eq_iff_eq_mul,
      Finset.sum_mul, Category.id_comp]
    refine E.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, e₂, _root_.mul_assoc]
    congr 1

theorem exists_isBasisB (hT : SecTwistSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    {k : ℕ} (hk : 1 ≤ k) (α : D.X) : ∃ b : Fin (k ^ D.P.g) → D.SecB k α, IsBasisB D b := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk R (𝟙 _) (SectionScalarValuation.cQ D T α)
  let a : D.P.A ⟶ T := Over.homMk D.P.A.hom (Category.comp_id _)
  have ha : ∀ {Z : Over (Spec (CommRingCat.of R))} (x y : Z ⟶ T), x = y := fun x y =>
    Over.OverMorphism.ext (((Category.comp_id _).symm.trans (Over.w x)).trans
      ((Category.comp_id _).symm.trans (Over.w y)).symm)
  let h : D.P.A ⟶ T ⊗ D.P.A := lift a (𝟙 _)
  have e₁ : h ≫ snd T D.P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd T D.P.A ≫ h = 𝟙 _ := CartesianMonoidalCategory.hom_ext _ _ (ha _ _)
    (by rw [Category.assoc, e₁, Category.comp_id, Category.id_comp])
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    ![(SectionScalarValuation.cQ D T α).left, (1 : T ⟶ D.P.A).left] ![-1, 1]
  have e₃ : (snd T D.P.A).left ≫ D.P.A.hom = (fst T D.P.A).left :=
    congrArg (fun q => q.left) (ha (snd T D.P.A ≫ a) (fst T D.P.A))
  obtain ⟨b', hb'⟩ := exists_basis_of_iso D.P.isLB h.left (snd T D.P.A).left (congrArg (fun q => q.left) e₁)
    (congrArg (fun q => q.left) e₂) (φ' := D.famφB α) (ε' := DegPre.famε k)
    (LB.pullGen D.P.L _ _ e a.left) (pullGen_isGen _ _ _ _ he _) (fun U _ w => by
      have p := SectionScalarValuation.prod_famB D (𝟙 _) α k w
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₀ : h.left ≫ (snd T D.P.A).left = 𝟙 _ := congrArg (fun q => q.left) e₁
      have a₁ : a.left ≫ (SectionScalarValuation.cQ D T α).left = (SectionScalarValuation.cQ D D.P.A α).left := congrArg (fun x => x.left) (SectionScalarValuation.comp_cQ D a α)
      have a₂ : a.left ≫ (1 : T ⟶ D.P.A).left = (1 : D.P.A ⟶ D.P.A).left :=
        congrArg (fun x : D.P.A ⟶ D.P.A => x.left) (MonObj.comp_one (M := D.P.A) a)
      have a₃ : h.left ≫ (translPt D.P.A (SectionScalarValuation.cQ D T α)).left = (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A α).left := by
        have : h ≫ translPt D.P.A (SectionScalarValuation.cQ D T α) = 𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A α := by
          show h ≫ ((fst T D.P.A ≫ SectionScalarValuation.cQ D T α) * snd T D.P.A) = _
          rw [MonObj.comp_mul, e₁, ← Category.assoc, SectionScalarValuation.comp_cQ, mul_comm]
        exact congrArg (fun x => x.left) this
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, ← _root_.mul_assoc]
      refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun x => w x ^ ((k : ℤ) - 1)) a₀) ?_)
        ?_) ?_
      · exact (zpow_one _).trans (congrArg w a₃)
      · exact (zpow_neg_one _).trans (congrArg (fun x => (w x)⁻¹) a₁)
      · exact (zpow_one _).trans (congrArg w a₂)) (scal D.P.A.hom) b (fun s => by
      refine (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin (k ^ D.P.g) =>
        (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toEquiv) fun c => ?_).2 (hb s)
      have : ∀ x : R, (snd T D.P.A).left.appTop.hom (scal D.P.A.hom x) = (fst T D.P.A).left.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := fun x => by
        rw [← e₃]; rfl
      simp only [this]
      rfl)
  exact ⟨b', hb'⟩

theorem isBasisB_reindex {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {k : ℕ} {α : D.X} {I I' : Type}
    [Fintype I] [Fintype I'] (ε : I ≃ I') {b : I' → D.SecB k α} (hb : IsBasisB D b) {β : I → D.SecB k α}
    (h : ∀ i, β i = b (ε i)) : IsBasisB D β := fun s => by
  refine (Equiv.existsUnique_congr (Equiv.arrowCongr ε (Equiv.refl R)) fun a => forall_congr' fun j => ?_).2 (hb s)
  refine Eq.congr_right (Fintype.sum_equiv ε _ _ fun i => ?_)
  simp [h]

section Family

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {D : DegData V (maximalIdeal V)}


open GlobalTheory.FamInt in
theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 ≤ r) (hs : VGe D (FractionRing V) (ordVal hϖ) k α s r) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  choose b hb using fun i => (le_ordFn_iff hϖ (a i) 0).1 (le_trans (by exact_mod_cast hr) (hva i))
  refine ⟨secLin (fun i => scal D.toPre.P.A.hom (b i)) σ, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_⟩
  rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (b i)) σ (fun _ => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
  have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (b i)) =
      cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (b i) :=
    gs_pull _ _ y ⊤ trivial _
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
        spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e1, e2, e3, cst_comp, cst_comp, hb i, zpow_zero, _root_.one_mul]
  rfl

theorem integralFamily_of_min (hG : GlobalFnsSt) (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ}
    (hQ : QForm.IsQ D.toPre ϖ Q) {q : ℕ} (hq : 1 ≤ q) (χ : D.toPre.X) (β : D.toPre.SecB q χ)
    (hmin : ∀ z, Q χ ≤ Q (χ + q • z)) :
    ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), FamOf D.toPre _ f Φ ∧ f χ = β ∧
      ∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0 := by
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := FamFree.exists_fam_single (F := FractionRing V) hG D.tau_bimult hq χ σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hle := hmin z
      rw [q_shift hϖ hQ, le_add_iff_nonneg_right] at hle
      have hpos : (0 : ℤ) ≤ q * Q z + QForm.bOf D.toPre Q z χ := nonneg_of_mul_nonneg_right hle (by omega)
      obtain ⟨f, h1⟩ := exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z)⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3⟩

end Family

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J], Fintype.card J = k ^ S.g → ∃ (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ hJ
  obtain ⟨ϖ, Q, hϖ, hQ, hlt, hq⟩ := GlobalTheory.T.testQuadraticForm_eq_psi_valuation_mul o Ω S ρ p y₀ u l
  have hdim := (GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ u).2.1
  let C := u.D.toPre.X ⧸ FamFree.multiples u.D.toPre k
  have hc : Nat.card C = k ^ Module.finrank ℤ u.D.toPre.X := AddSubgroup.index_range_nsmul u.D.toPre.X k
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite C
  let e : J ≃ C × Fin (k ^ u.D.toPre.P.g) := Fintype.equivOfCardEq (by
    rw [hJ, Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card, hc, ← pow_add, add_comm, hdim])
  choose rep hrep hmin using fun c : C => l.pos.exists_within_forall_le
    (s := {α | (QuotientAddGroup.mk α : C) = c}) ⟨c.out, c.out_eq⟩
  have hsh : ∀ c, Short l.q k (rep c) := fun c m =>
    hmin c _ (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, rfl⟩).symm.trans (hrep c))
  have hpos : 0 < -Real.log ‖(u.j ϖ : PadicAlgCl p)‖ := by
    refine neg_pos.2 (Real.log_neg (norm_pos_iff.2 ?_) hlt)
    exact (map_ne_zero (algebraMap (FractionRing u.V) (PadicAlgCl p))).2 ((map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))).2 hϖ.ne_zero)
  have hQmin : ∀ c z, Q (rep c) ≤ Q (rep c + k • z) := fun c z => by
    have := hsh c z
    rw [hq, hq] at this
    exact_mod_cast le_of_mul_le_mul_right this hpos
  choose b hb using fun c => exists_isBasisB hL.2.1.secTwist u.D.toPre hk (rep c)
  choose Φ f hΦ hf hz using fun c m => integralFamily_of_min hL.1.globalFns hϖ hQ hk (rep c) (b c m) (hQmin c)
  choose σ hσ using fun c m => GlobalTheory.IntegralExpansion.main hL.1 u.V u.D u.A u.G u.U k hk (Φ c m) (f c m) (hΦ c m)
  have inj : ∀ c c', rep c = rep c' → c = c' := fun c c' h => (hrep c).symm.trans (by rw [h]; exact hrep c')
  refine ⟨fun i => σ (e i).1 (e i).2, fun i => rep (e i).1, fun i => f (e i).1 (e i).2, fun i => hsh _,
    fun i i' ⟨m, hm⟩ => ?_, fun α => ?_, fun i => hσ _ _, fun i => ⟨_, hΦ _ _⟩, fun i => hz _ _, fun i₀ => ?_⟩
  · exact congrArg rep ((hrep _).symm.trans (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, hm.symm⟩).symm.trans (hrep _)))
  · obtain ⟨m, hm⟩ := (FamFree.mk_eq_mk_iff _ _).1 (hrep (QuotientAddGroup.mk α))
    refine ⟨e.symm (QuotientAddGroup.mk α, ⟨0, by positivity⟩), m, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hm.symm
  · let ε : {i // rep (e i).1 = rep (e i₀).1} ≃ Fin (k ^ u.D.toPre.P.g) :=
      { toFun := fun i => (e i.1).2
        invFun := fun m => ⟨e.symm ((e i₀).1, m), by rw [Equiv.apply_symm_apply]⟩
        left_inv := fun i => Subtype.ext (
          e.symm_apply_eq.2 (Prod.ext (inj _ _ i.2).symm rfl))
        right_inv := fun m => by simp }
    refine isBasisB_reindex ε (hb (e i₀).1) fun i => ?_
    have key : ∀ c c' m, c = c' → f c m (rep c') = b c' m := by
      rintro c _ m rfl; exact hf c m
    exact key _ _ _ (inj _ _ i.2)

end GlobalTheory.AdaptedBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModKStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_basis_sections_mod_k : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J], Fintype.card J = k ^ S.g → ∃ (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f := by
  first | exact @GlobalTheory.AdaptedBasis.main | exact GlobalTheory.AdaptedBasis.main | (intros; apply GlobalTheory.AdaptedBasis.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsionNonzero

section Pull
variable {X Y : Scheme.{0}}

abbrev one (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)

theorem chart_le (L : LB X) {V : X.Opens} (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) (k : PUnit → L.ι) :
    (L.pull F).U k ≤ F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => k PUnit.unit)) := fun x hx =>
  ⟨h (x := x) trivial, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit⟩

theorem appLE_res (F : Y ⟶ X) {U V : X.Opens} {W : Y.Opens} (e : V ≤ U) (h : W ≤ F ⁻¹ᵁ V) (h' : W ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : (F.appLE V W h).hom (resG X e a) = (F.appLE U W h').hom a := by
  rw [← Scheme.Hom.map_appLE F h (homOfLE e).op]
  rfl

theorem res_appLE (F : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (e : W' ≤ W) (h : W ≤ F ⁻¹ᵁ U) (h' : W' ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : resG Y e ((F.appLE U W h).hom a) = (F.appLE U W' h').hom a := by
  rw [← Scheme.Hom.appLE_map F h (homOfLE e).op]
  rfl

theorem g_eq {K : Type} [Fintype K] [Unique K] (L : LB X) (F : Y ⟶ X) (i j : K → L.ι)
    (h : _ ≤ F ⁻¹ᵁ (L.U (i default) ⊓ L.U (j default))) :
    ((LB.LinComb L (K := K) (fun _ => F) (fun _ => 1)).g i j).val =
      (F.appLE _ _ h).hom (L.g (i default) (j default)).val := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

def pullSec (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V) (F : Y ⟶ X)
    (h : ⊤ ≤ F ⁻¹ᵁ V) : (L.pull F).Sec where
  f k := (F.appLE _ _ (chart_le L F h k)).hom (σ fun _ => k PUnit.unit)
  compat i j := by
    have hi := (inf_le_left : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h i)
    have hj := (inf_le_right : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h j)
    have hj' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => j PUnit.unit) :=
      hj.trans (F.preimage_mono inf_le_right)
    have hi' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => i PUnit.unit) :=
      hi.trans (F.preimage_mono inf_le_right)
    have hW : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi hj'
    have h₁ : (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit) ≤
        𝟙 X ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ 0) (LB.wchart_le L _ _ 0)
    have h₂ : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ PUnit.unit) (LB.wchart_le L _ _ PUnit.unit)
    have hU : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ ((one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi' hj'
    have e := congrArg (F.appLE _ _ hW).hom (hσ (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    rw [map_mul, appLE_res F _ hW hi, appLE_res F _ hW hj, appLE_res F _ hW hU] at e
    refine (res_appLE F _ _ hi _).trans (e.trans (congrArg₂ (· * ·) ?_ (res_appLE F _ _ hj _).symm))
    refine (congrArg (F.appLE _ _ hU).hom (g_eq L (𝟙 X) _ _ h₁)).trans (Eq.trans ?_ (g_eq L F i j h₂).symm)
    exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val)
      (Scheme.Hom.appLE_comp_appLE F (𝟙 X) _ _ _ h₁ hU)

theorem le_nonzeroLocus_iff (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V)
    (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) {K : Type} [Field K] (x : Sp K ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (pullSec L σ hσ F h) ↔ ∃ j, valF (x ≫ F) _ (σ j) ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((Points.le_preimage_iff x _).1 hx)
    have h₁ := (Points.le_preimage_iff x _).2 hk
    have h₂ := Points.le_preimage_mono x (Y.basicOpen_le _) h₁
    have h₃ := (Points.le_preimage_basicOpen_iff x h₂ _).1 h₁
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h k) h₂]
    exact h₃.ne_zero
  · rintro ⟨j, hj⟩
    obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
    have h₁ : ⊤ ≤ (x ≫ F) ⁻¹ᵁ (V ⊓ (one L).U fun _ => a) := by
      by_contra hc
      exact hj (dif_neg hc)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (L.pull F).U (fun _ => a) := fun z hz =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h₁ hz).2 0
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h fun _ => a) h₂] at hj
    exact Points.le_preimage_mono x (le_iSup (fun k => Y.basicOpen ((pullSec L σ hσ F h).f k)) fun _ => a)
      ((Points.le_preimage_basicOpen_iff x h₂ _).2 hj.isUnit)

end Pull

theorem exists_torsion_valF_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  intro laws laws₂ o Ω _ _ _ _ S ρ M U₀ Q hbig p _ y y₀ u jV yV yK hfac F ψ hmap hiso N σ hσ hne hy
  obtain ⟨hj, hyV, -, -⟩ := hfac
  have hloc := ZHPre.isLocalHom_of_test u jV hj
  have hK : IsAlgClosed (IsLocalRing.ResidueField (OO p)) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsq := hmap.1.1
  set r : Sp (IsLocalRing.ResidueField (OO p)) ⟶ Sp u.V :=
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV with hr
  have key : ∀ x, r x = IsLocalRing.closedPoint u.V := fun x => by
    have hx : x = IsLocalRing.closedPoint _ :=
      Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField (OO p))) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap jV)
      (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans (IsLocalRing.comap_closedPoint jV)
  have hrange : Set.range r = {IsLocalRing.closedPoint u.V} := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint _, (key _).trans h.symm⟩⟩
  have hyN : ⊤ ≤ yV ⁻¹ᵁ N := by
    refine (Points.le_preimage_iff yV N).2 ?_
    rw [← hyV] at hy
    rw [← IsLocalRing.comap_closedPoint jV]
    exact hy
  have hF : ⊤ ≤ F ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N) := by
    rw [← Scheme.Hom.comp_preimage, hsq.w]
    exact fun z _ => hyN (x := u.G.hom z) trivial
  let θ := pullSec Q.L.L σ hσ F hF
  have hθ : ∃ x ∈ nonzeroLocus θ, u.G.hom x = IsLocalRing.closedPoint u.V := by
    obtain ⟨g, j, hg, hv⟩ := hne _ (r ≫ yV) (by
      rintro _ ⟨z, rfl⟩
      exact hyN (x := r z) trivial)
    have h₁ := (le_nonzeroLocus_iff Q.L.L σ hσ F hF (hsq.lift g r hg)).2 ⟨j, by rwa [hsq.lift_fst]⟩
    refine ⟨hsq.lift g r hg (IsLocalRing.closedPoint _), h₁ (x := IsLocalRing.closedPoint _) trivial, ?_⟩
    exact (congrArg (fun φ : Sp _ ⟶ Sp u.V => φ (IsLocalRing.closedPoint _)) (hsq.lift_snd g r hg)).trans (key _)
  have hg : u.A.g = S.g := (H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))).trans ρ.g_eq
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h₂ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (two_pos.trans_le ρ.two_le).ne' _)
    exact Nat.pow_le_pow_left h₂ 2
  have hn : ((S.r * S.N : ℕ) : IsLocalRing.ResidueField (OO p)) ≠ 0 := by
    have := S.unit.map (Spec.preimage (r ≫ yV ≫ M.s)).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hlt : 6 * (S.N ^ u.A.g * u.A.g.factorial) < (S.r * S.N) ^ 2 := by
    rw [hg]
    exact hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _)
  have hc := GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ u.V u.complete u.D u.A u.G u.U (Q.L.L.pull F) θ
    (pull_isLB Q.L.isLB F) hiso hθ _ r S.N (S.r * S.N) hrange hN hn hlt 1
  by_contra hcon
  have heq : Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1 ∧ ¬ ⊤ ≤ (1 * h).left ⁻¹ᵁ nonzeroLocus θ} =
      Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => and_iff_left_of_imp fun hh hle => hcon ⟨h, hh, ?_⟩)
    rw [_root_.one_mul] at hle
    exact (le_nonzeroLocus_iff Q.L.L σ hσ F hF h.left).1 hle
  omega

end GlobalTheory.ZH.TorsionNonzero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPoint_specialFibre_section_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  first | exact @GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | exact GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero | (intros; apply GlobalTheory.ZH.TorsionNonzero.exists_torsion_valF_ne_zero <;> assumption)
end
end
