module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Formalism.LocalToGlobal.Columns.DiagUnitMemAndNormalizesKOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam
open scoped CategoryTheory.Obj Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

section Branches

variable {X X' : Scheme.{0}}

def pre (π : X' ⟶ X) (Z : Closeds X) : Closeds X' := Z.preimage π.continuous

abbrev van (Z : Closeds X) (x : X) : Ideal (X.presheaf.stalk x) :=
  FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x

def tr {x y : X} (h : x = y) : X.presheaf.stalk x →+* X.presheaf.stalk y :=
  (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom

def IsRsp {A : Type} [CommRing A] [IsLocalRing A] {ι : Type} [Fintype ι] (f : ι → A) : Prop :=
  IsRegularLocalRing A ∧ Ideal.span (Set.range f) = maximalIdeal A ∧ (Fintype.card ι : WithBot ℕ∞) = ringKrullDim A

def BrAt (B : Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x) : Prop :=
  IsRsp f ∧ van B x = Ideal.span {∏ j, f (Sum.inl j)}

def ColAt (B : Closeds X) {ι : Type} (E : ι → Closeds X) (x : X) {m d : ℕ} (f : Fin m ⊕ Fin d → X.presheaf.stalk x)
    (c : Fin m → ι) : Prop :=
  BrAt B x f ∧ ∀ i, van (E i) x = Ideal.span {∏ j ∈ Finset.univ.filter (fun j => c j = i), f (Sum.inl j)}

def IsStrict (B : Closeds X) {ι : Type} (E : ι → Closeds X) : Prop :=
  ∀ x : X, ∃ (m d : ℕ) (f : Fin m ⊕ Fin d → X.presheaf.stalk x) (c : Fin m → ι), ColAt B E x f c ∧ Function.Injective c

end Branches

section Pairs

variable {K F : Type} [Field K] [Field F] {XK X X'K X' : Scheme.{0}}

end Pairs

section Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsCN (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R ∧ CharZero R

abbrev toBase {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : Over.mk (spMap φ) ⟶ Over.mk (𝟙 (Sp R)) :=
  Over.homMk (spMap φ) (Category.comp_id _)

end Sections

section Steps

def HomExtNormalSt : Prop :=
  ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), Geo.Tor.IsNormalScheme X → IsOpenImmersion j → IsDominant j →
    ∀ (G G' : Over X) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
    ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f

def PullSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → IsCN R' → Function.Injective φ → IsLocalHom φ → P.TorsionIso →
    ∃ (t' : SAB H (Sp R')) (_ : SABMap t' t (spMap φ)) (P' : PELUnif (maximalIdeal R') t')
      (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X), P'.TorsionIso ∧
      ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)

end Steps

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.Bl

abbrev DatP : Type 1 := ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
  (Wt : Set B.places.Pl), R3.Dat (w.st Z) w.I hX T Wt → Prop

def AtDat (P : DatP) : Prop :=
  StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt),
    GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → P K B f T w Z hX Wt z

end GlobalTheory.Mem.Top.Bl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q m : ℕ}

abbrev Low (m : ℕ) : Type := {s : Fin m × Fin m // s.2 < s.1}

def uni (y : Low m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => if h : b < a then y ⟨(a, b), h⟩ else if a = b then 1 else 0

def dens (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : ℝ :=
  ∏ i : Fin m, ‖lminor ((uni y)ᴴ * A * uni y) i.castSucc‖ ^ (-2 : ℤ)

def IsBlockSL2Embedding (e : Fin r ≃ Fin p ⊕ Fin q) : Prop :=
  (∀ a, (e.symm (Sum.inl a) : ℕ) = q + a) ∧ ∀ a, (e.symm (Sum.inr a) : ℕ) = a

def toMat (v : Fin p × Fin q → ℂ) : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun a b => v (a, b)

def glue (e : Fin r ≃ Fin p ⊕ Fin q) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : Low r → ℂ :=
  fun s => fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) (e s.1.1) (e s.1.2)

def base (e : Fin r ≃ Fin p ⊕ Fin q) (y : Low r → ℂ) : Fin p × Fin q → ℂ := vecOf (moeb (reindex e e (uni y)) 0)

def shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  (fromBlocks 1 Z 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * A * fromBlocks 1 Z 0 1

def schur (H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₂₁

def sgnMat (r q : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ)

theorem isBlockOrderedSumEquiv_trueIndex {r j : ℕ} (h : j ≤ r) : IsBlockSL2Embedding (idx h) := ⟨idx_symm_inl h, idx_symm_inr h⟩

theorem IsBlockSL2Embedding.card {e : Fin r ≃ Fin p ⊕ Fin q} (_ : IsBlockSL2Embedding e) : r = p + q := by
  simpa using Fintype.card_congr e

theorem exists_isBlockOrderedSumEquiv (p q : ℕ) : ∃ e : Fin (p + q) ≃ Fin p ⊕ Fin q, IsBlockSL2Embedding e :=
  ⟨((finCongr (add_comm p q)).trans finSumFinEquiv.symm).trans (Equiv.sumComm _ _), by
    constructor <;> intro a <;> simp [add_comm]⟩

@[simp] theorem toMat_vecOf (Z : Matrix (Fin p) (Fin q) ℂ) : toMat (vecOf Z) = Z := rfl

@[simp] theorem vecOf_toMat (v : Fin p × Fin q → ℂ) : vecOf (toMat v) = v := rfl

theorem det_uni (y : Low m → ℂ) : (uni y).det = 1 := by
  rw [det_of_lowerTriangular]
  · simp [uni]
  · intro a b h
    have h' : a < b := h
    simp [uni, not_lt_of_gt h', h'.ne]

theorem uni_eq_of_entries {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (y : Low r → ℂ) (y1 : Low q → ℂ) (y2 : Low p → ℂ)
    (Y : Matrix (Fin p) (Fin q) ℂ) (h : ∀ s : Low r, y s = fromBlocks (uni y2) Y 0 (uni y1) (e s.1.1) (e s.1.2)) :
    reindex e e (uni y) = fromBlocks (uni y2) Y 0 (uni y1) := by
  ext a b
  rw [reindex_apply, submatrix_apply]
  by_cases hab : e.symm b < e.symm a
  · simp only [uni, of_apply, dif_pos hab]
    rw [h]; simp [uni]
  · simp only [uni, of_apply, dif_neg hab, EmbeddingLike.apply_eq_iff_eq]
    rw [Fin.lt_def] at hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]
    · have := b.2; omega
    · simp
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]

theorem reindex_uni_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e (uni (glue e w)) = fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) :=
  uni_eq_of_entries he _ _ _ _ fun _ => rfl

theorem base_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : base e (glue e w) = w.1 := by
  rw [base, reindex_uni_glue he, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    mul_nonsing_inv_cancel_right _ _ (by rw [det_uni]; exact isUnit_one), vecOf_toMat]

theorem glue_surjective {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : Function.Surjective (glue e) := by
  intro y
  set M := reindex e e (uni y) with hM
  let y1 : Low q → ℂ := fun s => M (.inr s.1.1) (.inr s.1.2)
  refine ⟨(vecOf (M.toBlocks₁₂ * (uni y1)⁻¹), y1, fun s => M (.inl s.1.1) (.inl s.1.2)), funext fun s => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := s
  obtain ⟨a, rfl⟩ := e.symm.surjective a
  obtain ⟨b, rfl⟩ := e.symm.surjective b
  have hy : y ⟨(e.symm a, e.symm b), hab⟩ = M a b := by
    have hab' : e.symm b < e.symm a := hab
    simp only [hM, reindex_apply, submatrix_apply, uni, of_apply, dif_pos hab']
  rw [hy]
  simp only [glue, toMat_vecOf, Equiv.apply_symm_apply]
  rw [nonsing_inv_mul_cancel_right _ _ (by rw [det_uni]; exact isUnit_one)]
  replace hab : (e.symm b : ℕ) < e.symm a := hab
  rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
  · have : b < a := by rw [Fin.lt_def]; omega
    simp [uni, this]
  · rfl
  · have := a.2; omega
  · have : b < a := hab
    simp [uni, this, y1]

theorem continuous_uni : Continuous (uni : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ) := by
  refine continuous_matrix fun a b => ?_
  simp only [uni, of_apply]
  split_ifs <;> fun_prop

theorem continuous_toMat : Continuous (toMat : (Fin p × Fin q → ℂ) → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_matrix fun a b => continuous_apply (a, b)

theorem continuous_glue (e : Fin r ≃ Fin p ⊕ Fin q) : Continuous (glue e) := by
  refine continuous_pi fun s => ?_
  have h1 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.1 :=
    continuous_uni.comp (by fun_prop)
  have h2 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.2 :=
    continuous_uni.comp (by fun_prop)
  exact (h2.matrix_fromBlocks ((continuous_toMat.comp continuous_fst).matrix_mul h1) continuous_const h1).matrix_elem _ _

theorem measurable_dens (A : Matrix (Fin m) (Fin m) ℂ) : Measurable (dens A) := by
  refine Finset.measurable_prod _ fun i _ => Measurable.pow_const (Continuous.measurable (Continuous.norm ?_)) _
  exact (((continuous_uni.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_uni).matrix_submatrix _ _).matrix_det

theorem dens_nonneg (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : 0 ≤ dens A y :=
  Finset.prod_nonneg fun _ _ => zpow_nonneg (norm_nonneg _) _

theorem measurable_moeb_zero {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {g : α → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : Continuous g) (a : Fin p) (b : Fin q) :
    Measurable fun x => moeb (g x) 0 a b := by
  have h2 : Continuous fun x => (g x).toBlocks₂₂ := continuous_matrix fun _ _ => hg.matrix_elem _ _
  simp only [moeb_zero, Matrix.mul_apply, inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun c _ => (hg.matrix_elem (.inl a) (.inr c)).measurable.mul
    (h2.matrix_det.measurable.inv.mul (h2.matrix_adjugate.matrix_elem _ _).measurable)

theorem measurable_base (e : Fin r ≃ Fin p ⊕ Fin q) : Measurable (base e) :=
  Measurable.of_eval fun s => measurable_moeb_zero (continuous_uni.matrix_submatrix _ _) s.1 s.2

theorem det_shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).det = A.det := by
  simp [shear, det_conjTranspose, det_fromBlocks_zero₂₁]

theorem posDef_shear {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).PosDef :=
  hA.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2
    (by simp [det_fromBlocks_zero₂₁])))

theorem det_eq_mul_schur {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUnit H.toBlocks₂₂.det) :
    H.det = H.toBlocks₂₂.det * (schur H).det := by
  letI := invertibleOfIsUnitDet _ h
  conv_lhs => rw [← fromBlocks_toBlocks H, det_fromBlocks₂₂]
  rw [schur, invOf_eq_nonsing_inv]

theorem posDef_blocks {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : H.PosDef) :
    H.toBlocks₁₁.PosDef ∧ H.toBlocks₂₂.PosDef ∧ (schur H).PosDef := by
  have h1 : H.toBlocks₁₁.PosDef := h.submatrix Sum.inl_injective
  have h2 : H.toBlocks₂₂.PosDef := h.submatrix Sum.inr_injective
  refine ⟨h1, h2, ?_⟩
  letI := invertibleOfIsUnitDet _ h2.det_pos.ne'.isUnit
  have e : H.toBlocks₂₁ = H.toBlocks₁₂ᴴ := by
    ext a b
    exact (h.1.apply _ _).symm
  have h3 := h.posSemidef
  rw [← fromBlocks_toBlocks H, e, PosDef.fromBlocks₂₂ _ _ h2, ← e] at h3
  refine h3.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 ?_)
  have h4 := h.det_pos.ne'
  rw [det_eq_mul_schur h2.det_pos.ne'.isUnit] at h4
  exact (right_ne_zero_of_mul h4).isUnit

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) {j : ℕ} (hj : j ≤ r) {Tau : Type}
  (ι : Tau → X.Ψ)

def coords (z : V (nd X)) : Tau → Low r → ℂ := fun t s => z (Fintype.equivFin (Ent X) ⟨ι t, s⟩)

def proj (z : V (nd X)) : Tau × Fin j × Fin (r - j) → ℂ := flat (domPt X hj ι (cpt X (x0F X) z))

theorem mat_nmat (z : V (nd X)) (t : Tau) : mat (nmat X z) (ι t) = uni (coords X ι z t) := rfl

theorem measurable_domPt : Measurable fun x : Frame X.Ψ r => flat (domPt X hj ι x) :=
  Measurable.of_eval fun s => measurable_moeb_zero
    ((continuous_const.matrix_mul (KU.cont_mat X (ι s.1))).matrix_submatrix _ _) s.2.1 s.2.2

theorem measurable_proj : Measurable (proj X hj ι) := (measurable_domPt X hj ι).comp (KU.cont_cpt X _).measurable

theorem proj_eq (z : V (nd X)) (t : Tau) (s : Fin j × Fin (r - j)) :
    proj X hj ι z (t, s) = base (idx hj) (coords X ι z t) s := by
  have e : frameCo X hj (cpt X (x0F X) z) (ι t) = reindex (idx hj) (idx hj) (uni (coords X ι z t)) := by
    rw [frameCo, ← mat_nmat]
    congr 1
    exact nonsing_inv_mul_cancel_left _ _ (det_x0F X (ι t)).isUnit
  simp only [proj, flat, domPt, base, vecOf, e]

theorem dmin_cpt (z : V (nd X)) (t : Tau) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X (x0F X) z) (ι t) i =
      lminor ((uni (coords X ι z t))ᴴ * sgnMat r X.p0 * uni (coords X ι z t)) i := by
  have h0 := congrArg transpose (isOrth_x0F X (ι t))
  rw [gram_eq_mul, diagonal_transpose] at h0
  have h1 := gram_eq_mul (ι t).1 X.Gm (mat (cpt X (x0F X) z) (ι t))
  have e : mat (cpt X (x0F X) z) (ι t) = mat (x0F X) (ι t) * uni (coords X ι z t) := rfl
  rw [sgnMat, ← h0, dmin, lminor, ← det_transpose, transpose_submatrix, h1, e, lminor]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end Data

end GlobalTheory.FlagFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HodgeDomain.ActionDeriv

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  have h : ∀ᶠ x in nhds x0, ∀ τ, (1 - (unflat x τ)ᴴ * unflat x τ).PosDef := by
    refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually _ (fun a b => ?_)
      (fun x => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
    fun_prop
  exact h

theorem diffOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s) :
    ContDiffOn ℂ 1 (fun z => (M z).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem diffOn_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s)
    (hd : ∀ z ∈ s, (M z).det ≠ 0) (a b : Fin n) : ContDiffOn ℂ 1 (fun z => (M z)⁻¹ a b) s := by
  have hadj : ContDiffOn ℂ 1 (fun z => (M z).adjugate a b) s := by
    simp only [adjugate_apply]
    refine diffOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (diffOn_det h) hd) hadj

theorem diffOn_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) :
    DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) := by
  refine differentiableOn_pi.2 fun x => ?_
  obtain ⟨τ, a, b⟩ := x
  refine ContDiffOn.differentiableOn (n := 1) ?_ one_ne_zero
  have hinv : ∀ k, ContDiffOn ℂ 1 (fun v => (kapQ (g τ) (unflat v τ))⁻¹ k b) (DomFlat ι p q) := by
    intro k
    refine diffOn_inv (s := DomFlat ι p q) (M := fun v => kapQ (g τ) (unflat v τ)) (fun i j => ?_) (fun v hv => (kapQ_isUnit (hg τ (Set.mem_univ _)) (hv τ)).ne_zero) k b
    simp only [kapQ, Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
    fun_prop
  simp only [flat, moebI, moeb, Matrix.mul_apply]
  refine ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ (hinv k)
  simp only [Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
  fun_prop

theorem hasDerivAt_affine {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin k) ℂ)
    (z ξ : Matrix (Fin n) (Fin k) ℂ) (a : Fin m) (b : Fin k) :
    HasDerivAt (fun t : ℂ => (A * (z + t • ξ) + B) a b) ((A * ξ) a b) 0 := by
  have e : (fun t : ℂ => (A * (z + t • ξ) + B) a b) = fun t => t * (A * ξ) a b + (A * z + B) a b := by
    funext t
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((A * ξ) a b)).add_const ((A * z + B) a b)

theorem fderiv_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ : Pt ι p q) :
    fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) =
      flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) := by
  have hz' : flat z ∈ DomFlat ι p q := hz
  have hn := isOpen_domFlat.mem_nhds hz'
  have hF := ((diffOn_moebI hg).differentiableAt hn).hasFDerivAt
  set D := fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) with hD
  have hc : HasDerivAt (fun t : ℂ => flat z + t • flat ξ) (flat ξ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (flat ξ)).const_add (flat z)
  have hW : HasDerivAt (fun t : ℂ => flat (moebI g (unflat (flat z + t • flat ξ)))) D 0 :=
    hF.comp_hasDerivAt_of_eq (0 : ℂ) hc (by simp)
  have hev : ∀ᶠ t : ℂ in nhds 0, flat z + t • flat ξ ∈ DomFlat ι p q :=
    hc.continuousAt.eventually_mem (by simpa using hn)
  funext x
  obtain ⟨τ, a, b⟩ := x
  have hgτ := hg τ (Set.mem_univ _)
  have key : unflat D τ * kapQ (g τ) (z τ) = jW (g τ) (z τ) * ξ τ := by
    rw [jW, Matrix.sub_mul, eq_sub_iff_add_eq, Matrix.mul_assoc]
    ext i j
    have h1 := hasDerivAt_affine (g τ).1.toBlocks₁₁ (g τ).1.toBlocks₁₂ (z τ) (ξ τ) i j
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_pi.1 hW (τ, i, k)).mul (hasDerivAt_affine (g τ).1.toBlocks₂₁ (g τ).1.toBlocks₂₂ (z τ) (ξ τ) k j)
    have h3 := h2.congr_of_eventuallyEq (f₁ := fun t : ℂ =>
      ((g τ).1.toBlocks₁₁ * (z τ + t • ξ τ) + (g τ).1.toBlocks₁₂) i j) (by
        filter_upwards [hev] with t ht
        have := moeb_mul_kapQ hgτ (ht τ)
        exact (congrFun (congrFun this i) j).symm)
    rw [h1.unique h3, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [zero_smul, add_zero]
    rfl
  have e : unflat D τ = tanAct (g τ) (z τ) (ξ τ) := by
    rw [tanAct, ← key, mul_nonsing_inv_cancel_right _ _ (kapQ_isUnit hgτ (hz τ))]
  exact congrFun (congrFun e a) b

theorem isOpen_and_fderiv_moebI : ∀ (ι : Type) [Fintype ι] (p q : ℕ), IsOpen (DomFlat ι p q) ∧ ∀ g ∈ UpqI ι p q, DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) ∧ ∀ z ∈ DomI ι p q, ∀ ξ : Pt ι p q, fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) = flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) :=
  fun _ _ _ _ => ⟨isOpen_domFlat, fun _ hg => ⟨diffOn_moebI hg, fun _ hz ξ => fderiv_moebI hg hz ξ⟩⟩

end GlobalTheory.HodgeDomain.ActionDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open Formalism.HermitianLatticesTheory

theorem topChain : TopChain := by
  classical
  intro D X u C r Pr Ch sel S mu cst L σ v m2 hX hPr hc hm hpi h
  obtain ⟨hSS, hlev, pt, ix, yb, pT, hN, hyb, hE, hC, ⟨hTN, hTX⟩, hpin, hpin'⟩ := h
  have key : ∀ (c' : C.cls (m2 + 1 + 1)) d, OverRow sel mu v d (pT c') →
      HEq (r.N (m2 + 1 + 1) c') (tilQ sel mu v d).1.N ∧ ∀ c, HEq (r.Xi (m2 + 1) c c') fun x => σ (XiCpl2 Ch sel mu cst m2 (pt (m2 + 1) le_rfl c) (yb c) d x) := by
    intro c' d hd
    obtain ⟨p', hp, hrow⟩ := hd
    have gen : ∀ (j : ℕ) (hj : j = m2 + 1 + 1) (q : DecoF X.E (D.R.N j) (Pr.vT v) Pr.vGs (QE sel (mu : Chr X.F X.E X.K))), HEq (pT c') q →
        HEq (pT c').deco.1.N q.deco.1.N ∧ ∀ c, HEq (fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x))
          (fun x => σ (XiTopG Ch sel mu cst (m2 + 1) j (D.R.N j) (pt (m2 + 1) le_rfl c) (yb c) q x)) := by
      intro j hj q hq
      subst hj
      obtain rfl := eq_of_heq hq
      exact ⟨HEq.rfl, fun _ => HEq.rfl⟩
    obtain ⟨g1, g2⟩ := gen D.R.m (by omega) p' hp
    refine ⟨?_, fun c => ?_⟩
    · rw [hTN c']
      refine g1.trans (heq_of_eq ?_)
      rw [hrow.1]
      rfl
    · have e : r.Xi (m2 + 1) c c' = fun x => σ (XiTop Ch sel mu cst (m2 + 1) (pt (m2 + 1) le_rfl c) (yb c) (pT c') x) := funext (hTX c c')
      rw [e]
      refine (g2 c).trans (heq_of_eq ?_)
      rw [xiTopTilQ_holds Ch sel mu cst hX hPr hc hm v hpi _ _ d p' hrow.1 hrow.2 (hyb c)]
  refine ⟨hSS, hlev, pt, ix, yb, fun c' => if h : ∃ d, OverRow sel mu v d (pT c') then some h.choose else none,
    hN, hyb, hE, hC, fun c' d hd => ?_, fun c c' d hd => ?_, hpin, fun c' => ?_⟩
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).1
  · dsimp only at hd
    split_ifs at hd with h
    obtain rfl := Option.some_inj.1 hd
    exact (key c' _ h.choose_spec).2 c
  · rw [hpin' c']
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨_, dif_pos ⟨d, hd⟩⟩
    · rintro ⟨d, hd⟩
      dsimp only at hd
      split_ifs at hd with h
      exact h

section Gen
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xiOver_eq_topG {u : Pr.Word} (n : ℕ) {j : ℕ} (h : j = R.m) (p : ChPt (R := R) sel mu u (n + 1))
    (Y : Set (Sp X.E (R.N (n + 1)))) (p' : ChPt (R := R) sel mu u j) :
    xiOver Ch sel mu cst n h p Y p' = XiTopG Ch sel mu cst (n + 1) j (R.N j) p Y p' := by
  subst h
  rfl
end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def kerRd (u : B.Word) (a : I.ι) : KerRead ((I.rec7 l Z).chTw u a) B.fields where
  SS := Sall (Pr := B.primes X) I.sel (I.tup a) u
  lev := levC (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u
  N i c := ((I.stp u a i).rep c).1.1.deco.1.N
  Xi i c c' x := B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') x)
  pin i c := i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1

theorem kerRd_top {m2 : ℕ} (hm : B.R.m = m2 + 2) (u : B.Word) (a : I.ι) :
    (I.kerRd l Z u a).IsChainTop I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) B.embLL u m2 := by
  have hm' : (I.rec7 l Z).R.m = m2 + 2 := hm
  refine ⟨rfl, rfl, fun i _ c => ((I.stp u a i).rep c).1.1, fun i hi c => Idx.get c.1 (by omega),
    fun c => ((I.stp u a (m2 + 1)).rep c).1.2, fun c => ((I.stp u a (m2 + 1 + 1)).rep c).1.1, fun _ _ _ => rfl,
    fun c => PtAt.mem_ybSet _ (by omega), fun i hi c c' x => ?_, fun c c' x => ?_, ⟨fun _ => rfl, fun c c' x => ?_⟩, fun i hi c => show i + 1 ≤ B.R.m ∨ _ from Or.inl (by omega), fun c' => ?_⟩
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1 c'.1 _ _ x) = _
    rw [xiAt_entry I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u m2 c.1 c'.1 _ _ x) = _
    rw [xiAt_penultimate_eq_xiCpl1 I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega) (Idx.some_get _ (by omega)).symm]
    rfl
  · show B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u (m2 + 1) c.1 c'.1 _ _ x) = _
    rw [xiAt_last I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (by omega : m2 + 1 + 1 = B.R.m), xiOver_eq_topG]
    rfl
  · exact or_iff_right (by show ¬ m2 + 1 + 1 + 1 ≤ B.R.m; omega)

theorem mem_stdL_iff {R : Ranks} (H : Host R) (n : ℕ) (x : Fin n → H.E) : x ∈ Th.stdL H n ↔ ∀ k, IsIntegral ℤ (x k) := by
  refine ⟨fun h k => ?_, fun h k _ => Submodule.mem_one.2 ⟨⟨x k, h k⟩, rfl⟩⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (h k trivial)
  rw [← hr]
  exact NumberField.RingOfIntegers.isIntegral_coe r

theorem chiRec_lat (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) :
    TaylorLogMetric.chiRec (I.rec7 l Z) idl (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) =
      I.chi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) := by
  have h1 := (O u a).dt_lat i c
  have h2 := hidl.2.2.2.2 _ ((O u a).L0 i) ((O u a).lat i c)
  rw [← h1] at h2
  have e0 : ((O u a).L0 i).1 = Th.stdL B.host (B.R.N i) := by
    ext x
    rw [(O u a).lattice_integral_coordinates]
    exact (mem_stdL_iff B.host _ x).symm
  have e1 : ((O u a).lat i c).1 = ((I.stp u a i).rep c).1.1.deco.1.N := hO.lat u a i c
  rw [e0, e1] at h2
  have h3 : Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N = idl (QuotientGroup.mk ((O u a).dt i c)) := h2.symm
  rw [h3, TaylorLogMetric.chiRec_idl _ _ hidl.1, ← h3]
  have h4 : ((TaylorLogMetric.chiQ (I.rec7 l Z) (QuotientGroup.mk ((O u a).dt i c)) : ℂˣ) : ℂ) = ((tildeQ B.host I.SQ I.C.chiPsi (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ) := by
    rw [hO.dt u a i c]
    rfl
  rw [h4]
  exact GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1

theorem kerRd_Th (hok : I.Ok) {idl : (I.rec7 l Z).Dt ⧸ (I.rec7 l Z).UO → TaylorLogMetric.IdE (I.rec7 l Z)} (hidl : TaylorLogMetric.RelDetPinned (I.rec7 l Z) idl)
    {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)} (hO : I.StdO l Z Qp O) (u : B.Word) (a : I.ι) (i : ℕ)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (TaylorLogMetric.chiRec (I.rec7 l Z) idl) I.J.cD) i c c' =
      I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := by
  refine (congrArg (fun A => (I.kerRd l Z u a).Th (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) A i c c')
    (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).symm).trans ?_
  have he : (I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N =
      I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N := by
    funext z
    show Th.chiFac B.host _ _ _ _ _ * _ = Th.chiFac B.host _ _ _ _ _ * _
    unfold Th.chiFac
    rw [I.chiRec_lat l Z hok hidl hO u a i c, I.chiRec_lat l Z hok hidl hO u a (i + 1) c']
  show thC _ _ _ _ _ _ _ _ _ _ ((I.J.amb B (TaylorLogMetric.chiRec (I.rec7 l Z) idl)).e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) = thC _ _ _ _ _ _ _ _ _ _ (I.A.e _ _ ((I.stp u a i).rep c).1.1.deco.1.N ((I.stp u a (i + 1)).rep c').1.1.deco.1.N)
  rw [he]
  rfl

theorem kerEntTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.Adapted ∧ t.TopPinned := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex O E hQ hO hU hE hS
  obtain ⟨idl, hidl⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  obtain ⟨⟨kf, hkf⟩, hAd⟩ := hE
  have hm := hok.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hok.sel_ok u ⟨hok.T_mem u, hok.g_mem⟩).2.1
  let t : KerEntTied ex :=
    { cc := ⊤
      cc_rec := B.toPre.ccK_top.symm
      cc_ok := ⟨top_ne_bot, by simp⟩
      δ := I.J.δ
      δ_ok := hok.amb_ok.delta
      B := I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      χ := TaylorLogMetric.chiRec (I.rec7 l Z) idl
      χ_ok := TaylorLogMetric.isChi_chiRec _ _ hidl
      idl := idl
      idl_ok := hidl
      χ_rec := rfl
      cD := I.J.cD
      X := B.fields
      seam := seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      seam_ok := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
      Pr := B.primes X
      pr_ok := l.pr
      g_rec := fun i => rfl
      Ch := I.Ch
      sel := I.sel
      S := I.S
      word := fun u => u
      T_rec := fun u => rfl
      tup := I.tup
      Q_rec := hQ
      cst := I.cst
      idx := I.idx
      m2 := B.R.m - 2
      glob := I.glob
      glob_σ := rfl
      glob_xi := rfl
      idx_ok := hok.idx_ok
      O := O
      rd := I.kerRd l Z
      rd_chain := fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hok.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a)
      O_dgen := hO.dgen
      O_S := hO.S
      O_lat := fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
      O_Th := fun u a i c c' => (hO.Th u a i c c').trans (I.kerRd_Th l Z hok hidl hO u a i c c').symm
      unf := fun u a i hi => (hU u a i hi).unfIs _
      ent := E
      ent_lam := fun u w h => (hS u w h).1
      kf := kf
      kf_un := hkf
      served := hS }
  exact ⟨t, ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl,
    heq_of_eq (AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J _).symm, rfl, hO⟩, rfl, hAd, fun u a => I.kerRd_top l Z hm u a⟩

end GlobalTheory.Mem.Col2.TC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_compatible_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.Adapted ∧ t.TopPinned := by
  first | exact @GlobalTheory.Mem.Col2.TC.kerEntTied_true | exact GlobalTheory.Mem.Col2.TC.kerEntTied_true | (intros; apply GlobalTheory.Mem.Col2.TC.kerEntTied_true <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.PointWell

open Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem moeb_one {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : moeb 1 z = z := by
  rw [← fromBlocks_one, moeb, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem block_of_moeb_eq {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hx' : x' ∈ X.dom) (τ : X.Ψ) (h : moeb (frameCo X hj x τ) 0 = moeb (frameCo X hj x' τ) 0) (a b : Fin r)
    (ha : X.p0 ≤ a) (hb : (b : ℕ) < X.p0) : ((mat x τ)⁻¹ * mat x' τ) a b = 0 := by
  have hu := frameCo_isUnit₂₂ X hj hp hx τ
  have hu' := frameCo_isUnit₂₂ X hj hp hx' τ
  have hd : IsUnit (mat x τ).det := (hx τ).1.isUnit
  have hd0 : IsUnit (mat (x0F X) τ).det := (det_x0F X τ).isUnit
  have hN : (frameCo X hj x τ)⁻¹ * frameCo X hj x' τ = reindex (idx hj) (idx hj) ((mat x τ)⁻¹ * mat x' τ) := by
    simp only [frameCo, inv_reindex]
    simp only [reindex_apply, submatrix_mul_equiv]
    rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hd0, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hd0]
  have hf : IsUnit (frameCo X hj x τ).det := by
    rw [frameCo, det_reindex_self, det_mul]
    exact (isUnit_nonsing_inv_det _ hd0).mul hd
  rw [moeb_zero, moeb_zero] at h
  generalize frameCo X hj x τ = f at *
  generalize frameCo X hj x' τ = f' at *
  have h1 : f'.toCols₂ = f * fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) := by
    have h0 := fromBlocks_mul_fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂)
      f.toBlocks₁₁ f.toBlocks₁₂ f.toBlocks₂₁ f.toBlocks₂₂
    rw [fromBlocks_toBlocks] at h0
    refine Eq.trans ?_ h0.symm
    simp only [Matrix.mul_zero, zero_add]
    rw [mul_nonsing_inv_cancel_left _ _ hu, ← Matrix.mul_assoc, h, nonsing_inv_mul_cancel_right _ _ hu']
    ext (a | a) b <;> rfl
  have h2 : (f⁻¹ * f').toCols₂ = fromRows (0 : Matrix (Fin j) (Fin (r - j)) ℂ) (f.toBlocks₂₂⁻¹ * f'.toBlocks₂₂) :=
    (congrArg (f⁻¹ * ·) h1).trans (nonsing_inv_mul_cancel_left f _ hf)
  have hb' : (b : ℕ) < r - j := hp ▸ hb
  have ha' : (a : ℕ) - (r - j) < j := by have := a.2; omega
  have h3 := congrFun (congrFun h2 (Sum.inl ⟨_, ha'⟩)) ⟨_, hb'⟩
  rw [hN] at h3
  have ea : (idx hj).symm (Sum.inl ⟨_, ha'⟩) = a := Fin.ext (by rw [idx_symm_inl]; simp only; omega)
  have eb : (idx hj).symm (Sum.inr ⟨_, hb'⟩) = b := Fin.ext (by rw [idx_symm_inr])
  simpa [toCols₂, ea, eb] using h3

theorem perFr_mem {A : Type} (S : Submodule ℂ (A → ℂ)) (w : A → Fin r → E) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (τ : E →+* ℂ) (m : ℕ) (hm : τ ∈ X.Ψ → m = r - X.p0) (hm' : τ ∉ X.Ψ → m = X.p0)
    (hS : ∀ i < m, (fun a => perFr X x (w a) τ i) ∈ S) (i : ℕ) (hi : i < m) :
    (fun a => perFr X x' (w a) τ i) ∈ S := by
  have hp := X.p0_le
  by_cases h : τ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨τ, h⟩).det := (hx _).1.isUnit
    have hi' : X.p0 + i < r := by omega
    have key : (∑ b : Fin r, ((mat x' ⟨τ, h⟩)⁻¹ * mat x ⟨τ, h⟩) ⟨_, hi'⟩ b •
        fun a => ((mat x ⟨τ, h⟩)⁻¹.mulVec (Data.emb τ (w a))) b) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · rw [h2 _ _ _ (Nat.le_add_right _ _) hb, zero_smul]; exact zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hbr := b.2
        convert hS (b - X.p0) (by omega) using 2 with a
        unfold perFr
        rw [dite_eq_left h, dite_eq_left (by omega)]
        congr 1
        exact Fin.ext (by simp; omega)
    convert key using 2 with a
    unfold perFr
    rw [dite_eq_left h, dite_eq_left hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨τ, h⟩) (mat x' ⟨τ, h⟩)⁻¹ hd, ← mulVec_mulVec]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  · have hm := hm' h
    have h' : conjEmb τ ∈ X.Ψ := by_contra fun h' => h ((X.cmType τ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hi' : X.p0 - 1 - i < r := by omega
    have key : (∑ b : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) b ⟨_, hi'⟩ •
        fun a => hermC (conjEmb τ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) b) (Data.emb (conjEmb τ) (w a))) ∈ S := by
      refine Submodule.sum_mem _ fun b _ => ?_
      by_cases hb : (b : ℕ) < X.p0
      · refine Submodule.smul_mem _ _ ?_
        convert hS (X.p0 - 1 - b) (by omega) using 2 with a
        unfold perFr
        rw [dite_eq_right h, dite_eq_left h', dite_eq_left (by omega)]
        congr 2
        exact Fin.ext (by simp; omega)
      · rw [h1 _ _ _ (not_lt.1 hb) (by simp only; omega), zero_smul]; exact zero_mem _
    convert key using 2 with a
    unfold perFr
    rw [dite_eq_right h, dite_eq_left h', dite_eq_left hi']
    conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
    generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (f := fun b c => ∑ d, n b _ * _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ r}

theorem pt_eq_of_block (hU : IsUnf U) (hσ : GoodEmb c σ) (k : U.Comp) (x x' : (U.X k).dom)
    (h1 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) :
    (U.un k x).x = (U.un k x').x := by
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', -⟩ := hF k x'
  have hmem : ∀ j, (fun a => P' a j) ∈ Submodule.span ℂ (Set.range fun (j : Fin g) a => P a j) := by
    intro j
    simp only [hP']
    refine perFr_mem (U.X k) _ (fun a => (φ k a : Fin r → E)) x.2 h1 h2 _ (Dw.mult (e j).1) (fun h => ?_)
      (fun h => ?_) (fun i hi => ?_) _ (e j).2.2
    · exact (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega)
    · exact (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm
    · refine Submodule.subset_span ⟨e.symm ⟨(e j).1, ⟨i, hi⟩⟩, funext fun a => ?_⟩
      dsimp only
      rw [hP, Equiv.apply_symm_apply]
  choose μ hμ using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem j)
  have hL : ∀ a, P' a = mulVecLin (of μ) (P a) := fun a => funext fun j => by
    have := congrFun (hμ j) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have hsurj : Function.Surjective (mulVecLin (of μ)) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (mulVecLin (of μ))).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  rw [hx, hx']
  exact (F.fibre _ P P' hper hper').2 ⟨LinearEquiv.refl _ _,
    LinearEquiv.ofBijective _ ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun _ _ => rfl,
    fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hL⟩

end GlobalTheory.TrueCx.PointWell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem T_notMem_qv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  classical
  intro B X I hI _ u a P
  have hP : P.1 ∈ uSG (B.primes X).vGs I.SQ := Finset.mem_union.2 (Or.inr (I.mem_SQ.2 ⟨a, P.2⟩))
  exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P.1 hP

end GlobalTheory.Mem.Col2.ChEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotUnderTwistPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberLevelPrime_not_under_twistPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (B.primes X).Ok → ∀ (u : B.Word) (a : I.ι) (P : I.Q a), (B.T u : 𝓞 B.host.F) ∉ (qv B.host.F P.1).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | exact GlobalTheory.Mem.Col2.ChEx.T_notMem_qv | (intros; apply GlobalTheory.Mem.Col2.ChEx.T_notMem_qv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteSeriesThreeOfHyp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem discreteSeries_three_of_hypotheses (hC : GlobalTheory.Published.DiscreteSeriesCoverExists) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) ∧ (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) ∧ (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) := by
  intro hE hU
  refine ⟨fun n ε lam hl => ?_, fun n ε lam hl H H' _ _ _ _ σ σ' hσ hσ' => hU n ε lam hl H H' σ σ' hσ hσ', hC⟩
  obtain ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩ := hE n ε lam hl
  exact ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩

end GlobalTheory
end
