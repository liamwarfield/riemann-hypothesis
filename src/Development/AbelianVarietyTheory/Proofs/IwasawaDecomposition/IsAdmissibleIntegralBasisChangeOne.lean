module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

variable {X : Fields} {Pr : Primes X} {R : Ranks}


variable (Pr) in
def admitted (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  (P ∈ Pr.vGs → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)) ∧ (P ∉ Pr.vGs → Between j P h)

theorem isAdmissibleIntegralBasisChange_one (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : admitted Pr j P (1 : AutY X R j) :=
  ⟨fun _ => one_mem _, fun hP => between_of_nf hP (IndefiniteRowSideFullHecke.SandwichNormalForm.nf_one j hP)⟩

def nfMat {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  fun l s => if hs : s.1 < n then (if l = s then 1 else 0)
    else q ^ e ⟨s.1 - n, by omega⟩ * ((if l = s then 1 else 0) + if s.1 = n then Loc.inX E n c z l else 0)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

abbrev CAt (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Subgroup (AutY X R j) :=
  Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h

def ChiMul (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  (∀ r ∈ CAt sel mu cst j P h, chiInv Ch sel mu cst j P h r ≠ 0) ∧
    ∀ r ∈ CAt sel mu cst j P h, ∀ r' ∈ CAt sel mu cst j P h,
      chiInv Ch sel mu cst j P h (r * r') = chiInv Ch sel mu cst j P h r * chiInv Ch sel mu cst j P h r'

def ChiTriv (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  ∀ r ∈ CAt sel mu cst j P h, r ∈ Loc.fixX X.E (R.N j) (cOf R j) → chiInv Ch sel mu cst j P h r = 1

def GrpG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal), hbar ∈ lev.H ↔ ∃ g ∈ prCat (Pr := Pr) cst.sharp j P.1 h,
    ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.mulVec (redV P.1 x)

def ChrG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ (hbar : ↥lev.H) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.1.mulVec (redV P.1 x)) →
    ((lev.lam hbar : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

def GrpQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  lev.H = (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1)

def ChrQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  ∀ (g : ↥lev.H) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) →
    ((lev.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

theorem exists_char {G H K : Type} [Group G] [Group H] [Field K] (C : Subgroup G) (χ : G → K) (Rel : G → H → Prop)
    (hne : ∀ r ∈ C, χ r ≠ 0) (hmul : ∀ r ∈ C, ∀ r' ∈ C, χ (r * r') = χ r * χ r')
    (hs : ∀ h, ∃ r ∈ C, Rel r h) (hm : ∀ r h r' h', Rel r h → Rel r' h' → Rel (r * r') (h * h'))
    (hw : ∀ h, ∀ r ∈ C, ∀ r' ∈ C, Rel r h → Rel r' h → χ r = χ r') :
    ∃ lam : H →* Kˣ, ∀ h, ∀ r ∈ C, Rel r h → ((lam h : Kˣ) : K) = χ r := by
  choose s hsC hsR using hs
  refine ⟨MonoidHom.mk' (fun h => Units.mk0 (χ (s h)) (hne _ (hsC h))) fun a b => Units.ext ?_, fun h r hr hR => ?_⟩
  · simp only [Units.val_mk0, Units.val_mul]
    rw [← hmul _ (hsC a) _ (hsC b)]
    exact hw _ _ (hsC _) _ (mul_mem (hsC a) (hsC b)) (hsR _) (hm _ _ _ _ (hsR a) (hsR b))
  · exact hw _ _ (hsC _) _ hr (hsR _) hR

end GlobalTheory.Mem.Col2.IdxEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Proportional
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {X W T : Scheme.{0}} {L : LB X} {m : ℕ}

def Generates (J : X.IdealSheafData) (σ : Fin (m + 1) → L.Sec) : Prop :=
  (⨆ k, L.U k = ⊤) ∧ ∀ (k : L.ι) (V : X.affineOpens) (h : V.1 ≤ L.U k),
    J.ideal V = Ideal.span (Set.range fun j => resG X h ((σ j).f k))

def Proportional (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) : Prop :=
  ∀ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : Fin (m + 1)) (hi : A ≤ ψ ⁻¹ᵁ chart R m i) (j : Fin (m + 1)),
    (g.appLE (L.U k) A hk).hom ((σ j).f k) = pullRatio ψ A i hi j * (g.appLE (L.U k) A hk).hom ((σ i).f k)

theorem Proportional.comp {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (h : Proportional σ g ψ)
    (d : T ⟶ W) : Proportional σ (d ≫ g) (d ≫ ψ) := by
  intro A k hk i hi j
  have hA : A ≤ d ⁻¹ᵁ (g ⁻¹ᵁ L.U k ⊓ ψ ⁻¹ᵁ chart R m i) := fun x hx => ⟨hk hx, hi hx⟩
  have := congrArg (d.appLE _ A hA).hom (h _ k inf_le_left i inf_le_right j)
  rwa [map_mul, appLE_appLE, appLE_appLE, appLE_pullRatio] at this

theorem Proportional.of_comp {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (d : T ⟶ W)
    [IsSchemeTheoreticallyDominant d] [QuasiCompact d] (h : Proportional σ (d ≫ g) (d ≫ ψ)) :
    Proportional σ g ψ := by
  intro A k hk i hi j
  apply d.app_injective A
  rw [Scheme.Hom.app_eq_appLE, map_mul, appLE_appLE, appLE_appLE, appLE_pullRatio]
  exact h _ k _ i _ j

end GlobalTheory.ProjBlowup
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

def GeneratesAlong (I : W.IdealSheafData) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) : Prop :=
  (⨆ k, g ⁻¹ᵁ L.U k = ⊤) ∧ ∀ (k : L.ι) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ L.U k),
    I.ideal A = Ideal.span (Set.range fun j => (g.appLE (L.U k) A.1 h).hom ((σ j).f k))

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgebraicOfEllipticTorsionCoordinatesFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgebraicOfEllipticTorsionCoordinatesFinite
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem isAlgebraic_snd_of_equation {k L : Type} [Field k] [Field L] [Algebra k L] (A : WeierstrassCurve k)
    (x : k) {y : L} (h : (A.baseChange L).toAffine.Equation (algebraMap k L x) y) : IsAlgebraic k y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  refine IsIntegral.isAlgebraic ⟨Polynomial.X ^ 2 + (Polynomial.C (A.a₁ * x + A.a₃) * Polynomial.X
    - Polynomial.C (x ^ 3 + A.a₂ * x ^ 2 + A.a₄ * x + A.a₆)), ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, map_add, map_mul, map_pow]
    linear_combination h

theorem isAlgebraic_snd_adjoin {k : Type} [Field k] [Algebra k ℂ] (A : WeierstrassCurve k)
    {x y : ℂ} (h : (A.baseChange ℂ).toAffine.Equation x y) : IsAlgebraic k⟮x⟯ y := by
  refine isAlgebraic_snd_of_equation (A.baseChange k⟮x⟯) (IntermediateField.AdjoinSimple.gen k x) ?_
  have e : (A.baseChange k⟮x⟯).baseChange ℂ = A.baseChange ℂ := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
  rw [e]
  exact h

theorem isAlgebraic_of_torsionCoords_finite :
    ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) (n : ℕ),
      (torsionCoords (A.baseChange ℂ) n).Finite → ∀ z ∈ torsionCoords (A.baseChange ℂ) n, IsAlgebraic ℚ z := by
  rintro F _ A n hfin z ⟨x, y, h, h0, hz⟩
  have hy : IsAlgebraic (↥F)⟮x⟯ y := isAlgebraic_snd_adjoin A h.1
  have hx : IsAlgebraic F x :=
    GlobalTheory.CurveAlgebraic.isAlgebraic_of_torsion A.toAffine (A.baseChange ℂ).toAffine rfl n _ hfin
      (fun x y h h0 => ⟨x, y, h, h0, Or.inl rfl⟩) h h0 hy
  have : FiniteDimensional F (↥F)⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  have hy' : IsAlgebraic F y := hy.restrictScalars F
  rcases hz with rfl | rfl
  · exact hx.restrictScalars ℚ
  · exact hy'.restrictScalars ℚ

end GlobalTheory.Mem.FieldsEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgebraicOfEllipticTorsionCoordinatesFiniteStatement
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_of_ellipticTorsionCoordinates_finite : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (A : WeierstrassCurve F) (n : ℕ), (torsionCoords (A.baseChange ℂ) n).Finite → ∀ z ∈ torsionCoords (A.baseChange ℂ) n, IsAlgebraic ℚ z := by
  first | exact @GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | exact GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite | (intros; apply GlobalTheory.Mem.FieldsEx.isAlgebraic_of_torsionCoords_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousGrpHom
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.CompactDualSwap

variable {P Q P' Q' : ℕ}

def AntiIso (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') : Prop :=
  (Formalism.UG.Jpq P Q).submatrix e.symm e.symm = -Formalism.UG.Jpq P' Q'

theorem AntiIso.symm {e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q'} (h : AntiIso e) : AntiIso e.symm := by
  unfold AntiIso at *
  ext i j
  have := congrFun (congrFun h (e i)) (e j)
  simp only [submatrix_apply, Equiv.symm_apply_apply, Matrix.neg_apply, Equiv.symm_symm] at *
  rw [this, neg_neg]

def grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q →* UpqT P' Q' :=
  let f : Formalism.UG.Upq P Q →* GL (Fin P' ⊕ Fin Q') ℂ :=
    (Units.map (Matrix.reindexAlgEquiv ℂ ℂ e).toMonoidHom).comp (Formalism.UG.Upq P Q).subtype
  let f' : Formalism.UG.Upq P Q →* Formalism.UG.Upq P' Q' := f.codRestrict _ (by
    rintro ⟨g, hg⟩
    change Formalism.UG.cT _ g.val * _ * g.val = _ at hg
    change Formalism.UG.cT _ (g.val.submatrix e.symm e.symm) * _ *
      (g.val.submatrix e.symm e.symm) = _
    have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
      rw [h, neg_neg]
    have h3 : Formalism.UG.cT (starRingEnd ℂ) (g.val.submatrix e.symm e.symm) =
      (Formalism.UG.cT (starRingEnd ℂ) g.val).submatrix e.symm e.symm := rfl
    rw [h2, h3, Matrix.mul_neg, Matrix.neg_mul, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hg])
  f'

theorem mat_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (g : UpqT P Q) :
    (grpHom e h g).mat = g.mat.submatrix e.symm e.symm := rfl

theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → _) :=
  (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.injective

theorem continuous_grpHom (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) :
    Continuous (grpHom e h) := by
  rw [(GlobalTheory.UpqTopology.upq_lcsc P' Q').2.2.2.2.2.isInducing.continuous_iff]
  exact ((GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.2.continuous).matrix_submatrix e.symm e.symm

def grpEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : UpqT P Q ≃ₜ* UpqT P' Q' where
  toFun := grpHom e h
  invFun := grpHom e.symm h.symm
  left_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  right_inv g := mat_injective (by ext i j; simp [mat_grpHom])
  map_mul' := map_mul _
  continuous_toFun := continuous_grpHom e h
  continuous_invFun := continuous_grpHom e.symm h.symm

theorem lie_mem (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    X.val.submatrix e.symm e.symm ∈ lieU P' Q' := by
  have hX : X.valᴴ * Formalism.UG.Jpq P Q + Formalism.UG.Jpq P Q * X.val = 0 := X.2
  change (X.val.submatrix e.symm e.symm)ᴴ * Formalism.UG.Jpq P' Q' +
    Formalism.UG.Jpq P' Q' * X.val.submatrix e.symm e.symm = 0
  have h2 : Formalism.UG.Jpq P' Q' = -(Formalism.UG.Jpq P Q).submatrix e.symm e.symm := by
    rw [h, neg_neg]
  rw [h2, Matrix.conjTranspose_submatrix, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← neg_add, neg_eq_zero]
  have := congrArg (fun M => Matrix.submatrix M e.symm e.symm) hX
  exact this

def lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) : lieU P Q ≃L[ℝ] lieU P' Q' where
  toFun X := ⟨_, lie_mem e h X⟩
  invFun X := ⟨_, lie_mem e.symm h.symm X⟩
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp
  map_add' X Y := rfl
  map_smul' c X := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix e.symm e.symm).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix e e).subtype_mk _

theorem coe_lieEquiv (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) :
    ((lieEquiv e h X : lieU P' Q') : Matrix _ _ ℂ) = X.val.submatrix e.symm e.symm := rfl

theorem mem_ball (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e) (X : lieU P Q) (r : ℝ) :
    lieEquiv e h X ∈ ballU P' Q' r ↔ X ∈ ballU P Q r := by
  simp only [ballU, Set.mem_ofPred_eq, coe_lieEquiv, submatrix_apply]
  have : ∑ i, ∑ j, ‖X.val (e.symm i) (e.symm j)‖ = ∑ i, ∑ j, ‖X.val i j‖ := by
    rw [← e.symm.sum_comp (fun i => ∑ j, ‖X.val i j‖)]
    exact Finset.sum_congr rfl fun i _ => e.symm.sum_comp (fun j => ‖X.val (e.symm i) j‖)
  rw [this]

open scoped Matrix.Norms.Operator in
theorem exp_submatrix {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (X.submatrix e.symm e.symm) = (NormedSpace.exp X).submatrix e.symm e.symm :=
  (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (continuous_id.matrix_submatrix e.symm e.symm) X).symm

theorem isOmegaLeb_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (lam : Measure (lieU P Q)) (hl : IsOmegaLeb lam) : IsOmegaLeb (lam.map (lieEquiv e h)) := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P' ⊕ Fin Q') → (Fin P' ⊕ Fin Q') → ℂ))
  have : SecondCountableTopology (lieU P Q) := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology (lieU P' Q') := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (lieU P Q) := LocallyCompactSpace.of_finiteDimensional_of_complete ℝ _
  obtain ⟨h1, h2⟩ := hl
  refine ⟨(lieEquiv e h).isAddHaarMeasure_map lam, ?_⟩
  have hm : Measurable (lieEquiv e h) := (lieEquiv e h).continuous.measurable
  have hc : ∀ A B : ℕ, Continuous (fun ab : lieU A B × lieU A B =>
      Formalism.BasicNotions.entries ((ab.1 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin A ⊕ Fin B) (Fin A ⊕ Fin B) ℂ))) := by
    intro A B
    refine continuous_pi fun ij => ?_
    exact ((continuous_subtype_val.comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).const_smul Complex.I)).matrix_elem ij.1 ij.2
  have hv := volume_measurePreserving_piCongrLeft
    (fun _ : (Fin P' ⊕ Fin Q') × (Fin P' ⊕ Fin Q') => ℂ) (e.prodCongr e)
  rw [Measure.map_prod_map _ _ hm hm, Measure.map_map (hc P' Q').measurable (hm.prodMap hm),
    ← hv.map_eq, ← h2, Measure.map_map hv.measurable (hc P Q).measurable]
  congr 1
  funext ab ij
  obtain ⟨ij, rfl⟩ := (e.prodCongr e).surjective ij
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  simp [Formalism.BasicNotions.entries, coe_lieEquiv]

theorem omegaDensity_map (e : Fin P ⊕ Fin Q ≃ Fin P' ⊕ Fin Q') (h : AntiIso e)
    (μ : Measure (UpqT P Q)) (c : ENNReal) (hμ : OmegaDensity μ c) :
    OmegaDensity (μ.map (grpEquiv e h)) c := by
  have : BorelSpace (lieU P Q) := ⟨rfl⟩
  have : BorelSpace (lieU P' Q') := ⟨rfl⟩
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : BorelSpace (UpqT P' Q') := ⟨rfl⟩
  obtain ⟨lam, hl, ht⟩ := hμ
  refine ⟨_, isOmegaLeb_map e h lam hl, ?_⟩
  refine ht.congr fun r => ?_
  have e1 := (grpEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := μ)
  have e2 := (lieEquiv e h).toHomeomorph.toMeasurableEquiv.map_apply (μ := lam)
  congr 1
  · refine Eq.trans ?_ (e1 _).symm
    congr 1
    ext g
    change (∃ X ∈ ballU P Q r, _) ↔ ∃ X ∈ ballU P' Q' r, g.mat.submatrix e.symm e.symm = _
    rw [(lieEquiv e h).surjective.exists]
    refine exists_congr fun X => ?_
    rw [mem_ball, coe_lieEquiv, exp_submatrix]
    refine and_congr_right fun _ => ⟨fun hh => by rw [hh], fun hh => ?_⟩
    ext i j
    simpa using congrFun (congrFun hh (e i)) (e j)
  · refine Eq.trans ?_ (e2 _).symm
    congr 1
    ext X
    exact (mem_ball e h X r).symm

def swapIdx (N : ℕ) : Fin 0 ⊕ Fin N ≃ Fin (0 + N) ⊕ Fin 0 :=
  (Equiv.sumComm _ _).trans (Equiv.sumCongr (finCongr (Nat.zero_add N).symm) (Equiv.refl _))

theorem antiIso_swapIdx (N : ℕ) : AntiIso (swapIdx N) := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [swapIdx, Formalism.UG.Jpq, Matrix.one_apply, Fin.ext_iff]
    · exact j.elim0
  · exact i.elim0

theorem cd_zero_univ : ∀ (c : CDHaar) (N : ℕ), c.cd 0 N Set.univ = 1 := by
  intro c N
  obtain ⟨d, hd0, hdt, h1, h2⟩ := c.trick 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc 0 N
  obtain ⟨_, _, _, _, _, -⟩ := GlobalTheory.UpqTopology.upq_lcsc (0 + N) 0
  have := c.haar 0 N
  have := c.haar (0 + N) 0
  have := c.prob (0 + N)
  let G := grpEquiv (swapIdx N) (antiIso_swapIdx N)
  have : ((c.cd 0 N).map G).IsHaarMeasure := G.isHaarMeasure_map _
  have h3 := omegaDensity_map _ (antiIso_swapIdx N) _ _ h1
  have h4 := Measure.isMulLeftInvariant_eq_smul ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  set a := Measure.haarScalarFactor ((c.cd 0 N).map G) (c.cd (0 + N) 0)
  have h5 : OmegaDensity ((c.cd 0 N).map G) (a * d) := by
    rw [h4]; exact (GlobalTheory.T.omegaDensity_upq_unique_and_smul _ _ _ _ h2).2 a
  have h6 : (a : ENNReal) * d = 1 * d := by
    rw [one_mul]; exact (GlobalTheory.T.omegaDensity_upq_unique_and_smul _ _ _ _ h3).1 _ h5
  have h7 : (a : ENNReal) = 1 := (ENNReal.mul_left_inj hd0 hdt).1 h6
  have h8 : ((c.cd 0 N).map G) Set.univ = 1 := by
    rw [h4, Measure.smul_apply, measure_univ, ENNReal.smul_def, h7, one_smul]
  have hG : Measurable G := G.continuous.measurable
  rwa [Measure.map_apply hG MeasurableSet.univ, Set.preimage_univ] at h8

end GlobalTheory.CompactDualSwap
end
end
