module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.SupThetaGrowth

theorem om_sup_quotHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  intro D ψ S T χS χT om hom f hf
  obtain ⟨C, A, hC⟩ := om_sup_growth D ψ S T χS χT om hom f hf
  refine ⟨max C 0 * 4 ^ A, A, fun g h w => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  have e := om_rat_mul D ψ S T χS χT om hom f hf γ⁻¹ (inv_mem hγ) γ'⁻¹ (inv_mem hγ') (γ * g) (γ' * h) w
  rw [inv_mul_cancel_left, inv_mul_cancel_left] at e
  rw [e]
  have p1 := (height_pos S (γ * g)).le
  have p2 := (height_pos T (γ' * h)).le
  have q1 := (quotHeight_pos S g).le
  calc _ ≤ C * (height S (γ * g) * height T (γ' * h)) ^ A := hC _ _ _
    _ ≤ max C 0 * (height S (γ * g) * height T (γ' * h)) ^ A :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (mul_nonneg p1 p2) A)
    _ ≤ max C 0 * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg p1 p2)
          (mul_le_mul h1 h2 p2 (mul_nonneg zero_le_two q1)) A) (le_max_right _ _)
    _ = max C 0 * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A := by
        generalize quotHeight S g = a
        generalize quotHeight T h = b
        rw [show 2 * a * (2 * b) = 4 * (a * b) by ring, mul_pow, mul_assoc]

end GlobalTheory.SupThetaGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeigStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_thetaFunction_sup_le_quotientHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  first | exact @GlobalTheory.SupThetaGrowth.om_sup_quotHeight | exact GlobalTheory.SupThetaGrowth.om_sup_quotHeight | (intros; apply GlobalTheory.SupThetaGrowth.om_sup_quotHeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.CongrOrbit

variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem quot_mapMatrix_eq_one_iff (I : Ideal O) (A : Matrix n n O) :
    (Ideal.Quotient.mk I).mapMatrix A = 1 ↔ ∀ i j, (A - 1) i j ∈ I := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simpa [Matrix.one_apply, apply_ite] using this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simpa [Matrix.one_apply, apply_ite] using this

theorem isUnit_det_of_sub_one_mem (I : Ideal O) (hI : I ≤ Ideal.jacobson ⊥) (A : Matrix n n O)
    (hA : ∀ i j, (A - 1) i j ∈ I) : IsUnit A.det := by
  have h1 := (quot_mapMatrix_eq_one_iff I A).2 hA
  have h2 : Ideal.Quotient.mk I A.det = 1 := by
    rw [RingHom.map_det, h1, Matrix.det_one]
  have h3 : A.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, h2, map_one]
  have h4 := (Ideal.mem_jacobson_bot.1 (hI h3)) 1
  simpa using h4

variable {a b : Type} [Fintype a] [Fintype b]

def colFix (f : a → n) (ξ : a → n → O) : Matrix n n O :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    ∑ p, (ξ p i - if i = f p then 1 else 0) * (if j = f p then 1 else 0)

def rowFix (g : b → n) (ζ : b → n → O) : Matrix n n O :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    ∑ q, (if i = g q then 1 else 0) * (ζ q j - if g q = j then 1 else 0)

theorem colFix_sub_one_mem (I : Ideal O) (f : a → n) (ξ : a → n → O)
    (hξ : ∀ p i, ξ p i - (if i = f p then 1 else 0) ∈ I) (i j : n) :
    (colFix f ξ - 1) i j ∈ I := by
  simp only [colFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hξ p i)

theorem colFix_apply_col {f : a → n} (hf : Function.Injective f) (ξ : a → n → O) (i : n)
    (p₀ : a) : colFix f ξ i (f p₀) = ξ p₀ i := by
  simp only [colFix, Matrix.of_apply]
  rw [Finset.sum_eq_single p₀]
  · rw [if_pos rfl, mul_one]; ring
  · intro p _ hp
    rw [if_neg (fun h => hp (hf h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowFix_sub_one_mem (I : Ideal O) (g : b → n) (ζ : b → n → O)
    (hζ : ∀ q j, ζ q j - (if g q = j then 1 else 0) ∈ I) (i j : n) :
    (rowFix g ζ - 1) i j ∈ I := by
  simp only [rowFix, Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply, add_sub_cancel_left]
  exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (hζ q j)

theorem rowFix_apply_row {g : b → n} (hg : Function.Injective g) (ζ : b → n → O) (j : n)
    (q₀ : b) : rowFix g ζ (g q₀) j = ζ q₀ j := by
  simp only [rowFix, Matrix.of_apply]
  rw [Finset.sum_eq_single q₀]
  · rw [if_pos rfl, one_mul]; ring
  · intro q _ hq
    rw [if_neg (fun h => hq (hg h).symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rowFix_apply_col (f : a → n) (g : b → n) (ζ : b → n → O)
    (hζ : ∀ q p, ζ q (f p) = if g q = f p then 1 else 0) (i : n) (p : a) :
    rowFix g ζ i (f p) = if i = f p then 1 else 0 := by
  simp only [rowFix, Matrix.of_apply, hζ, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem vecMul_sub_single_mem (I : Ideal O) (A : Matrix n n O)
    (hA : ∀ i j, (A - 1) i j ∈ I) (v : n → O) (c : n)
    (hv : ∀ i, v i - (if i = c then 1 else 0) ∈ I) (j : n) :
    (v ᵥ* A) j - (if c = j then 1 else 0) ∈ I := by
  have e1 : (v ᵥ* A) j = (v ᵥ* (A - 1)) j + v j := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply]; ring
  have e2 : (if c = j then (1 : O) else 0) = if j = c then 1 else 0 := by
    by_cases h : c = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [e1, e2, add_sub_assoc]
  refine add_mem ?_ (hv j)
  simp only [Matrix.vecMul, dotProduct]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hA i j)

end GlobalTheory.AscFin.CongrOrbit

theorem GlobalTheory.AscFin.exists_gl_congr_cols_rows : ∀ (O : Type) [CommRing O] (I : Ideal O), I ≤ Ideal.jacobson ⊥ → ∀ (n a b : Type) [Fintype n] [DecidableEq n] [Fintype a] [Fintype b] (f : a → n) (g : b → n), Function.Injective f → Function.Injective g → ∀ (ξ : a → n → O) (η : b → n → O), (∀ p i, ξ p i - (if i = f p then 1 else 0) ∈ I) → (∀ q i, η q i - (if i = g q then 1 else 0) ∈ I) → (∀ p q, η q ⬝ᵥ ξ p = if g q = f p then 1 else 0) → ∃ k : GL n O, (∀ i j, (k.1 - 1) i j ∈ I) ∧ (∀ p i, k.1 i (f p) = ξ p i) ∧ ∀ q, η q ᵥ* k.1 = fun i => if i = g q then 1 else 0 := by
  intro O _ I hI n a b _ _ _ _ f g hf hg ξ η hξ hη hηξ
  open GlobalTheory.AscFin.CongrOrbit in
  set k₁ := colFix f ξ with hk₁
  have hk₁I := colFix_sub_one_mem I f ξ hξ
  set ζ : b → n → O := fun q => η q ᵥ* k₁ with hζdef
  have hζI : ∀ q j, ζ q j - (if g q = j then 1 else 0) ∈ I := fun q j =>
    vecMul_sub_single_mem I k₁ hk₁I (η q) (g q) (hη q) j
  have hζcol : ∀ q p, ζ q (f p) = if g q = f p then 1 else 0 := by
    intro q p
    have hc : (fun i => k₁ i (f p)) = ξ p := funext fun i => colFix_apply_col hf ξ i p
    simp only [hζdef, Matrix.vecMul]
    rw [hc, hηξ]
  set m := rowFix g ζ with hm
  have hmI := rowFix_sub_one_mem I g ζ hζI
  have hmcol : ∀ i p, m i (f p) = if i = f p then 1 else 0 := rowFix_apply_col f g ζ hζcol
  have u₁ := isUnit_det_of_sub_one_mem I hI k₁ hk₁I
  have um := isUnit_det_of_sub_one_mem I hI m hmI
  set U₁ := Matrix.nonsingInvUnit k₁ u₁
  set Um := Matrix.nonsingInvUnit m um
  set Wm : Matrix n n O := ((Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) with hWm
  have hWmm : Wm * m = 1 := Um.inv_mul
  have hmWm : m * Wm = 1 := Um.mul_inv
  have hval : ((U₁ * Um⁻¹ : (Matrix n n O)ˣ) : Matrix n n O) = k₁ * Wm := rfl
  refine ⟨U₁ * Um⁻¹, ?_, ?_, ?_⟩
  · rw [hval, ← quot_mapMatrix_eq_one_iff]
    have e1 := (quot_mapMatrix_eq_one_iff I k₁).2 hk₁I
    have e2 := (quot_mapMatrix_eq_one_iff I m).2 hmI
    have eW : (Ideal.Quotient.mk I).mapMatrix Wm = 1 := by
      calc (Ideal.Quotient.mk I).mapMatrix Wm
          = (Ideal.Quotient.mk I).mapMatrix Wm * (Ideal.Quotient.mk I).mapMatrix m := by
            rw [e2, mul_one]
        _ = 1 := by rw [← map_mul, hWmm, map_one]
    rw [map_mul, e1, eW, one_mul]
  · intro p i
    rw [hval]
    have hWcol : ∀ l, Wm l (f p) = if l = f p then 1 else 0 := by
      intro l
      have := congrFun (congrFun hWmm l) (f p)
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simpa only [hmcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] using this
    rw [Matrix.mul_apply]
    simp only [hWcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact colFix_apply_col hf ξ i p
  · intro q
    rw [hval, ← Matrix.vecMul_vecMul]
    funext j
    have hrow : η q ᵥ* k₁ = fun l => m (g q) l := by
      funext l; rw [hm, rowFix_apply_row hg]
    rw [hrow]
    have := congrFun (congrFun hmWm (g q)) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.vecMul, dotProduct]
    rw [this]
    by_cases h : g q = j
    · simp [h]
    · simp [h, Ne.symm h]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.VacSub

theorem exists_vacG_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Γ ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ∃ f, VacG ψ S T Γ f ∧ f ≠ 0 := by
  intro D ψ hψ S T LS LT dS dT Γ hΓ
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) LS LT dS dT
  obtain ⟨h1, h2, -⟩ := hf 1
  simp only [one_mul] at h1 h2
  exact ⟨f, ⟨h1, fun u hu => h2.1 u (hΓ hu), fun e he u hu hh => h2.2 e he u (hΓ hu) hh⟩, f0⟩

end GlobalTheory.AscFin.VacSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroLatticeVacuumSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_latticeVacuum_selfDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Γ ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ∃ f, VacG ψ S T Γ f ∧ f ≠ 0 := by
  first | exact @GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero | exact GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero | (intros; apply GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumConjugationDictionaryRowGrid
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumConjugationDictionaryRowGrid
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ConjDict

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ConjWeil

variable {D : D7}

theorem cjOm_apply {S T : HSp D} (om : Om (negSp S) T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    cjOm om p f = cj id (om (negGA S p.1, p.2) (cj id f)) := rfl

theorem negGA_mem_GQ (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _)

theorem weil_cjOm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om (negSp S) T) (hw : IsWeilDatumO ψ (negSp S) T χS χT om) :
    IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (cjOm om) := _root_.GlobalTheory.Asc.FamilyModel.weil_cjOm ψ S T χS χT om hw

theorem vac_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) :
    VacG ψ (negSp S) T Γ f ↔ VacG ψ S T Γ (star f) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T
  have e0 : star f = cj id f := rfl
  have th : IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hz : ∀ w : WO S T, heisO ψ (negSp S) T w f = f ↔ heisO ψ S T w (cj id f) = cj id f := fun w => by
    have := (I.2 w (cj id f)).2
    rw [cj_id_cj_id] at this
    rw [this]
    exact ⟨fun h => by have := congrArg (cj id) h; rwa [cj_id_cj_id] at this, fun h => by rw [h, cj_id_cj_id]⟩
  rw [e0]
  unfold VacG IsLatVac
  simp only [th, hz]

theorem conj_dict : GlobalTheory.SepRows.DepFixed → All fun {D} _ {L} _ {G} W _ => ∀ i, i < D.R.m → IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧ IsWeilDatumO W.ψ _ _ (G.chrS (.core i))⁻¹ (G.chrT (.core i))⁻¹ (omCore W i) ∧ (∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f)) ∧ (∀ f, VacG W.ψ _ _ (latCore G i) f ↔ Dep W (.core i) (star f)) ∧ (∀ g h f, omRow W i (g, h) f = star (W.om (.chi i 0) (negGA _ g, h) (star f))) ∧ (∀ g h f, omCore W i (g, h) f = star (W.om (.core i) (negGA _ g, h) (star f))) ∧ ∀ f, VacG W.ψ _ _ (latRow G i) f → ∀ k ∈ lev G (.grid i 0), omRow W i (1, k) f = f := by
  intro h1 D hq T L μ0 hL sc G W M hM i hi
  have hv : ∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f) := fun f =>
    ((vac_star W.ψ_std (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (latRow G i) (star f)).trans
      (by rw [star_star])).symm
  refine ⟨weil_cjOm W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩),
    weil_cjOm W.ψ (G.V (.core (i + 1))) (G.V (.core i)) _ _ _ (W.om_is (.core i) hi), hv, fun f =>
    ((vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) (star f)).trans (by rw [star_star])).symm,
    fun g h f => rfl, fun g h f => rfl, fun f hf k hk => ?_⟩
  have e := h1 D hq T L μ0 hL sc G W M hM i hi (.chi i 0) (Or.inl rfl) (star f) ((hv f).1 hf) k hk 1 (one_mem _)
  show star (W.om (.chi i 0) (G.toPair (.chi i 0) k 1) (star f)) = f
  rw [e, star_star]

end GlobalTheory.ConjDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumConjugationDictionaryRowGridStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_conjugation_dictionary_row_grid : GlobalTheory.SepRows.DepFixed → All fun {D} _ {L} _ {G} W _ => ∀ i, i < D.R.m → IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧ IsWeilDatumO W.ψ _ _ (G.chrS (.core i))⁻¹ (G.chrT (.core i))⁻¹ (omCore W i) ∧ (∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f)) ∧ (∀ f, VacG W.ψ _ _ (latCore G i) f ↔ Dep W (.core i) (star f)) ∧ (∀ g h f, omRow W i (g, h) f = star (W.om (.chi i 0) (negGA _ g, h) (star f))) ∧ (∀ g h f, omCore W i (g, h) f = star (W.om (.core i) (negGA _ g, h) (star f))) ∧ ∀ f, VacG W.ψ _ _ (latRow G i) f → ∀ k ∈ lev G (.grid i 0), omRow W i (1, k) f = f := by
  first | exact @GlobalTheory.ConjDict.conj_dict | exact GlobalTheory.ConjDict.conj_dict | (intros; apply GlobalTheory.ConjDict.conj_dict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmoothStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_orbit_coefficient_smooth : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  first | exact @GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | exact GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth | (intros; apply GlobalTheory.HeisOrbitSmooth.archCo_orbit_smooth <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.CharXFB
variable {D : D7}

def hA (T : HSp D) (y z : Fin T.rank → AE D) : AE D := ∑ k, cA D (z k) * (gA T *ᵥ y) k

theorem pairS_eq_sum (T : HSp D) {ρ : ℕ} (x x' : Mx D T.rank ρ) :
    pairS T x x' = ∑ p, hA T (fun k => x k p) (fun k => x' k p) := by
  simp only [pairS, hA, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem mxAt_of_mem_depLat {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {p : Pair T}
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ depLat G p) : MxAt (fun _ => True) u :=
  GlobalTheory.FinPl.LatMem.latO_mxAt hu.1

end GlobalTheory.CharXFB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulMemComplId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

def complId (𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : AddSubgroup (AE D) :=
  AddSubgroup.closure {s | ∃ α ∈ intAf D.host.F, ∃ a ∈ 𝔠, s = pairA D.host.F 0 α ⊗ₜ[D.host.F] a}

theorem tmul_mem_complId {𝔠 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    {a : D.host.E} (ha : a ∈ 𝔠) : pairA D.host.F 0 α ⊗ₜ[D.host.F] a ∈ complId 𝔠 :=
  AddSubgroup.subset_closure ⟨α, hα, a, ha, rfl⟩

end GlobalTheory.XCharBF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreProjectionMemLatticeOfSplits
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreProjectionMemLatticeOfSplits
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.FinPl.CoreProj

theorem rat_mulVec_gen' {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem wittCoreProjection_mem_lattice_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S₀.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S₀ L₀ (· = v)) → z ∈ L₀) → (∀ v, MonoAt d L L₀ v) → ∀ t ∈ L, d.q0 *ᵥ t ∈ L₀ := by
  intro D S S₀ ρ d L L₀ hlg hmono t ht
  refine hlg _ fun v => ?_
  have hY : (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * t i)) ∈
      latV S L (· = v) :=
    AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _, GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, t, ht, rfl⟩
  have h := ((hmono v _).1 hY).2.2
  rw [HypDec.p0, rat_mulVec_gen'] at h
  simpa only [one_mul] using h

end GlobalTheory.FinPl.CoreProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreProjectionMemLatticeOfSplitsStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.q0_mulVec_mem_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S₀.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S₀ L₀ (· = v)) → z ∈ L₀) → (∀ v, MonoAt d L L₀ v) → ∀ t ∈ L, d.q0 *ᵥ t ∈ L₀ := by
  first | exact @GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits | exact GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits | (intros; apply GlobalTheory.FinPl.CoreProj.wittCoreProjection_mem_lattice_of_splits <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelf
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.Twist.RatLatO

variable {D : D7}

theorem incA_eq_tmul (e : D.host.E) : incA D e = ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := rfl

theorem rat_mulVec_mem_latMul {S T : HSp D} (𝔞 : Set D.host.E) {L : Lat S} {L' : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (hM : ∀ t ∈ L, M *ᵥ t ∈ L')
    {z : Fin S.rank → AE D} (hz : z ∈ GlobalTheory.FinPl.latMul S 𝔞 L P) : rat M *ᵥ z ∈ GlobalTheory.FinPl.latMul T 𝔞 L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, M *ᵥ s, hM s hs, ?_⟩
    funext i
    simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, incA_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, ← TensorProduct.tmul_sum]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem rat_mul_mem_latO : ∀ {D : D7} {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}, IsSelfDualC S LS → IsSelfDualC S' LS' → IsSelfDualC T' LT' → ∀ (j : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E), (∀ y ∈ LS', j *ᵥ y ∈ LS) → (∀ t ∈ LT, q *ᵥ t ∈ LT') → ∀ x : WO S T, x ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) → (rat q * x * rat j : WO S' T') ∈ latO S' T' (LS' : Set _) (LT' : Set _) (fun _ => True) := by
  intro D S S' T T' LS LS' LT LT' hS hS' hT' j q hj hq x hx
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S' T' LS' LT' hS' hT']
  refine ⟨fun i k => ?_, fun y hy => ?_⟩
  · have hxM := GlobalTheory.FinPl.LatMem.latO_mxAt hx
    simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _
      (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hxM m l))
  · show (rat q * x * rat j) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : rat j *ᵥ y ∈ latV S LS (fun _ => True) :=
      rat_mulVec_mem_latMul (L := LS') (L' := LS) (P := fun _ => True) {1} j hj hy
    have h2 : x *ᵥ (rat j *ᵥ y) ∈ latA T LT (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hS hx h1
    exact rat_mulVec_mem_latMul (L := LT) (L' := LT') (P := fun _ => True) {a | a ∈ D.host.AA} q hq h2

end GlobalTheory.Twist.RatLatO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedHomLatticeSelfStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual : ∀ {D : D7} {S S' T T' : HSp D} {LS : Lat S} {LS' : Lat S'} {LT : Lat T} {LT' : Lat T'}, IsSelfDualC S LS → IsSelfDualC S' LS' → IsSelfDualC T' LT' → ∀ (j : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E), (∀ y ∈ LS', j *ᵥ y ∈ LS) → (∀ t ∈ LT, q *ᵥ t ∈ LT') → ∀ x : WO S T, x ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) → (rat q * x * rat j : WO S' T') ∈ latO S' T' (LS' : Set _) (LT' : Set _) (fun _ => True) := by
  first | exact @GlobalTheory.Twist.RatLatO.rat_mul_mem_latO | exact GlobalTheory.Twist.RatLatO.rat_mul_mem_latO | (intros; apply GlobalTheory.Twist.RatLatO.rat_mul_mem_latO <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHo
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHo
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.TwistHatMx

theorem homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (h : Matrix (Fin m) (Fin n) D.host.E) (hh : h ∈ homLat Λ Λ') : q * h * j ∈ homLat M M' := by
  intro y hy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hq _ (hh _ (hj _ hy))

theorem smul_homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Matrix (Fin m) (Fin n) D.host.E) (hx : x ∈ 𝔪 • homLat Λ Λ') : q * x * j ∈ 𝔪 • homLat M M' := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro c hc h hh
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem_smul hc (homLat_conj j q hj hq h hh)
  · intro a b ha hb
    rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ ha hb

theorem gen_conj {D : D7} {m n m' n' : ℕ} (a : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) :
    rat q * (Matrix.of fun i k => a ⊗ₜ[D.host.F] x i k) * rat j = Matrix.of fun i k => a ⊗ₜ[D.host.F] (q * x * j) i k := by
  have e : ∀ {r s : ℕ} (y : Matrix (Fin r) (Fin s) D.host.E), (Matrix.of fun i k => a ⊗ₜ[D.host.F] y i k) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • rat y := by
    intro r s y
    ext i k
    simp [rat, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [rat, Matrix.map_mul]

theorem rat_conj_mem_hatMx {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Mx D m n) (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    rw [gen_conj]
    exact AddSubgroup.subset_closure ⟨α, hα, q * y * j, smul_homLat_conj 𝔪 j q hj hq y hy, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha =>
    rw [Matrix.mul_neg, Matrix.neg_mul]
    exact AddSubgroup.neg_mem _ ha

end GlobalTheory.TwistHatMx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHoStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrix_sandwich_mem_completed_ideal_latticeHom : ∀ {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E), (∀ y ∈ M, j *ᵥ y ∈ Λ) → (∀ t ∈ Λ', q *ᵥ t ∈ M') → ∀ x : Mx D m n, x ∈ hatMx (𝔪 • homLat Λ Λ') → rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  first | exact @GlobalTheory.TwistHatMx.rat_conj_mem_hatMx | exact GlobalTheory.TwistHatMx.rat_conj_mem_hatMx | (intros; apply GlobalTheory.TwistHatMx.rat_conj_mem_hatMx <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMove
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMove
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.PrincipalMove

open GlobalTheory.FinPlLoc

theorem exists_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k * x - mt W g⁻¹ * (x * u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  intro D W ρ x Q g k u hg hk hM
  set e : AE D := idem D Q with he_def
  have he : e * e = e := idem_mul_self Q
  have hr : g * k ∈ grpAt W Q := mul_mem hg hk
  set U : Matrix (Fin ρ) (Fin ρ) (AE D) := u.1.1 with hU
  have hu : ∀ i j : Fin ρ, (j < i → U i j = 0) ∧ U i i = 1 := fun i j => u.2 i j
  let u' : GL (Fin ρ) (AE D) := mixGL he u.1 1
  have hu'v : u'.val = e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) := rfl
  have hu' : u' ∈ UX D ρ := by
    intro i j
    refine ⟨fun hij => ?_, ?_⟩
    · show u'.val i j = 0
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i j).1 hij, Matrix.one_apply_ne hij.ne']
    · show u'.val i i = 1
      rw [hu'v]
      simp [Matrix.add_apply, Matrix.smul_apply, (hu i i).2]
  refine ⟨g * k, ⟨u', hu', ?_⟩, hr, by group⟩
  have heM : e • (mt W k * x - mt W g⁻¹ * (x * U)) = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact (mem_idOff_iff Q _).1 (hM i j)
  have hgg : mt W g * mt W g⁻¹ = 1 := by
    rw [← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one]
  have h1 : e • (mt W (g * k) * x) = e • (x * U) := by
    have : mt W (g * k) * x = x * U + mt W g * (mt W k * x - mt W g⁻¹ * (x * U)) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc (mt W g) (mt W g⁻¹), hgg, Matrix.one_mul, FinPlLoc.mt_mul, Matrix.mul_assoc]
      abel
    rw [this, smul_add, ← Matrix.mul_smul (mt W g), heM, Matrix.mul_zero, add_zero]
  have h2 : (1 - e) • (mt W (g * k) * x) = (1 - e) • x := by
    have hm := (mem_grpAt_iff Q (g * k)).1 hr
    have : (1 - e) • mt W (g * k) = (1 - e) • (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) := by
      conv_lhs => rw [← hm]
      simp only [mix, smul_add, smul_smul]
      have h3 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
      have h4 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
      rw [h3, h4, zero_smul, zero_add]
    rw [← Matrix.smul_mul, this, Matrix.smul_mul, Matrix.one_mul]
  show mt W (g * k) * x = x * u'.val
  rw [hu'v]
  calc mt W (g * k) * x = e • (mt W (g * k) * x) + (1 - e) • (mt W (g * k) * x) := by
        rw [← add_smul, add_sub_cancel, one_smul]
    _ = e • (x * U) + (1 - e) • x := by rw [h1, h2]
    _ = x * (e • U + (1 - e) • (1 : Matrix (Fin ρ) (Fin ρ) (AE D))) := by
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]

end GlobalTheory.PrincipalMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMoveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  first | exact @GlobalTheory.PrincipalMove.exists_move | exact GlobalTheory.PrincipalMove.exists_move | (intros; apply GlobalTheory.PrincipalMove.exists_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHaarCoordinateReversalPositiveMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHaarCoordinateReversalPositiveMultiple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarRev

theorem haar_rev : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  intro m ε
  set ε' : Fin m → Bool := fun a => ε a.rev with hε'
  have he : ∀ a, ε' a = ε a.rev := fun a => rfl
  let φ : Formalism.REAL.UJ ε ≃* Formalism.REAL.UJ ε' := GlobalTheory.ConjDS.rvU (GlobalTheory.ConjDS.sg_symm he)
  have hφ : Continuous φ := GlobalTheory.ConjDS.rvU_cont _
  have hφs : Continuous φ.symm := GlobalTheory.ConjDS.rvU_cont he
  haveI : ((Formalism.REAL.muG ε).map φ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ φ hφ hφs
  set c := Measure.haarScalarFactor ((Formalism.REAL.muG ε).map φ) (Formalism.REAL.muG ε') with hc
  have hmap : (Formalism.REAL.muG ε).map φ = c • Formalism.REAL.muG ε' :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := by
    intro h0
    have : (Formalism.REAL.muG ε).map φ = 0 := by rw [hmap, h0, zero_smul]
    exact (Measure.IsHaarMeasure.toIsOpenPosMeasure (μ := (Formalism.REAL.muG ε).map φ)).open_pos _ isOpen_univ
      Set.univ_nonempty (by rw [this]; rfl)
  let e : Formalism.REAL.UJ ε ≃ᵐ Formalism.REAL.UJ ε' :=
    { toEquiv := φ.toEquiv, measurable_toFun := hφ.measurable, measurable_invFun := hφs.measurable }
  have he' : ⇑e = ⇑φ := rfl
  refine ⟨(c : ℝ), by positivity, ?_⟩
  intro E _ _ F
  have hcomp : (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) =
      (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)) ∘ e := rfl
  constructor
  · rw [hcomp, ← integrable_map_equiv e, he', hmap, ENNReal.smul_def]
    exact integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top
  · show ∫ u, F (Formalism.MainNotions.S.umat (e u)) ∂(Formalism.REAL.muG ε) = _
    rw [← integral_map_equiv e (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)), he', hmap, integral_smul_nnreal_measure, NNReal.smul_def]

end GlobalTheory.HaarRev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHaarCoordinateReversalPositiveMultipleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  first | exact @GlobalTheory.HaarRev.haar_rev | exact GlobalTheory.HaarRev.haar_rev | (intros; apply GlobalTheory.HaarRev.haar_rev <;> assumption)
end
end
