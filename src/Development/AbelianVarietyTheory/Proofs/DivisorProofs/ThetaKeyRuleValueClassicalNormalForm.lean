module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSeventh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthUnitSizeBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCuspOfVanishOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KeyFormulaIffClauses
section -- merged from Development.AbelianVarietyTheory.BlockTheory.CMModuli.ExponentialDifferential
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms

def In {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens) : Prop :=
  (⊤ : (Sp R).Opens) ≤ x ⁻¹ᵁ U

def val {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) {U : X.Opens} (h : In x U)
    (f : Γ(X, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE U ⊤ h).hom f)

abbrev Pt (A : Over (Sp ℂ)) : Type := 𝟙_ (Over (Sp ℂ)) ⟶ A

abbrev Pt.mor {A : Over (Sp ℂ)} (x : Pt A) : Sp ℂ ⟶ A.left := x.left

abbrev EpsPt (A : Over (Sp ℂ)) : Type := epsPt (𝟙 (Sp ℂ)) ⟶ A

abbrev EpsPt.mor {A : Over (Sp ℂ)} (v : EpsPt A) : Sp (DualNumber ℂ) ⟶ A.left := v.left


open Classical in
def extZero {V : Type} (s : Set V) (F : ∀ z, z ∈ s → ℂ) : V → ℂ :=
  fun z => if h : z ∈ s then F z h else 0

section Hol

variable {g : ℕ} {A : Over (Sp ℂ)}

def pre (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) : Set (Fin g → ℂ) := {z | In (u z).mor U}

def comp (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) (f : Γ(A.left, U)) : (Fin g → ℂ) → ℂ :=
  extZero (pre u U) (fun z h => val (u z).mor h f)

def IsHol (u : (Fin g → ℂ) → Pt A) : Prop :=
  ∀ U : A.left.Opens, IsOpen (pre u U) ∧ ∀ f : Γ(A.left, U), DifferentiableOn ℂ (comp u U f) (pre u U)

variable [GrpObj A]

def IsTangent (v : EpsPt A) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.mor = (1 : Pt A).mor

def IsDiffAt (u : (Fin g → ℂ) → Pt A) (w : Fin g → ℂ) (v : EpsPt A) : Prop :=
  IsTangent v ∧ ∀ (U : A.left.Opens) (h : In v.mor U) (f : Γ(A.left, U)),
    HasDerivAt (fun t : ℂ => comp u U f (t • w)) (val v.mor h f).snd 0

end Hol

structure Exp (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) where
  exp : (Fin g → ℂ) → Pt A
  exp_add : ∀ z z', exp (z + z') = exp z * exp z'
  hol : IsHol exp
  onto : Function.Surjective exp
  locIso : ∀ v : EpsPt A, IsTangent v → ∃! w, IsDiffAt exp w v
  discrete : DiscreteTopology {z : Fin g → ℂ | exp z = 1}
  span : Submodule.span ℝ {z : Fin g → ℂ | exp z = 1} = ⊤

namespace Exp

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g)

def hom : Multiplicative (Fin g → ℂ) →* Pt A :=
  MonoidHom.mk' (fun z => E.exp z.toAdd) (fun _ _ => E.exp_add _ _)

end Exp

structure Unif (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) extends Exp A g where
  isLB : L.IsLB
  fr : ∀ (i : L.ι) (z : Fin g → ℂ), z ∈ pre exp (L.U i) → ℂ
  fr_ne : ∀ i z h, fr i z h ≠ 0
  fr_hol : ∀ i, DifferentiableOn ℂ (extZero (pre exp (L.U i)) (fr i)) (pre exp (L.U i))
  fr_compat : ∀ (i j : L.ι) (z : Fin g → ℂ) (hi : z ∈ pre exp (L.U i)) (hj : z ∈ pre exp (L.U j))
    (hij : In (exp z).mor (L.U i ⊓ L.U j)),
    fr i z hi = val (exp z).mor hij (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) * fr j z hj

structure AHDatum {g : ℕ} (La : Submodule ℤ (Fin g → ℂ)) where
  H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ
  herm : ∀ x y, H y x = starRingEnd ℂ (H x y)
  pos : ∀ x, x ≠ 0 → 0 < (H x x).re
  integral : ∀ la mu : La, ∃ n : ℤ, (H la mu).im = n
  ch : La → ℂ
  ch_norm : ∀ la, ‖ch la‖ = 1
  ch_add : ∀ la mu : La,
    ch (la + mu) = ch la * ch mu * Complex.exp (π * Complex.I * ((H la mu).im : ℝ))

def AHDatum.factor {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (la : La) (z : Fin g → ℂ) : ℂ :=
  D.ch la * Complex.exp (π * D.H z la + π * D.H la la / 2)

namespace Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)

end Unif

def e (x : ℂ) : ℂ := Complex.exp (2 * π * Complex.I * x)

def Siegel (g : ℕ) : Type :=
  {τ : Matrix (Fin g) (Fin g) ℂ // τ.IsSymm ∧ (τ.map Complex.im).PosDef}

def thetaTerm {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℤ) : ℂ :=
  e ((∑ i, ∑ j, ((l i : ℂ) + a i) * τ i j * ((l j : ℂ) + a j)) / 2 + ∑ i, ((l i : ℂ) + a i) * (z i + b i))

def theta {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Siegel g) : ℂ :=
  ∑' l : Fin g → ℤ, thetaTerm a b z τ.1 l

end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
end
end

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyFormulaCompare

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def Same (u : HolUnif A L g) (F : Unif A L g) : Prop :=
  F.exp = u.ex ∧ ∀ i z h, F.fr i z h = u.fr i z

namespace Same

variable {u : HolUnif A L g} {F : Unif A L g} (h : Same u F)
include h

end Same

end Unif

section Analytic

end Analytic

section Principal

theorem tangent_bijective (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) :
    (∀ v, Geo.Tor.IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, Geo.Tor.IsTangent v ∧ u.IsDiff w v := by
  obtain ⟨u₀, H₀, χ₀, E₀, -, -, hv, hw, -⟩ := thetaUnifAV_closed x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex
    u.ex_add (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u₀.IsDiff (e w) v :=
    UnifCompare.isDiff_iff u u₀ e.toContinuousLinearEquiv hF
  refine ⟨fun v hv' => ?_, fun w => ?_⟩
  · obtain ⟨w, h1, h2⟩ := hv v hv'
    refine ⟨e.symm w, (hd _ _).2 (by rwa [e.apply_symm_apply]), fun y hy => ?_⟩
    rw [← h2 _ ((hd _ _).1 hy), e.symm_apply_apply]
  · simp only [hd]
    exact hw (e w)

theorem det_ne_zero (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
    (hW : ∀ i, u.IsDiff (W i) (x.v i)) : W.det ≠ 0 := by
  obtain ⟨h₁, h₂⟩ := tangent_bijective x u
  refine ((Matrix.isUnit_iff_isUnit_det W).1 (Matrix.vecMul_surjective_iff_isUnit.1 fun w => ?_)).ne_zero
  obtain ⟨v, hv, hd⟩ := (h₂ w).exists
  obtain ⟨c, hc⟩ := (x.basis.2 v hv).exists
  exact ⟨c, (Matrix.vecMul_eq_sum c W).trans ((h₁ v hv).unique
    (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W x.v c v x.basis.1 hW hc) hd)⟩

end Principal

section Clauses

abbrev RuleIn : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ

variable (κ : RuleIn)

end Clauses

end GlobalTheory.KeyFormulaCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem key_value_of_nf : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  intro κ hH hT g x hg u τ a b c Mx h
  subst hg
  obtain ⟨h₁, h₂, ha, hb, hc, hΛ, hr, hs, hd⟩ := h
  have hW := GlobalTheory.KeyFormulaCompare.det_ne_zero x u ((2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx) hd
  have hM : Mx.det ≠ 0 := by
    rw [Matrix.det_smul] at hW
    exact right_ne_zero_of_mul hW
  refine ⟨hM, ?_⟩
  have hN : KeyPow.NormalAt x τ Mx a b c := ⟨u, h₁, h₂, hΛ, hr, hs, hd⟩
  obtain ⟨P, hg, rig, hr', th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, h₀, e₁, e₂⟩ := KeyConst.exists_rescale _ _ _ _ _ _ _ _ _ _ _ _ _ hc hM hN
  obtain ⟨u₀, t₁, t₂, t₃, t₄, t₅, t₆⟩ := (KeyPow.normalAt_one_iff _ _ _ _).1 h₀
  have h₃ := hH ℂ P hg rig hr' th₀ hth₀ v₀ hv₀ th hth v hv c Mx e₁ e₂
  have h₄ := hT _ u₀ _ _ _ t₁ t₂ ha hb t₃ t₄ t₅ t₆
  rw [h₄, Units.val_one, _root_.mul_one] at h₃
  rw [mul_comm]
  exact h₃.trans (_root_.mul_one _)

end GlobalTheory.MBLow.Cl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_value_classicalNormalForm : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  first | exact @GlobalTheory.MBLow.Cl.key_value_of_nf | exact GlobalTheory.MBLow.Cl.key_value_of_nf | (intros; apply GlobalTheory.MBLow.Cl.key_value_of_nf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimes
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory.Rounding

variable {K : Type} [Field K] [NumberField K]

theorem lw_nonneg_here (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw K w := by
  unfold lw
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
  have : Ideal.absNorm w.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.2 this

theorem vAdd_int_nonneg (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) : 0 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]; exact Nat.cast_nonneg _

theorem vAdd_int_pos (w : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) (hm : x ∈ w.asIdeal) :
    1 ≤ vAdd w (x : K) := by
  rw [← vla_span hx w]
  have h0 : Ideal.span {x} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  have := (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w h0).2
    (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hm))
  omega

theorem finite_vla {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => (Formalism.L2.Pj.QAt.vla w I : ℝ)).Finite :=
  (Ideal.finite_factors hI).subset fun w h => by
    refine (Formalism.L2.Pj.QAt.BeSumPf.vla_ne_zero_iff w hI).1 fun h0 => h ?_
    simp [h0]

theorem sum_vla_lw {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w I : ℝ) * lw K w = Real.log (Ideal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  rw [finsum_eq_sum_of_support_subset (s := (finite_vla hI).toFinset) _
    (by simpa using Function.support_mul_subset_left _ _)]
  have h1 := Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin I hI (finite_vla hI).toFinset fun v hv => by
    simpa using hv
  rw [← h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [lw, mul_div_assoc]

theorem vAdd_mul_here (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  simp only [vAdd, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]; ring

theorem vAdd_inv_here (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd w x⁻¹ = -vAdd w x := by
  simp [vAdd, map_inv₀, WithZero.log_inv]

theorem count_inv_span (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap (𝓞 K) K c)⁻¹) =
      vAdd w (algebraMap (𝓞 K) K c)⁻¹ := by
  have hspan : Ideal.span {c} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hI : ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hspan
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.coeIdeal_span_singleton, vAdd_inv_here]
  have h1 := FractionalIdeal.count_mul K w hI (inv_ne_zero hI)
  rw [mul_inv_cancel₀ hI, FractionalIdeal.count_one] at h1
  have h2 : FractionalIdeal.count K w ((Ideal.span {c} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      vAdd w (algebraMap (𝓞 K) K c) := by
    rw [FractionalIdeal.count_coe K w hspan]
    exact vla_span hc w
  omega

theorem vla_eq_count (w : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (Formalism.L2.Pj.QAt.vla w I : ℤ) = FractionalIdeal.count K w (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  (FractionalIdeal.count_coe K w hI).symm

theorem exists_rounding (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hB : ∀ p ∈ B, p.Prime) (hρ : (Function.support ρ).Finite)
    (hint : ∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) :
    ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧
      (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧
      (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤
        -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) -
          Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  set f : HeightOneSpectrum (𝓞 K) → ℤ := fun w => -⌊ρ w⌋ with hf
  have hfs : Function.support f ⊆ Function.support ρ := fun w h h0 => h (by simp [hf, h0])
  have hfin : ∀ᶠ w in Filter.cofinite, f w = 0 := by
    rw [Filter.eventually_cofinite]; exact hρ.subset hfs
  set J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f w with hJdef
  have hJ0 : J ≠ 0 := by
    rw [hJdef, finprod_eq_prod_of_mulSupport_subset (s := hρ.toFinset)]
    · exact Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)
    · intro w hw
      simp only [Set.Finite.coe_toFinset]
      intro h0; apply hw; simp [hf, h0]
  have hcJ : ∀ w, FractionalIdeal.count K w J = f w := fun w => FractionalIdeal.count_finprod K w f hfin
  obtain ⟨c, 𝔞, hc, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  set a : K := (algebraMap (𝓞 K) K c)⁻¹ with ha
  have ha0 : a ≠ 0 := inv_ne_zero (by simpa using hc)
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rintro rfl; apply hJ0; rw [hJ]; simp
  have hsa0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.2 ha0
  have h𝔞0 : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsum : ∀ w, vAdd w a + (Formalism.L2.Pj.QAt.vla w 𝔞 : ℤ) = f w := fun w => by
    rw [← hcJ w, hJ, FractionalIdeal.count_mul K w hsa0 h𝔞0, vla_eq_count w h𝔞, ha, count_inv_span w hc]
  refine ⟨a, 𝔞, ha0, h𝔞, ?_, ?_⟩
  · intro b hb hb0 w
    have hspan : Ideal.span {b} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨e, he⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
    have he0 : e ≠ ⊥ := by rintro rfl; apply hspan; rw [he]; simp
    have hbK : (b : K) ≠ 0 := by simpa using hb0
    have h1 : vAdd w ((b : K) * a) = vAdd w (b : K) + vAdd w a := vAdd_mul_here w hbK ha0
    have h2 : vAdd w (b : K) = Formalism.L2.Pj.QAt.vla w 𝔞 + Formalism.L2.Pj.QAt.vla w e := by
      rw [← vla_span hb0 w, vla_eq_count w hspan, vla_eq_count w h𝔞, vla_eq_count w he0, he,
        FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K w h𝔞0 (FractionalIdeal.coeIdeal_ne_zero.2 he0)]
    have h3 : f w ≤ vAdd w ((b : K) * a) := by
      rw [h1, h2, ← hsum w]; have := (Formalism.L2.Pj.QAt.vla w e).zero_le; omega
    have h4 : (f w : ℝ) ≤ vAdd w ((b : K) * a) := by exact_mod_cast h3
    have h5 := Int.fract_nonneg (ρ w)
    rw [Int.fract] at h5
    simp only [hf, Int.cast_neg] at h4
    linarith
  · have e1 := lineDeg_num ha0
    unfold lineDeg at e1
    have e2 := sum_vla_lw h𝔞
    have e3 : (∑ᶠ w, (vAdd w a : ℝ) * lw K w) + ∑ᶠ w, (Formalism.L2.Pj.QAt.vla w 𝔞 : ℝ) * lw K w =
        ∑ᶠ w, (f w : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul (finite_vAdd ha0) _) (fin_mul (finite_vla h𝔞) _)]
      refine finsum_congr fun w => ?_
      rw [← add_mul, ← hsum w]; push_cast; ring
    set n : ℕ := ∏ p ∈ B, p with hn
    have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
    have e4 : ∑ p ∈ B, Real.log p = ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [sum_vAdd_nat hn0, hn, Nat.cast_prod, Real.log_prod]
      intro p hp; exact_mod_cast (hB p hp).ne_zero
    have hfinf : (Function.support fun w => (f w : ℝ) * lw K w).Finite :=
      (hρ.subset fun w h h0 => h (by simp [hf, h0]))
    have e5 : (∑ᶠ w, ρ w * lw K w) + ∑ᶠ w, (f w : ℝ) * lw K w ≤ ∑ᶠ w, (vAdd w (n : K) : ℝ) * lw K w := by
      rw [← finsum_add_distrib (fin_mul hρ _) hfinf]
      refine finsum_le_finsum' ((fin_mul hρ _).union hfinf |>.subset (Function.support_add _ _))
        (fin_mul (finite_vAdd (Nat.cast_ne_zero.2 hn0)) _) fun w => ?_
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (lw_nonneg_here w)
      have hfr : ρ w + (f w : ℝ) = Int.fract (ρ w) := by
        show ρ w + ((-⌊ρ w⌋ : ℤ) : ℝ) = Int.fract (ρ w)
        rw [Int.fract, Int.cast_neg]; ring
      rw [hfr]
      have hnK : ((n : 𝓞 K) : K) = (n : K) := by simp
      have hn0' : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hn0
      by_cases h : ∃ p ∈ B, ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
      · obtain ⟨p, hp, hpw⟩ := h
        obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun p : ℕ => p) hp
        have hmem : (n : 𝓞 K) ∈ w.asIdeal := by
          rw [hn, hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpw
        have h1 := vAdd_int_pos w hn0' hmem
        rw [hnK] at h1
        have h2 : (1 : ℝ) ≤ vAdd w (n : K) := by exact_mod_cast h1
        linarith [Int.fract_lt_one (ρ w)]
      · push_neg at h
        obtain ⟨m, hm⟩ := hint w h
        have h1 := vAdd_int_nonneg w hn0'
        rw [hnK] at h1
        rw [hm, Int.fract_intCast]
        have h2 : (0 : ℝ) ≤ (vAdd w (n : K) : ℝ) := Int.cast_nonneg h1
        simpa using h2
    have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.2 (Module.finrank_pos (R := ℚ) (M := K))
    linarith

end GlobalTheory.Rounding
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealRoundingRealExponentsBadPrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes : ∀ (K : Type) [Field K] [NumberField K] (B : Finset ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ), (∀ p ∈ B, p.Prime) → (Function.support ρ).Finite → (∀ w : HeightOneSpectrum (𝓞 K), (∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal) → ∃ n : ℤ, ρ w = n) → ∃ (a : K) (𝔞 : Ideal (𝓞 K)), a ≠ 0 ∧ 𝔞 ≠ ⊥ ∧ (∀ b ∈ 𝔞, b ≠ 0 → ∀ w, 0 ≤ (vAdd w ((b : K) * a) : ℝ) + ρ w) ∧ (∑ᶠ w, ρ w * lw K w) - ∑ p ∈ B, Real.log p ≤ -((∑ σ : K →+* ℂ, Real.log ‖σ a‖) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.Rounding.exists_rounding | exact GlobalTheory.Rounding.exists_rounding | (intros; apply GlobalTheory.Rounding.exists_rounding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBound
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

theorem degOn_add_rank_mul_degLo_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E) (B : Finset ℕ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ p ∈ B, p.Prime) → IntOff B s.lo → GoodOn U x V dict Z G → degOn U x V dict Z G + (rankOn U Z G : ℝ) * (s.degLo - logSum B) ≤ degOn U x V dict Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G₀ s G B hU hG hB hInt hGood
  haveI : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨a, 𝔞, ha, h𝔞, hint, hsum⟩ := GlobalTheory.T.exists_ideal_rounding_realExponents_badPrimes c.F B s.lo hB s.finite_lo hInt
  obtain ⟨φ, hφ, -, hlat, -⟩ := GlobalTheory.T.exists_linearEquiv_mul_twistingSection_integral E H Dw l Xo c r U x Z G₀ s G hG
  have hPres : GoodOn U x V dict Z (G + G₀) ∧ rankOn U Z (G + G₀) = rankOn U Z G :=
    GlobalTheory.T.twistingSection_preserves_hermitianLattices_ranks E H Dw l Xo c r U x D V dict Z G₀ s G hU hG hGood
  have hGood' : GoodOn U x V dict Z (G + G₀) := hPres.1
  have hrk : rankOn U Z (G + G₀) = rankOn U Z G := hPres.2
  have hna : ∀ σ : c.F →+* ℂ, 0 < ‖σ a‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  set t : (c.F →+* ℂ) → ℝ := fun σ => ‖σ a‖ * s.cInf σ with ht
  have ht0 : ∀ σ, 0 < t σ := fun σ => mul_pos (hna σ) (s.cInf_pos σ)
  have htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ := fun σ => by
    simp only [ht, RingHom.comp_apply, Complex.norm_conj]
    rw [s.cInf_congr (CompHt.goodOf_conj σ)]
  let ψ : cuspOn U Z G →ₗ[c.F] cuspOn U Z (G + G₀) := a • φ.toLinearMap
  have hψ : Function.Injective ψ := fun f g h => φ.injective (smul_right_injective _ ha h)
  have hN : ∀ σ f, normOn U x V dict Z (G + G₀) σ (ψ f) ≤ t σ * normOn U x V dict Z G σ f := by
    intro σ f
    apply le_of_eq
    have e : ((ψ f : cuspOn U Z (G + G₀)) : Rul Xo c) = a • ((f : Rul Xo c) * s.sig) := by
      simp [ψ, hφ]
    simp only [normOn]
    rw [e, petOn_smul, petOn, petOn, GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul E H Dw l Xo c r U x Z G₀ s G hG f f.2.2 σ D _ _ _]
    simp only [ht]
    ring
  have hL : 𝔞 • (latOn U Z G).map (ψ.restrictScalars (𝓞 c.F)) ≤ latOn U Z (G + G₀) := by
    rw [Submodule.smul_le]
    rintro b hb _ ⟨f, hf, rfl⟩
    by_cases hb0 : b = 0
    · rw [hb0, zero_smul]; exact zero_mem _
    · have hb' : (b : c.F) ≠ 0 := by simpa using hb0
      refine hlat ((b : c.F) * a) (mul_ne_zero hb' ha) (hint b hb hb0) f hf _ ?_
      rw [← IsScalarTower.algebraMap_smul c.F b]
      simp [ψ, mul_smul]
      rfl
  have key := GlobalTheory.T.deg_add_le_deg_of_ideal_smul_le_alt c.F _ _ (normOn U x V dict Z G) (normOn U x V dict Z (G + G₀)) ψ t (latOn U Z G)
    (latOn U Z (G + G₀)) 𝔞 hGood.1 hGood'.1 hψ ht0 htc hN hGood.2.1 hGood'.2.1 h𝔞 hL hrk
  have hlog : ∑ σ, Real.log (t σ) = ∑ σ : c.F →+* ℂ, Real.log ‖σ a‖ + ∑ σ, Real.log (s.cInf σ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => Real.log_mul (hna σ).ne' (s.cInf_pos σ).ne'
  have hdeg : s.degLo - logSum B ≤ -((∑ σ, Real.log (t σ)) / (Module.finrank ℚ c.F : ℝ)) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ c.F : ℝ) := by
    rw [hlog, add_div]
    unfold TwSec.degLo lineDeg logSum
    linarith [hsum]
  exact le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _))) key

end GlobalTheory.FlatTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupLatticeDegreeTwistLowerBoundStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_supLattice_degree_twist_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (D : D7) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E) (B : Finset ℕ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ p ∈ B, p.Prime) → IntOff B s.lo → GoodOn U x V dict Z G → degOn U x V dict Z G + (rankOn U Z G : ℝ) * (s.degLo - logSum B) ≤ degOn U x V dict Z (G + G₀) := by
  first | exact @GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le | exact GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le | (intros; apply GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergence
noncomputable section

namespace GlobalTheory.ArcQZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj _root_.Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hasSum_evR_of_chart_natural (hL : GlobalTheory.Reg.EvLaws Xo c) (σ : c.F →+* ℂ) [Algebra c.F ℂ⸨X⸩]
    (hK : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    {v : ℂ} (hv : v ≠ 0) {R : Type} [CommRing R] [Algebra c.F R] (φ : R →ₐ[c.F] ℂ⸨X⸩) (ψ : R →ₐ[c.F] CAt σ)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩)
    (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ)
    {y₀ : FrPt Xo c R} {y₁ y : FrPt Xo c ℂ⸨X⸩} {yw₁ yw : FrPt Xo c (CAt σ)}
    (h₁ : FrMap φ y₀ y₁) (hy : FrChg G s y₁ y) (hw₁ : FrMap ψ y₀ yw₁) (hyw : FrChg Gw sw yw₁ yw)
    (hφ : ∀ f, HasSum (fun n : ℤ => (φ f).coeff n * v ^ n) (toC (ψ f)))
    (hG : ∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * v ^ n) (toC (Gw τ i k)))
    (hs : HasSum (fun n : ℤ => s.coeff n * v ^ n) (toC sw))
    (hG' : ∀ τ, Summable fun n : ℤ => ((G τ).det⁻¹).coeff n * v ^ n)
    (hs' : Summable fun n : ℤ => (s⁻¹).coeff n * v ^ n) (F : Rul Xo c)
    (hF : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F) :
    HasSum (fun m : ℤ => (evR Xo c F y).coeff m * v ^ m) (toC (evR Xo c F yw)) := by
  let A := ptRing σ hK hv
  let φA : R →ₐ[c.F] A := φ.codRestrict A fun f => (hφ f).summable
  let GA : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A :=
    fun τ i k => ⟨G τ i k, (hG τ i k).summable⟩
  let sA : A := ⟨s, hs.summable⟩
  obtain ⟨hu1, hu2⟩ := (frChg_exists_unique_units E H Dw l Xo c _ G s y₁).2.2.1 y hy
  have hdet : ∀ τ, ((GA τ).det : ℂ⸨X⸩) = (G τ).det := fun τ => A.val.map_det (GA τ)
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ φA y₀
  obtain ⟨u, hu⟩ := (frChg_exists_unique_units E H Dw l Xo c A GA sA u₁).1
    (fun τ => isUnit_ptRing σ hK hv _ (by rw [hdet]; exact (hu1 τ).ne_zero) (by rw [hdet]; exact hG' τ))
    (isUnit_ptRing σ hK hv sA hu2.ne_zero hs')
  have e₁ : FrMap A.val u y := frMap_of_frChg_map φA A.val GA sA hu₁ hu h₁ hy
  have eψ : (ptEv σ hK hv).comp φA = ψ := AlgHom.ext fun f => ptEv_eq σ hK hv _ (hφ f)
  have eG : (fun τ => (GA τ).map (ptEv σ hK hv)) = Gw := by
    funext τ
    ext i k
    exact ptEv_eq σ hK hv _ (hG τ i k)
  have es : ptEv σ hK hv sA = sw := ptEv_eq σ hK hv _ hs
  have e₂ : FrMap (ptEv σ hK hv) u yw :=
    frMap_of_frChg_map φA (ptEv σ hK hv) GA sA hu₁ hu (by rw [eψ]; exact hw₁) (by rw [eG, es]; exact hyw)
  rw [GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₁, GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₂]
  exact hasSum_ptEv σ hK hv _

theorem hasSum_evR_arc_natural : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ F : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (toC (evR Xo c F yw)) := by
  intro hL1 hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th Θ z hL hK hχ hβ hP hth hy hz
  obtain ⟨pt, -, -, -, -, hpt1, hpt2, -⟩ := id hy
  have hpt3 : pt ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ⸨X⸩) := by
    rw [← cancel_mono (spMap β), Category.assoc, ← Y.jQ_over, Category.assoc, ← pullback.condition,
      ← Category.assoc Y.jQ, ← Category.assoc]
    show (pt ≫ Y.j) ≫ Y.s = _
    rw [hpt1, Category.assoc, hχ]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (hK (β x)).symm
  obtain ⟨p, j, y₀, hch, hmem⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hL1.secBaseChange E H Dw l Xo c (pt (IsLocalRing.closedPoint ℂ⸨X⸩))
  haveI := hch.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.ArcQ.exists_algHom_of_mem_range j hch.2.2 pt hpt3 hmem
  obtain ⟨y₁, hy₁⟩ := hL.bc _ _ φ y₀
  obtain ⟨G, s, hGs⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 y₁).2.2.2 y
    (by rw [hy₁.1, ← hch.2.1, ← Category.assoc, hφ, hpt2])
  obtain ⟨T₁, h₁⟩ := GlobalTheory.T.holArc_chart_coordinates_hasSum E H Dw l Xo c σ O β Y a χ W g ty Fu Ha p j φ hK hχ hβ hch.1 hch.2.2
    (by rw [← Category.assoc, hφ, hpt1])
  obtain ⟨T₂, h₂⟩ := GlobalTheory.T.frame_matrix_hasSum_alt hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th z p j y₀ φ y₁ G s
    hK hχ hβ hy hz hch hy₁ hGs
  obtain ⟨T₃, h₃⟩ := GlobalTheory.T.hasSum_thetaGenerator_chart_ratio hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th Θ p j y₀ φ y₁ G s
    hK hχ hβ hP hth hy hch hy₁ hGs
  have key : ∀ w : ℂ, max T₁ (max T₂ T₃) < w.im → ∀ yw, AnFr Ha Θ z w yw →
      ∃ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ : FrPt Xo c (CAt σ))
        (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ),
        FrMap ψ y₀ yw₁ ∧ FrChg Gw sw yw₁ yw ∧
        (∀ f, HasSum (fun n : ℤ => (φ f).coeff n * eTwoPi w ^ n) (toC (ψ f))) ∧
        (∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * eTwoPi w ^ n) (toC (Gw τ i k))) ∧
        HasSum (fun n : ℤ => s.coeff n * eTwoPi w ^ n) (toC sw) := by
    intro w hw yw hyw
    rw [max_lt_iff, max_lt_iff] at hw
    obtain ⟨ψ, hψ1, hψ2⟩ := h₁ w hw.1
    obtain ⟨yw₁, hyw₁⟩ := hL.bc _ _ ψ y₀
    obtain ⟨Gw, sw, hw'⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 yw₁).2.2.2 yw
      (by rw [hyw₁.1, ← hch.2.1, hψ1]; exact hyw.1.1)
    exact ⟨ψ, yw₁, Gw, sw, hyw₁, hw', hψ2, h₂ w hw.2.1 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1 hw',
      h₃ w hw.2.2 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1.1 hyw.2 hw'⟩
  by_cases hex : ∃ w : ℂ, max T₁ (max T₂ T₃) < w.im ∧ ∃ yw, AnFr Ha Θ z w yw
  · obtain ⟨w₀, hw₀, yw₀, hyw₀⟩ := hex
    obtain ⟨-, -, Gw₀, sw₀, -, -, -, hG₀, hs₀⟩ := key w₀ hw₀ yw₀ hyw₀
    have hv₀ := GlobalTheory.Conv.eTwoPi_ne_zero w₀
    have cs : s⁻¹ ∈ GlobalTheory.Conv.convLaurent :=
      inv_mem (GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ hs₀.summable)
    have cG : ∀ τ, (G τ).det⁻¹ ∈ GlobalTheory.Conv.convLaurent := fun τ => by
      refine inv_mem ?_
      rw [Matrix.det_apply']
      exact sum_mem fun π _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ =>
        GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ (hG₀ τ _ _).summable)
    obtain ⟨T₄, h₄⟩ := GlobalTheory.Conv.exists_forall_mem_halfRing
      (S := insert s⁻¹ (Set.range fun τ => (G τ).det⁻¹)) ((Set.finite_range _).insert _)
      (by rintro _ (rfl | ⟨τ, rfl⟩); exacts [cs, cG τ])
    refine ⟨max T₄ (max T₁ (max T₂ T₃)), fun w hw yw hyw F hF => ?_⟩
    rw [max_lt_iff] at hw
    obtain ⟨ψ, yw₁, Gw, sw, k₁, k₂, k₃, k₄, k₅⟩ := key w hw.2 yw hyw
    exact hasSum_evR_of_chart_natural hL σ hK (GlobalTheory.Conv.eTwoPi_ne_zero w) φ ψ G s Gw sw hy₁ hGs k₁ k₂ k₃ k₄ k₅
      (fun τ => h₄ _ (Or.inr ⟨τ, rfl⟩) w hw.1) (h₄ _ (Or.inl rfl) w hw.1) F hF
  · exact ⟨_, fun w hw yw hyw => absurd ⟨w, hw, yw, hyw⟩ hex⟩

end GlobalTheory.ArcQZ

namespace GlobalTheory.CuspFrom

section SecZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem evR_frChg_one_secZ {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {ex : Ix Dw → ℤ}
    (hex : ex none = 0) {F : Rul Xo c} (hF : F ∈ GlobalTheory.AllWt.secZ Xo c ex) {s : S} {y y' : FrPt Xo c S}
    (h : FrChg (fun _ => 1) s y y') : evR Xo c F y' = evR Xo c F y := by
  obtain ⟨u, rfl⟩ := ((GlobalTheory.T.frameChange_exists_unique_invertible E H Dw l Xo c S _ s y).2.2.1 y' h).2
  let t : Ix Dw → Sˣ := fun i => i.elim u fun _ => 1
  have hb : FrBor t y y' :=
    ((GlobalTheory.T.frameChange_compose_invert_baseChange_triangular E H Dw l Xo c S).2.2.2 t y y').2
      ⟨fun _ => 1, fun τ i => by simp [t], fun τ i j hij => Matrix.one_apply_ne hij.ne, h⟩
  rw [GlobalTheory.FlagTan.evR_frBor hF hb]
  simp [t, Fintype.prod_option, hex]

theorem exists_arc_secZ' [Algebra c.F ℂ⸨X⸩]
    (halg : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) :
    ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ),
      BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im →
        (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex,
          HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m)
            (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  letI := FractionRing.liftAlgebra ℂ ℂ
  haveI := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  have hK := GlobalTheory.ArcCM.known_holds
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨aC, htie⟩ := GlobalTheory.CuspFrom.exists_input Uw hσ hU hξ hx
  obtain ⟨Wp, Y, h4, hpush⟩ := GlobalTheory.CuspFrom.exists_model Xo c (by omega)
  have hmono := mono_spMap_subtype (c.V Wp)
  obtain ⟨χ, hχ, -⟩ := h4 ℂ _ 1 (aC.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField ℂ, rfl⟩)
  obtain ⟨hover, hab, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ _).1 hW
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ Y σ _ χ W Uw.g _ Uw.F hσ hty (GlobalTheory.ArcInTest.exists_values c Wp) hover
    (fun q hq => hj q (by simpa using hq))
  obtain ⟨T, s, d, z, hd, hz, hflow⟩ := htie _ _ Y χ W Ha
  obtain ⟨-, v₂, -, -⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c _ _ _ Y _ _ W _ _ Uw.F Ha
  choose e he using fun τ i => (v₂ (z τ i)).exists
  have hB := GlobalTheory.T.constant_vectors_lieBasis_of_complex_arc E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha e z hσ hz he
  obtain ⟨-, -, th, hth⟩ := GlobalTheory.ThetaOverField.nonzero_generates h1 h2 ℂ (aC.restrict (c.V Wp).subtype).D₀
    DVR.SecOps.secZero
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha hty th hth
  have hc : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ≫ Y.s = spMap (algebraMap c.F ℂ⸨X⸩) ≫ spMap (c.V Wp).subtype := by
    rw [Category.assoc, hover, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp]
    congr 1
    exact RingHom.ext fun t => (halg _).symm
  haveI := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ hc : Sp ℂ⸨X⸩ ⟶ gen Y) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]
    intro hq
    have h0 : HahnSeries.ofPowerSeries ℤ ℂ PowerSeries.X ∈ q.asIdeal := hq
    rw [@Ideal.eq_bot_of_prime _ _ q.asIdeal q.isPrime, Ideal.mem_bot] at h0
    exact PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm))
  let z₀ := IsOpenImmersion.lift Y.jQ _ hr
  have hz₀ : z₀ ≫ Y.jQ = _ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨y, -, hy⟩ := GlobalTheory.ArcQ.exists_isArcFr h1 h2 E H Dw l Xo c _ _ Y ℂ _ _ χ W _ e th hB hth (Or.inr hpush) ℂ⸨X⸩
    (HahnSeries.ofPowerSeries ℤ ℂ) z₀ (by unfold RingHom.Flat; infer_instance)
    (by rw [Model.j, ← Category.assoc, hz₀, pullback.lift_fst])
    (by
      rw [pullback.condition, ← Category.assoc, ← Y.jQ_over, ← Category.assoc, hz₀, pullback.lift_snd,
        GlobalTheory.ArcId.sp_comp]
      rfl)
    (fun τ t => halg _)
  have hbd := GlobalTheory.T.arc_framed_point_extends_to_model_boundary E H Dw l Xo c σ _ _ Y _ χ W e th y halg hover hmono hB hy (fun h =>
    (hab _).1 h (by
      change _ ∈ IsLocalRing.maximalIdeal _
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.mem_span_singleton_self _))
  obtain ⟨T', hT'⟩ := GlobalTheory.ArcQZ.hasSum_evR_arc_natural h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha y e th Θ z hev halg hover
    hmono hpush hth hy he
  refine ⟨y, max T (max T' Ha.T), s, d, GlobalTheory.T.boundaryExtension_independent_of_model E H Dw l Xo c _ _ Z _ _ Y _ _ _ y
    (RingHom.ext fun t => (halg t).symm) hbd, hd, fun w hw => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨hxw, hlie⟩ := hflow w hw.1
  refine ⟨hxw, fun ex hex0 F hF => ?_⟩
  obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr h1 h2 E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha th Θ z hσ hz w
    hw.2.2
  obtain ⟨t, ht⟩ := GlobalTheory.ArcCoeff.frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw.2.2) _ _ z hlie hyw.1
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have e1 := evR_frChg_one_secZ hex0 hF ht
  have := hT' w hw.2.1 yw hyw F hF.1
  rw [e1] at this
  convert this using 1
  exact dif_pos hxw

end SecZ

end GlobalTheory.CuspFrom

section Final

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

theorem GlobalTheory.CuspFrom.exists_arc_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) [Algebra c.F ℂ⸨X⸩], (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (ξ' : Fin r → E), (U.X k).IsIso ξ' → ∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r, x ∈ (U.X k).dom → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ), GlobalTheory.CuspFrom.BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im → (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex, HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  intro E _ _ _ H Dw l Xo c σ r U _ halg hσ hU k ξ' hξ x hx O _ β Z
  exact GlobalTheory.CuspFrom.exists_arc_secZ' halg hσ hU hξ hx Z

end Final
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergenceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentArc_degenerating_on_model_convergence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) [Algebra c.F ℂ⸨X⸩], (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (ξ' : Fin r → E), (U.X k).IsIso ξ' → ∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r, x ∈ (U.X k).dom → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ), GlobalTheory.CuspFrom.BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im → (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex, HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  first | exact @GlobalTheory.CuspFrom.exists_arc_secZ | exact GlobalTheory.CuspFrom.exists_arc_secZ | (intros; apply GlobalTheory.CuspFrom.exists_arc_secZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddStrictLowerMemClosureTransvection
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory

theorem one_add_strictLower_mem_closure_transvection (R : Type) [CommRing R] (N : ℕ)
    (c : Matrix (Fin N) (Fin N) R) (hc : ∀ a b, a ≤ b → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  have key : ∀ S : Finset (Fin N × Fin N), ∀ c : Matrix (Fin N) (Fin N) R,
      (∀ a b, a ≤ b → c a b = 0) → (∀ a b, (a, b) ∉ S → c a b = 0) →
      1 + c ∈ Submonoid.closure
        {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
    intro S
    induction S using Finset.induction_on_max_value (fun p : Fin N × Fin N => p.2) with
    | empty =>
      intro c _ h
      have : c = 0 := by
        ext a b
        simpa using h a b (by simp)
      rw [this, add_zero]
      exact Submonoid.one_mem _
    | insert p S hp hmax ih =>
      intro c hc hS
      obtain ⟨a, b⟩ := p
      by_cases hab : a ≤ b
      · refine ih c hc fun i j hij => ?_
        by_cases h : (i, j) = (a, b)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact hc _ _ hab
        · exact hS i j (by simp only [Finset.mem_insert, not_or]; exact ⟨h, hij⟩)
      · have hba : b < a := lt_of_not_ge hab
        set c' : Matrix (Fin N) (Fin N) R := c - Matrix.single a b (c a b) with hc'
        have h2 : ∀ i j, (i, j) ∉ S → c' i j = 0 := by
          intro i j hij
          by_cases h : (i, j) = (a, b)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            simp [hc']
          · have h0 : c i j = 0 :=
              hS i j (by simp only [Finset.mem_insert, not_or]; exact ⟨h, hij⟩)
            have h' : ¬ (a = i ∧ b = j) := by
              rintro ⟨rfl, rfl⟩; exact h rfl
            simp [hc', h0, Matrix.single_apply, h']
        have h1 : ∀ i j, i ≤ j → c' i j = 0 := by
          intro i j hij
          have h' : ¬ (a = i ∧ b = j) := by
            rintro ⟨rfl, rfl⟩; exact hab hij
          simp [hc', hc i j hij, Matrix.single_apply, h']
        have h3 : c' * Matrix.single a b (c a b) = 0 := by
          ext i j
          have hz : c' i a = 0 := by
            apply h2
            intro hmem
            exact absurd (hmax _ hmem) (not_le.mpr hba)
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun e _ => ?_
          by_cases he : a = e
          · subst he; simp [hz]
          · simp [Matrix.single_apply, he]
        have h4 : 1 + c = (1 + c') * Matrix.transvection a b (c a b) := by
          rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, h3, add_zero, hc']
          abel
        rw [h4]
        exact Submonoid.mul_mem _ (ih c' h1 h2)
          (Submonoid.subset_closure ⟨a, b, _, hba.ne', rfl⟩)
  exact key Finset.univ c hc (by simp)

end GlobalTheory
end
