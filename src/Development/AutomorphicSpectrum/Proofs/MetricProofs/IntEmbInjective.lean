module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricVectorLogResolution

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

section Pure

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

abbrev Sg (j j' : ℕ) : Type := Fin j ⊕ Fin j'

def sgI (j j' : ℕ) : Matrix (Sg j j') (Sg j j') ℂ := fromBlocks 1 0 0 (-1)

def IsSgU (u : Matrix (Sg j j') (Sg j j') ℂ) : Prop := uᴴ * sgI j j' * u = sgI j j'

def moebW (u : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ) : Matrix (Fin j') (Fin j) ℂ :=
  (u.toBlocks₂₁ + u.toBlocks₂₂ * W) * (u.toBlocks₁₁ + u.toBlocks₁₂ * W)⁻¹

def ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) : Fin n → ℂ :=
  fun k => W (q.symm k).1 (q.symm k).2.2 (q.symm k).2.1

def moebBall (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) : Fin n → ℂ :=
  ballPt q fun τ => moebW (u τ) (ballMat q t τ)ᵀ

end Pure

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]


omit [IsCMField E] in
theorem intEmb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def embOf (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (intEmb_injective s)

structure LatEmb (F : UnivFam E Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  xi : E

  c : ℝ
  c_pos : 0 < c

  eps : Ψ → ℝ
  eps_sq : ∀ τ, eps τ ^ 2 = 1
  xi_eq : ∀ τ, embOf (F.σ τ) xi = Complex.I * ((c * eps τ : ℝ) : ℂ)
  form_eq : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (xi * h.toSesq (e y) (e x))

  lam : Module.Basis (Fin (2 * g)) ℤ Λ

  bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin (j + j') → ℂ)
  bas_eq : ∀ k τ i, bas k τ i = embOf (F.σ τ) (e (lam k) i)

def plc (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) : InfinitePlace E := InfinitePlace.mk (embOf (F.σ τ))


open Classical in
def tauMat (F : UnivFam E Ψ j j' n g Λ) (a : InfinitePlace E → GL (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  if (plc F τ).embedding = embOf (F.σ τ) then (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)
  else (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map (starRingEnd ℂ)

namespace LatEmb

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

def vec (x : Λ) : Ψ → Fin (j + j') → ℂ := fun τ i => embOf (F.σ τ) (C.e x i)

def gr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  (gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))

def sgr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ := ((C.eps τ : ℝ) : ℂ) • C.gr τ

def Fm (y y' : Ψ → Fin (j + j') → ℂ) : ℝ :=
  ∑ τ, 2 * (embOf (F.σ τ) C.xi * (star (y' τ) ⬝ᵥ (C.gr τ *ᵥ y τ))).re

def cinv (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) : Matrix (Sg j j') (Fin (j + j')) ℂ :=
  sgI j j' * Aᴴ * C.sgr τ

def perExt (R : RiemLat E g Λ) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  C.bas.constr ℝ fun k => R.P (C.lam k)


open Classical in
def pPart (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) - Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))


open Classical in
def pBar (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) + Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))

structure IsAdapted (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) : Prop where
  unit : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j'
  ker : ∀ τ (v : Fin j → ℂ), C.pPart R τ (A τ *ᵥ Sum.elim v 0) = 0
  kerBar : ∀ τ (v : Fin j' → ℂ), C.pBar R τ (A τ *ᵥ Sum.elim 0 v) = 0

abbrev Arch : Subgroup (InfinitePlace E → GL (Fin (j + j')) ℂ) := archUnitary C.h (Pi.basisFun E (Fin (j + j')))

def tm (a : C.Arch) (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  tauMat F (a : InfinitePlace E → GL (Fin (j + j')) ℂ) τ

end LatEmb

end Arch

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

def tz {I : Type} [Fintype I] (Z : Matrix I I ℂ) (z : I → ℂ) : I → ℂ := z - Z *ᵥ star z

abbrev Ix (Ψ : Type) (j j' : ℕ) : Type := (Fin j' ⊕ Fin j) × Ψ

def emb {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (i : Ix Ψ j j') : 𝓞 E →+* ℂ :=
  Sum.elim (fun _ => σ i.2) (fun _ => (starRingEnd ℂ).comp (σ i.2)) i.1

def bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ :=
  blockDiagonal fun τ => fromBlocks 0 (ballMat q t τ)ᵀ (ballMat q t τ) 0

def bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (t : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (bigZ q t).submatrix e.symm e.symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariables
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariables
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem maDensity_const_eq_normSq_jacobian_mul :
    ∀ (n : ℕ) (φ ψ : (Fin n → ℂ) → ℝ) (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ)
      (t : Fin n → ℂ), AnalyticAt ℂ A t → AnalyticAt ℂ G t → ContDiffAt ℝ 2 φ (A t) →
      (∀ᶠ t' in 𝓝 t, ψ t' = φ (A t') + (G t').re) →
      maDensity (fun (_ : Fin n) => ψ) t =
        ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * maDensity (fun (_ : Fin n) => φ) (A t) := by
  intro n φ ψ A G t hA hG hφ hψ
  have h := GroundTheory.Heights₂.Heights.ChartEnergySwapHessian.maDensity_comp_holo
    (fun (_ : Fin n) => ψ) (fun (_ : Fin n) => φ) A G t (fun _ => hφ) hA.contDiffAt hG.contDiffAt
    (fun _ => hψ)
  rw [h, LinearMap.det_toMatrix', Complex.normSq_eq_norm_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariablesStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_density_change_of_variables : ∀ (n : ℕ) (φ ψ : (Fin n → ℂ) → ℝ) (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ) (t : Fin n → ℂ), AnalyticAt ℂ A t → AnalyticAt ℂ G t → ContDiffAt ℝ 2 φ (A t) → (∀ᶠ t' in 𝓝 t, ψ t' = φ (A t') + (G t').re) → maDensity (fun (_ : Fin n) => ψ) t = ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * maDensity (fun (_ : Fin n) => φ) (A t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.maDensity_const_eq_normSq_jacobian_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriod
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriod
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ}

def diagAct (ty : Fin g → (E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
  (Algebra.lmul ℂ (Fin g → ℂ)).toRingHom.comp (Pi.ringHom fun i => (ty i).comp (algebraMap (𝓞 E) E))

theorem diagAct_apply (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (i : Fin g) :
    diagAct ty a x i = ty i (a : E) * x i := rfl

theorem embedding_eq_of_integers {s t : E →+* ℂ} (h : ∀ a : 𝓞 E, s (a : E) = t (a : E)) : s = t :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem mem_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) (x : Fin g → ℂ) :
    x ∈ eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ↔ ∀ i, ty i ≠ s → x i = 0 := by
  have key : ∀ (a : 𝓞 E) (i : Fin g),
      ((diagAct ty a - (s.comp (algebraMap (𝓞 E) E)) a • LinearMap.id : Module.End ℂ (Fin g → ℂ)) x) i = (ty i (a : E) - s (a : E)) * x i := by
    intro a i
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      diagAct_apply, RingHom.comp_apply]
    ring_nf
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i hi
    by_contra hx
    refine hi (embedding_eq_of_integers fun a => ?_)
    have h1 := congrFun (h a) i
    rw [key] at h1
    simpa [hx, sub_eq_zero] using h1
  · intro h a
    funext i
    rw [key]
    by_cases hi : ty i = s
    · simp [hi]
    · simp [h i hi]

def eigSpDiagEquiv (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E)) ≃ₗ[ℂ] ({i // ty i = s} → ℂ) where
  toFun x j := x.1 j.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun i => open Classical in if h : ty i = s then f ⟨i, h⟩ else 0,
    (mem_eigSp_diagAct ty s _).2 fun i hi => by simp [hi]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    by_cases h : ty i = s
    · simp [h]
    · simp [h, (mem_eigSp_diagAct ty s x.1).1 x.2 i h]
  right_inv f := by
    funext j
    simp [j.2]

theorem finrank_eigSp_diagAct (ty : Fin g → (E →+* ℂ)) (s : E →+* ℂ) :
    Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = Nat.card {i // ty i = s} := by
  classical
  rw [(eigSpDiagEquiv ty s).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Diag

theorem free_of_period {Λ : Type} [AddCommGroup Λ] {g : ℕ} (P : Λ →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Free ℤ Λ ∧ Module.Finite ℤ Λ ∧ Module.finrank ℤ Λ = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    have : ((L : Set (Fin g → ℂ))) = Set.range P := by
      ext x; simp [L]
    rw [this, hs]⟩
  let e : Λ ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem riemLat_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P → ∃ R : RiemLat E g D.La, R.P = P ∧ R.form = D.EF ∧ (∀ a x i, R.B a x i = ty i (a : E) * x i) ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q := by
  intro E _ _ _ H D g ty P hty hP
  obtain ⟨hact, hinj, hdisc, hspan, Hm, hherm, hpos, him⟩ := hP
  obtain ⟨hfree, hfin, hrank⟩ := free_of_period P hinj hdisc hspan
  refine ⟨{ free := hfree, fin := hfin, rank := hrank, form := D.EF, alt := D.alt, unimod := D.unimod
            adj := ?_, P := P, Hm := Hm, herm := hherm, pos := hpos, im := him, B := diagAct ty, act := ?_ },
    rfl, rfl, fun a x i => diagAct_apply ty a x i, fun s => ?_⟩
  · intro a a' h x y
    have : a' = H.bar a := by
      apply RingOfIntegers.ext
      rw [H.bar_eq a]
      exact h
    rw [this]
    exact D.adj a x y
  · intro a x
    funext i
    exact hact a x i
  · show Module.finrank ℂ (eigSp (diagAct ty) (s.comp (algebraMap (𝓞 E) E))) = _
    rw [finrank_eigSp_diagAct]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h]
      exact (hty s).1 h
    · rw [if_neg h]
      exact (hty s).2 h

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRiemannLatticeOfPeriodStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_riemann_lattice_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P → ∃ R : RiemLat E g D.La, R.P = P ∧ R.form = D.EF ∧ (∀ a x i, R.B a x i = ty i (a : E) * x i) ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_of_period | exact GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_of_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_of_period <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticBadLocusNull
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPoints
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensR

variable {K : Type} {ι : K → Type}

theorem orbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [hc p.1]

theorem orbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem orbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem analytic_minorIJ {m N : ℕ} {V : Set (Fin m → ℂ)} {h : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ r s, AnalyticOnNhd ℂ (fun u => h u r s) V) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun u => minorIJ (h u) I J) V := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply', Matrix.submatrix_apply]
    refine Finset.analyticOnNhd_fun_sum _ fun σ _ => ?_
    exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ => hh _ _)
  · simp only [dif_neg e]
    exact analyticOnNhd_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensR

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC


open DensR in
theorem dens_r : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x : FA.Re.R.X), FA.pr (FA.Re.π x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (FA.Re.π x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x'))) (FA.Re.R.lift x' x') p ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x hx V hV hxV
  have hlift : FA.Re.R.lift x x ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x x (FA.Re.R.mem_U x)
  obtain ⟨h₀, hh₀, hso₀⟩ := GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l (FA.pr (FA.Re.π x)) hx _ hlift (FA.pr_eq x)
  have hgood := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l
  have han : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X)
      (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ), IsOpen V → ContinuousOn bp V →
      (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) →
      (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) →
      (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) →
      ∀ q, AnalyticOnNhd ℂ (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) q) V := by
    intro m V bp hh hV hc ha hm hhan _ q
    have hval := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l m V bp hV hc ha hm
    by_cases hk : ∀ p, M.blk p ≠ some q.1
    · simp only [FC.flagPt, dif_pos hk]
      exact hval.1 _
    · simp only [FC.flagPt, dif_neg hk]
      refine Finset.analyticOnNhd_fun_sum _ fun I _ => ?_
      refine (hval.2 _ fun b hb => ((hgood b hb).2.1.2.1 q I).1).mul ?_
      exact analytic_minorIJ (fun r s => hhan _ r s) _ _
  obtain ⟨x', hx'V, b', hb', h', hh', hso', hmin⟩ :=
    GlobalTheory.T.base_metric_vector_log_resolution K ι Φ y Ψ N j M n BM K ι (mCoordIdeal y) FA.Re.J (d + 1) FA.Re.R FA.J_top l
      (fun b h => FC.flagPt M (BM.F l) (FC.bvec BM l b) h) (fun _ => 1)
      (fun _ => ⟨fun a => by simp, fun a b hab => Matrix.one_apply_ne hab.ne⟩) han
      (fun b hb h hh => GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l b hb h hh)
      x _ hx h₀ hh₀ hso₀ V hV hxV
  have hg' := hgood b' hb'.1
  have hpr : FA.pr (FA.Re.π x') = b' := by
    refine BM.Rb.inj _ _ (fun hc => by simpa using hc.2 1 Submodule.mem_top) ?_
    refine orbit_trans (orbit_symm (FA.pr_eq x')) (orbit_trans (orbit_basePart M.blk hso') ?_)
    rw [FC.basePart_flagPt]
    exact hg'.2.2.2
  refine ⟨x', hx'V, hpr ▸ hb', fun p => ?_⟩
  rw [hpr]
  rw [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hso']
  cases hp : M.blk p with
  | none => simp [FC.plk, hp]
  | some k =>
    have hprop : IsProperStep N j p.2 := by
      by_contra hc
      have := (M.blk_none p).2 hc
      simp [hp] at this
    rw [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h' p k (BM.isFrame l) hg'.1 hg'.2.1
      (fun τ' => (hh' τ').1) hp]
    exact (hmin p.1 p.2 hprop).1

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPointsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_dense_good_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x : FA.Re.R.X), FA.pr (FA.Re.π x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (FA.Re.π x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x'))) (FA.Re.R.lift x' x') p ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_r <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticBadLocusNull
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem null_off_bigCell_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q), IsNull FA.Re.R.A {x | FA.pr (FA.Re.π x) ∈ BM.O l ∧ (FA.pr (FA.Re.π x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x))) (FA.Re.R.lift x x) p = 0)} := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l
  exact GlobalTheory.T.base_metric_pullback_family K ι Φ y Ψ N j M n BM _ FA.Re.R.X FA.Re.R.A FA.Re.R.U FA.Re.R.lift
    (FA.pr ∘ FA.Re.π) l (Pr.holoMap_comp' FA.Re.holo FA.pr_holo) (fun x => FA.Re.R.isOpen_U x)
    (fun x => FA.Re.R.mem_U x) (fun x p => FA.Re.R.holo x p)
    (fun x y' hy => FA.Re.R.compat x y' y' ⟨hy, FA.Re.R.mem_U y'⟩)
    (fun x hx V hV hxV => GlobalTheory.T.flag_analytic_dense_good_points K ι Φ y Ψ N j M n d BM FA l x hx V hV hxV)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticBadLocusNullStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_bad_locus_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q), IsNull FA.Re.R.A {x | FA.pr (FA.Re.π x) ∈ BM.O l ∧ (FA.pr (FA.Re.π x) ∈ bdry BM.s ∨ ∃ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x))) (FA.Re.R.lift x x) p = 0)} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_off_bigCell_resolution | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_off_bigCell_resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.null_off_bigCell_resolution <;> assumption)
end
end
