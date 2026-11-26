module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import GroundTheory.GlobalFields.Artin.LogCharpoly
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
namespace GlobalTheory

open Cardinal

theorem cardinalMk_padic_eq_continuum (l : ℕ) [Fact l.Prime] : #ℚ_[l] = 𝔠 := by
  apply le_antisymm
  · have hd := Padic.denseRange_ratCast l
    have h : ∀ x : ℚ_[l], ∃ u : ℕ → ℚ,
        Filter.Tendsto (fun n => (u n : ℚ_[l])) Filter.atTop (nhds x) := by
      intro x
      obtain ⟨v, hv, hx⟩ := mem_closure_iff_seq_limit.1 (hd x)
      choose u hu using hv
      exact ⟨u, by simpa only [hu] using hx⟩
    choose u hu using h
    have hi : Function.Injective u := fun x y hxy =>
      tendsto_nhds_unique (hu x) (hxy ▸ hu y)
    refine (Cardinal.mk_le_of_injective hi).trans ?_
    simp
  · exact continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]

theorem cardinalMk_padicAlgCl_eq_continuum (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  apply le_antisymm
  · exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
      (max_le (cardinalMk_padic_eq_continuum l).le Cardinal.aleph0_le_continuum)
  · rw [← cardinalMk_padic_eq_continuum l]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective

theorem nonempty_padicAlgCl_ringEquiv_complex (l : ℕ) [Fact l.Prime] :
    Nonempty (PadicAlgCl l ≃+* ℂ) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinalMk_padicAlgCl_eq_continuum]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [cardinalMk_padicAlgCl_eq_continuum, Cardinal.mk_complex]))

theorem exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [Countable K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, ∀ x, e (a x) = b x := by
  obtain ⟨e₀⟩ := nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨σ, hσ⟩ := GaloisDescent.exists_complex_ringEquiv_comp_eq (e₀.toRingHom.comp a) b
  exact ⟨e₀.trans σ, fun x => hσ x⟩

theorem exists_padicAlgCl_ringEquiv_complex_comp_eq (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [NumberField K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, (e : PadicAlgCl l →+* ℂ).comp a = b := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨e, he⟩ := exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable l K a b
  exact ⟨e, RingHom.ext he⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
open NumberField IsDedekindDomain

namespace GlobalTheory

noncomputable def unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) : A →* Circle where
  toFun y := ⟨(a y : ℂ), by simpa [Submonoid.unitSphere] using ha y⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    exact (congrArg (fun u : ℂˣ => (u : ℂ)) (map_mul a x y)).trans (Units.val_mul _ _)

theorem toUnits_unitaryCharToCircle {A : Type} [CommGroup A] (a : A →* ℂˣ)
    (ha : ∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) (y : A) :
    Circle.toUnits (unitaryCharToCircle a ha y) = a y := by
  ext
  rfl

private lemma continuous_toUnits_comp {X : Type} [TopologicalSpace X] {f : X → Circle}
    (hf : Continuous f) : Continuous fun x => Circle.toUnits (f x) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val.comp hf, ?_⟩
  have h : (fun x => (((Circle.toUnits (f x))⁻¹ : ℂˣ) : ℂ)) = fun x => (((f x)⁻¹ : Circle) : ℂ) := by
    funext x
    simp
  rw [h]
  exact continuous_subtype_val.comp hf.inv

theorem exists_unitary_char_of_open_subgroup_and_hom :
    ∀ (G A : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A] (U : Subgroup G), IsOpen (U : Set G) → ∀ (α : A →* G) (a : A →* ℂˣ) (ψ : G →* ℂˣ), Continuous ψ → (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) → (∀ y, ‖((a y : ℂˣ) : ℂ)‖ = 1) → (∀ y, α y ∈ U → a y = ψ (α y)) → ∃ χ : G →* ℂˣ, Continuous χ ∧ (∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ x ∈ U, χ x = ψ x) ∧ ∀ y, χ (α y) = a y := by
  intro G A _ _ _ _ U hU α a ψ hψc hψ ha hagree
  let _ : TopologicalSpace A := ⊥
  have _ : DiscreteTopology A := ⟨rfl⟩

  set ψ₁ : G →* Circle := unitaryCharToCircle ψ hψ
  set a₁ : A →* Circle := unitaryCharToCircle a ha
  have hψ₁c : Continuous ψ₁ := Continuous.subtype_mk (Units.continuous_val.comp hψc) _
  have hψ₁coe : ∀ x, ((ψ₁ x : Circle) : ℂ) = (ψ x : ℂ) := fun x => rfl
  have ha₁coe : ∀ y, ((a₁ y : Circle) : ℂ) = (a y : ℂ) := fun y => rfl

  let H : Subgroup (G × A) := U.prod ⊤
  have hH : IsOpen (H : Set (G × A)) := by
    simpa [H, Subgroup.coe_prod] using hU.prod isOpen_univ
  let N : Subgroup (G × A) := (MonoidHom.prod α (MonoidHom.id A)).range
  let φ : H →* Circle :=
    ((ψ₁.comp (MonoidHom.fst G A)) / (a₁.comp (MonoidHom.snd G A))).comp H.subtype
  have hφ : ∀ x : H, φ x = ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := fun x => rfl
  have hφc : Continuous φ := by
    have h1 : Continuous fun x : H => ψ₁ (x : G × A).1 :=
      hψ₁c.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : H => a₁ (x : G × A).2 :=
      continuous_of_discreteTopology.comp (continuous_snd.comp continuous_subtype_val)
    have hfun : (φ : H → Circle) = fun x : H => ψ₁ (x : G × A).1 / a₁ (x : G × A).2 := funext hφ
    rw [hfun]
    exact h1.div' h2

  have htriv : ∀ x : H, (x : G × A) ∈ N → φ x = 1 := by
    rintro ⟨x, hxH⟩ ⟨y, rfl⟩
    have hyU : α y ∈ U := (Subgroup.mem_prod.1 hxH).1
    change ψ₁ (α y) / a₁ y = 1
    rw [div_eq_one]
    apply Circle.ext
    rw [hψ₁coe, ha₁coe, hagree y hyU]
  obtain ⟨χ₂, hχ₂c, hχ₂N, hχ₂H⟩ :=
    exists_continuous_circle_char_extension (G × A) H N φ hH hφc htriv

  refine ⟨Circle.toUnits.comp (χ₂.comp (MonoidHom.inl G A)), ?_, ?_, ?_, ?_⟩
  · exact continuous_toUnits_comp (hχ₂c.comp (continuous_id.prodMk continuous_const))
  · intro x
    exact Circle.norm_coe _
  · intro x hx
    have hxH : ((x, 1) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨hx, Subgroup.mem_top 1⟩
    have h : χ₂ (x, 1) = ψ₁ x / a₁ 1 := hχ₂H ⟨(x, 1), hxH⟩
    change Circle.toUnits (χ₂ (x, 1)) = ψ x
    rw [h, map_one, div_one]
    exact toUnits_unitaryCharToCircle ψ hψ x
  · intro y
    have hN : ((α y, y) : G × A) ∈ N := ⟨y, rfl⟩
    have h0 : χ₂ (α y, y) = 1 := hχ₂N _ hN
    have hyH : ((1, y) : G × A) ∈ H := Subgroup.mem_prod.2 ⟨U.one_mem, Subgroup.mem_top y⟩
    have h1 : χ₂ (1, y) = ψ₁ 1 / a₁ y := hχ₂H ⟨(1, y), hyH⟩
    have hsplit : ((α y, y) : G × A) = (α y, 1) * (1, y) :=
      Prod.ext (mul_one _).symm (one_mul _).symm
    rw [hsplit, map_mul, h1, map_one, one_div, mul_inv_eq_one] at h0
    change Circle.toUnits (χ₂ (α y, 1)) = a y
    rw [h0]
    exact toUnits_unitaryCharToCircle a ha y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped ContDiff Real

namespace GlobalTheory.Mem.Lift

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def dH (ρ : V → B →L[ℂ] B) (v : V) (f : B) : B := fderiv ℝ (fun u => ρ u f) 0 v

def quad (ρ : V → B →L[ℂ] B) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) (f : B) : B :=
  ∑ i, c i • dH ρ (p i) (dH ρ (q i) f)

def IsQuadOf (om : V → V → ℝ) (X : V → V) {κ : Type} [Fintype κ] (c : κ → ℂ) (p q : κ → V) : Prop :=
  ∀ (l : V →ₗ[ℝ] ℂ) (v : V),
    2 * π * I * ∑ i, c i * ((om (q i) v : ℂ) * l (p i) + (om (p i) v : ℂ) * l (q i)) = l (X v)

theorem _root_.GlobalTheory.Mem.Lift.dH_add_left (ρ : V → B →L[ℂ] B) (u v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (u + v) f =
      _root_.GlobalTheory.Mem.Lift.dH ρ u f + _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_add _ _ _

theorem _root_.GlobalTheory.Mem.Lift.dH_smul_left (ρ : V → B →L[ℂ] B) (r : ℝ) (v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (r • v) f = r • _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_smul _ _ _

theorem _root_.GlobalTheory.Mem.Lift.dH_add {ρ : V → B →L[ℂ] B} (v : V) {f g : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) (hg : _root_.GlobalTheory.RealWeil.Sm ρ g) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (f + g) =
      _root_.GlobalTheory.Mem.Lift.dH ρ v f + _root_.GlobalTheory.Mem.Lift.dH ρ v g := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hg' : DifferentiableAt ℝ (fun u => ρ u g) 0 :=
    (ContDiff.differentiable hg (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_add (f := _)]
  rw [(hf'.hasFDerivAt.fun_add hg'.hasFDerivAt).fderiv]
  rfl

theorem _root_.GlobalTheory.Mem.Lift.dH_smul {ρ : V → B →L[ℂ] B} (v : V) (a : ℂ) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.Mem.Lift.dH ρ v (a • f) = a • _root_.GlobalTheory.Mem.Lift.dH ρ v f := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  unfold _root_.GlobalTheory.Mem.Lift.dH
  simp only [map_smul]
  rw [(hf'.hasFDerivAt.fun_const_smul a).fderiv]
  rfl

theorem _root_.GlobalTheory.Mem.Lift.hasDerivAt_dH {ρ : V → B →L[ℂ] B} (v : V) {f : B}
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (_root_.GlobalTheory.Mem.Lift.dH ρ v f) 0 := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact hf'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem _root_.GlobalTheory.Mem.Lift.dH_comm {ρ : V → B →L[ℂ] B} (A : B →L[ℂ] B)
    (hA : ∀ v f, A (ρ v f) = ρ v (A f)) {f : B} (hf : _root_.GlobalTheory.RealWeil.Sm ρ f) :
    _root_.GlobalTheory.RealWeil.Sm ρ (A f) ∧
      ∀ v, _root_.GlobalTheory.Mem.Lift.dH ρ v (A f) = A (_root_.GlobalTheory.Mem.Lift.dH ρ v f) := by
  have hf' : DifferentiableAt ℝ (fun u => ρ u f) 0 :=
    (ContDiff.differentiable hf (by simp)).differentiableAt
  have hfun : (fun u => ρ u (A f)) = fun u => (A.restrictScalars ℝ) (ρ u f) := by
    funext u
    simp [hA]
  refine ⟨?_, fun v => ?_⟩
  · unfold _root_.GlobalTheory.RealWeil.Sm
    rw [hfun]
    exact (A.restrictScalars ℝ).contDiff.comp hf
  · unfold _root_.GlobalTheory.Mem.Lift.dH
    have h : HasFDerivAt (fun u => (A.restrictScalars ℝ) (ρ u f))
        ((A.restrictScalars ℝ).comp (fderiv ℝ (fun u => ρ u f) 0)) 0 :=
      (A.restrictScalars ℝ).hasFDerivAt.comp (0 : V) hf'.hasFDerivAt
    rw [hfun, h.fderiv]
    rfl

def smS (ρ : V → B →L[ℂ] B) : Submodule ℂ B where
  carrier := {f | Sm ρ f}
  add_mem' := fun hf hg => by simpa only [Set.mem_setOf_eq, Sm, map_add (f := _)] using ContDiff.add (show ContDiff ℝ ∞ _ from hf) (show ContDiff ℝ ∞ _ from hg)
  zero_mem' := by simpa only [Set.mem_setOf_eq, Sm, map_zero] using contDiff_const
  smul_mem' := fun a _ hf => by simpa only [Set.mem_setOf_eq, Sm, map_smul] using ContDiff.const_smul a (show ContDiff ℝ ∞ _ from hf)

end General

section Coord

variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

def xOp (ρ : (ι → ℂ) → B →L[ℂ] B) (k : ι) (f : B) : B :=
  dH ρ (Pi.single k 1) f - I • dH ρ (I • Pi.single k 1) f

def dOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (l : ι) (f : B) : B :=
  (-(1 / (4 * π)) : ℂ) • (dH ρ (H⁻¹ *ᵥ Pi.single l 1) f + I • dH ρ (I • H⁻¹ *ᵥ Pi.single l 1) f)

def nOp (ρ : (ι → ℂ) → B →L[ℂ] B) (H X : Matrix ι ι ℂ) (f : B) : B := ∑ k, ∑ l, X k l • xOp ρ k (dOp ρ H l f)

end Coord

def IsCCR {A : Type} [Ring A] {κ : Type} [DecidableEq κ] (x d : κ → A) : Prop :=
  (∀ k l, x k * x l = x l * x k) ∧ (∀ k l, d k * d l = d l * d k) ∧
    ∀ k l, d l * x k - x k * d l = if k = l then 1 else 0

end GlobalTheory.Mem.Lift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeig
namespace GlobalTheory

theorem localizationAtPrime_isDiscreteValuationRing_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  intro A _ _ _ _ q _ hq
  exact isDiscreteValuationRing_of_height_eq_one q hq (Localization.AtPrime q)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
namespace GlobalTheory

theorem matrix_exists_left_inverse_of_field {K : Type} [Field K] {m n : ℕ}
    (Q : Matrix (Fin m) (Fin n) K) (h : Function.Injective Q.mulVec) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q' * Q = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' Q) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.CharpolyDvd

theorem matrix_charpoly_dvd_pow {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  classical
  by_cases h0 : G = 0
  · subst h0
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · have : M.charpoly = 1 := by
        apply Polynomial.eq_one_of_monic_natDegree_zero M.charpoly_monic
        rw [Matrix.charpoly_natDegree_eq_dim, h]
      rw [this, h, pow_zero]
    · rw [zero_pow h.ne']
      exact dvd_zero _
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f, Polynomial.map_pow, ← Matrix.charpoly_map]
  set N := M.map f with hNdef
  have hN : aeval N (G.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := ι) (Algebra.ofId K Ω)) hG
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  have hG0 : G.map f ≠ 0 := Polynomial.map_ne_zero h0
  have hq0 : G.map f ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hG0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots N.charpoly_monic.ne_zero ?_
  rw [roots_pow, Multiset.le_iff_count]
  intro μ
  rw [Multiset.count_nsmul]
  by_cases hμ : μ ∈ N.charpoly.roots
  · have h1 : μ ∈ spectrum Ω N := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact isRoot_of_mem_roots hμ
    have h2 := spectrum.subset_polynomial_aeval N (G.map f) ⟨μ, h1, rfl⟩
    rw [hN] at h2
    have h3 : (G.map f).eval μ = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 h2)
        (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix ι ι Ω)))
    have h4 : 1 ≤ (G.map f).roots.count μ :=
      Multiset.one_le_count_iff_mem.2 ((mem_roots hG0).2 h3)
    calc N.charpoly.roots.count μ ≤ Multiset.card N.charpoly.roots := Multiset.count_le_card _ _
      _ ≤ N.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim N
      _ ≤ Fintype.card ι * (G.map f).roots.count μ := Nat.le_mul_of_pos_right _ h4
  · rw [Multiset.count_eq_zero.2 hμ]
    exact Nat.zero_le _

theorem charpoly_dvd_pow_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (G : K[X]) (hG : aeval f G = 0) :
    f.charpoly ∣ G ^ Module.finrank K V := by
  classical
  let b := Module.finBasis K V
  have hM : aeval (LinearMap.toMatrix b b f) G = 0 := by
    have := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom f G
    rw [hG, map_zero] at this
    have e : LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f := by
      ext i j
      simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [← e]
    exact this
  have := matrix_charpoly_dvd_pow _ G hM
  rwa [LinearMap.charpoly_toMatrix, Fintype.card_fin] at this

theorem main : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V :=
  fun f G hG => charpoly_dvd_pow_finrank f G hG

end GlobalTheory.CharpolyDvd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZeroStatement
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V := by
  first | exact @GlobalTheory.CharpolyDvd.main | exact GlobalTheory.CharpolyDvd.main | (intros; apply GlobalTheory.CharpolyDvd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemOfListProdMem
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemSpanIntegers
namespace GlobalTheory.SmulMemSpanIntegers

theorem exists_smul_mem_span_integers {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type}
    [AddCommGroup WL] [Module Ks WL] [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {T : Set WL} {g : WL}
    (hg : g ∈ Submodule.span Ks T) :
    ∃ d : NumberField.RingOfIntegers Ks, d ≠ 0 ∧
      d • g ∈ Submodule.span (NumberField.RingOfIntegers Ks) T := by

  induction hg using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d₁, hd₁, h₁⟩ := ihx
    obtain ⟨d₂, hd₂, h₂⟩ := ihy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm d₁ d₂ x]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul c x _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (NumberField.RingOfIntegers Ks) Ks b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ Ks)).2 hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have e : b • ((algebraMap (NumberField.RingOfIntegers Ks) Ks a /
        algebraMap (NumberField.RingOfIntegers Ks) Ks b) • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hbK, algebraMap_smul]
    rw [mul_comm, mul_smul, e, smul_comm]
    exact Submodule.smul_mem _ _ h

end GlobalTheory.SmulMemSpanIntegers
end

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SupPowNorm

open Formalism.IndefR.Arith

section Clear

variable {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type} [AddCommGroup WL] [Module Ks WL] [Module (𝓞 Ks) WL]
  [IsScalarTower (𝓞 Ks) Ks WL]

theorem exists_smul_mem_span_int {T : Set WL} {g : WL} (hg : g ∈ Submodule.span Ks T) :
    ∃ d : 𝓞 Ks, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 Ks) T := by
  first
  | exact @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers
  | (apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers ..)

end Clear

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_MK (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1)
    {t : WL} (ht : t ∈ A.MK) : ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := by
  obtain ⟨htW, htb⟩ := ht
  have hg := hW t htW
  obtain ⟨d, hd, hdg⟩ := exists_smul_mem_span_int (hspan _ hg)
  have hdM : d • hL t ∈ A.MK := (Submodule.span_le.2 fun x hx => hT x hx) hdg
  have hb : ∀ la y, FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ ≤ 1 := by
    intro la y
    obtain ⟨h1, h2⟩ := hdM
    have := h2 la y
    have e : (⟨d • hL t, h1⟩ : A.WK) = (algebraMap (𝓞 Ks) Ks d) • ⟨hL t, hg⟩ :=
      Subtype.ext (algebraMap_smul Ks d (hL t)).symm
    rwa [e, A.nrm_smul] at this
  have hfin : {la : HeightOneSpectrum (𝓞 Ks) | la.asIdeal ∣ Ideal.span {(p : 𝓞 Ks)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hex : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∈ la.asIdeal →
      ∃ n : ℕ, FinitePlace.mk la (N : Ks) ^ n ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := by
    intro la hla
    have hNla : (N : 𝓞 Ks) ∈ la.asIdeal := by
      obtain ⟨k, rfl⟩ := hpN
      push_cast
      exact la.asIdeal.mul_mem_right _ hla
    have h1 : FinitePlace.mk la (N : Ks) < 1 := by
      rw [FinitePlace.mk_apply]
      have := (FinitePlace.norm_lt_one_iff_mem Ks la (N : 𝓞 Ks)).2 hNla
      simpa using this
    have h2 : 0 < FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) := FinitePlace.pos_iff.2 (by simpa using hd)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
    exact ⟨n, hn.le⟩
  classical
  choose! nf hnf using hex
  refine ⟨hfin.toFinset.sup nf, fun m hm => ?_⟩
  have hmW : N ^ m • hL t ∈ A.WK := by
    rw [← Nat.cast_smul_eq_nsmul Ks]
    exact A.WK.smul_mem _ hg
  refine ⟨hmW, fun la y => ?_⟩
  have e : (⟨N ^ m • hL t, hmW⟩ : A.WK) = ((N : Ks) ^ m) • ⟨hL t, hg⟩ :=
    Subtype.ext (by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl)
  rw [e, A.nrm_smul, map_pow]
  have hN1 : FinitePlace.mk la (N : Ks) ≤ 1 := by
    rw [FinitePlace.mk_apply]
    simpa using FinitePlace.norm_le_one Ks la (N : 𝓞 Ks)
  have hN0 : 0 ≤ FinitePlace.mk la (N : Ks) := by positivity
  have h0 := A.nrm_nonneg la y ⟨hL t, hg⟩
  by_cases hla : (p : 𝓞 Ks) ∈ la.asIdeal
  · have hmem : la ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hla
    have hle : nf la ≤ m := (Finset.le_sup hmem).trans hm
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩
        ≤ FinitePlace.mk la (N : Ks) ^ nf la * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hN0 hN1 hle) h0
      _ ≤ FinitePlace.mk la (algebraMap (𝓞 Ks) Ks d) * A.nrm la y ⟨hL t, hg⟩ :=
          mul_le_mul_of_nonneg_right (hnf la hla) h0
      _ ≤ 1 := hb la y
  · have := hsup la hla t htW (htb la) y
    calc FinitePlace.mk la (N : Ks) ^ m * A.nrm la y ⟨hL t, hg⟩ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hN0 hN1) this h0 zero_le_one
      _ = 1 := one_mul 1

end Forms

section Span

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] (A : FormsL LL Ks WL W G)

theorem exists_pow_smul_mem_span (hL : WL →ₗ[LL] WL) (T : Finset WL) (hT : ∀ x ∈ T, x ∈ A.MK)
    (hMK : ∀ x ∈ A.MK, x ∈ Submodule.span (𝓞 Ks) (T : Set WL))
    (hspan : ∀ x ∈ A.WK, x ∈ Submodule.span Ks (T : Set WL)) (hW : ∀ x ∈ A.WK, hL x ∈ A.WK)
    {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hsup : ∀ la : HeightOneSpectrum (𝓞 Ks), (p : 𝓞 Ks) ∉ la.asIdeal → ∀ (f : WL) (hf : f ∈ A.WK),
      (∀ y, A.nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, A.nrm la y ⟨hL f, hW f hf⟩ ≤ 1) :
    ∃ n : ℕ, ∀ x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      N ^ n • hL x ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
  classical
  have hex : ∀ t ∈ T, ∃ n : ℕ, ∀ m, n ≤ m → N ^ m • hL t ∈ A.MK := fun t ht =>
    exists_pow_smul_mem_MK A hL T hT hspan hW hp hpN hsup (hT t ht)
  choose! nf hnf using hex
  set n := T.sup nf
  have hks : ∀ (a : Ks) (x : WL), hL (a • x) = a • hL x := fun a x => LinearMap.map_smul_of_tower hL a x
  have h0 : ∀ f ∈ Submodule.span (𝓞 Ks) (T : Set WL), N ^ n • hL f ∈ A.MK := by
    intro f hfs
    induction hfs using Submodule.span_induction with
    | mem t ht => exact hnf t ht n (Finset.le_sup ht)
    | zero => rw [map_zero, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul Ks a x, hks, algebraMap_smul, smul_comm]
      exact A.MK.smul_mem a hx
  have h1 : ∀ f ∈ A.MK, N ^ n • hL f ∈ A.MK := fun f hf => h0 f (hMK f hf)
  refine ⟨n, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span (h1 f hf)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | smul b x _ hx =>
    rw [LinearMap.map_smul_of_tower, smul_comm]
    exact Submodule.smul_mem _ b hx

end Span

section Prime

variable {E : Type} [Field E] [NumberField E]

theorem exists_mem_of_list_prod_mem (P : HeightOneSpectrum (𝓞 E)) :
    ∀ l : List (𝓞 E), l.prod ∈ P.asIdeal → ∃ x ∈ l, x ∈ P.asIdeal := by
  intro l
  simpa only [Multiset.prod_coe, Multiset.mem_coe] using
    (P.isPrime.multiset_prod_mem_iff_exists_mem (l : Multiset (𝓞 E))).mp

theorem exists_prime_dvd_card (P : HeightOneSpectrum (𝓞 E)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P.asIdeal ∧ p ∣ Nat.card (𝓞 E ⧸ P.asIdeal) := by
  have e : Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  rw [← Nat.prod_primeFactorsList hN, Nat.cast_list_prod] at hmem
  obtain ⟨x, hx, hxP⟩ := exists_mem_of_list_prod_mem P _ hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxP, e ▸ Nat.dvd_of_mem_primeFactorsList hp⟩

theorem prime_eq_of_mem (P : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) (hqP : (q : 𝓞 E) ∈ P.asIdeal) : p = q := by
  by_contra hne
  have hco : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := ((Nat.coprime_primes hp hq).2 hne).cast
  obtain ⟨u, v, huv⟩ := hco
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpP) (P.asIdeal.mul_mem_left _ hqP)))

end Prime

end GlobalTheory.SupPowNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

def twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) K) : MvPolynomial (ι × Fin n × Fin n) K :=
  C (∏ τ, (t τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
    bind₁ (fun k : ι × Fin n × Fin n => ∑ j : Fin n,
      C (t k.1 ((M : Matrix (Fin n) (Fin n) E) k.2.1 j)) * X (k.1, j, k.2.2)) P

theorem _root_.GlobalTheory.IntegralityCompare.map_twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ}
    (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K)
    (φ : K →+* ℂ) :
    map φ (_root_.GlobalTheory.IntegralityCompare.twSubK t M s P) =
      _root_.GlobalTheory.IntegralityCompare.twSub (fun τ => φ.comp (t τ)) M s (map φ P) := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSubK, _root_.GlobalTheory.IntegralityCompare.twSub, map_mul, map_C, map_bind₁]
  simp [map_prod, map_zpow₀]

private lemma eval_bind_eq_eval_comp {K σ τ : Type} [CommRing K] (f : σ → MvPolynomial τ K)
    (x : τ → K) (P : MvPolynomial σ K) :
    eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, aeval_bind₁]

theorem _root_.GlobalTheory.IntegralityCompare.eval_twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ}
    (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K)
    (x : ι → Matrix (Fin n) (Fin n) K) :
    eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) (_root_.GlobalTheory.IntegralityCompare.twSubK t M s P) =
      (∏ τ, (t τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
        eval (fun k : ι × Fin n × Fin n =>
          (((M : Matrix (Fin n) (Fin n) E).map (t k.1)) * x k.1) k.2.1 k.2.2) P := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSubK, map_mul, eval_C, eval_bind_eq_eval_comp]
  congr 3
  funext k
  simp [Matrix.mul_apply, eval_sum]

end GlobalTheory.IntegralityCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMulCoeffCharpolyRev
namespace GlobalTheory

theorem natCast_mul_coeff_charpolyRev {R : Type} [CommRing R] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | j
  · simp
  · have h := congrArg (PowerSeries.coeff j) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg,
      PowerSeries.coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [Prod.swap_prod_mk, PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    have e : ∀ i ∈ Finset.range (j + 1), j + 1 - 1 - i = j - i := fun i _ => by omega
    rw [Finset.sum_congr rfl fun i hi => by rw [e i hi], mul_comm, Nat.cast_succ, h]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun i _ => mul_comm _ _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.Mem

theorem tsum_eq_exp_tsum_neg_log_of_primes {α ι : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (p : ι → α) (hp : ∀ i, Prime (p i)) (hdvd : ∀ i j, p i ∣ p j → i = j)
    (f : α → ℂ) (hmul : ∀ a b, f (a * b) = f a * f b) (h1 : f 1 = 1)
    (hex : ∀ a, a ≠ 1 → f a ≠ 0 → ∃ i, p i ∣ a) (hsum : Summable fun a => ‖f a‖)
    (hne : ∀ i, 1 - f (p i) ≠ 0) :
    ∑' a, f a = exp (∑' i, -log (1 - f (p i))) := by
  classical
  set g : Finset ι → α → ℂ := fun S a => if ∀ i ∈ S, ¬ p i ∣ a then f a else 0 with hg
  have hgle : ∀ S a, ‖g S a‖ ≤ ‖f a‖ := by
    intro S a
    simp only [hg]
    split_ifs <;> simp
  have hgs : ∀ S, Summable (g S) := fun S => Summable.of_norm_bounded hsum (hgle S)
  have key : ∀ S : Finset ι, (∏ i ∈ S, (1 - f (p i))) * ∑' a, f a = ∑' a, g S a := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [hg]
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, mul_assoc, ih]
      have hinj : Function.Injective fun b : α => p i * b := mul_right_injective₀ (hp i).ne_zero
      have e1 : ∀ a, g (insert i S) a = g S a - (if p i ∣ a then g S a else 0) := by
        intro a
        simp only [hg, Finset.forall_mem_insert]
        by_cases h : p i ∣ a <;> simp [h]
      have hs2 : Summable fun a => if p i ∣ a then g S a else 0 :=
        Summable.of_norm_bounded hsum (fun a => by
          split_ifs
          · exact hgle S a
          · simp)
      have e2 : ∑' a, (if p i ∣ a then g S a else 0) = f (p i) * ∑' a, g S a := by
        rw [← hinj.tsum_eq, ← tsum_mul_left]
        · refine tsum_congr fun b => ?_
          rw [if_pos (dvd_mul_right _ _)]
          have : (∀ j ∈ S, ¬ p j ∣ p i * b) ↔ ∀ j ∈ S, ¬ p j ∣ b := by
            refine forall₂_congr fun j hj => not_congr ?_
            rw [(hp j).dvd_mul]
            refine or_iff_right fun h => hi ?_
            rwa [← hdvd _ _ h]
          simp only [hg, this, hmul]
          split_ifs <;> simp
        · intro a ha
          by_cases h : p i ∣ a
          · obtain ⟨b, rfl⟩ := h
            exact ⟨b, rfl⟩
          · simp [h] at ha
      simp only [e1]
      rw [(hgs S).tsum_sub hs2, e2]
      ring
  have lim1 : Tendsto (fun S : Finset ι => ∑' a, g S a) atTop
      (𝓝 (∑' a : α, if a = 1 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun a => ?_)
      (Eventually.of_forall fun S a => hgle S a)
    by_cases ha : a = 1
    · subst ha
      have : ∀ S, g S 1 = 1 := fun S => by
        simp only [hg]
        rw [if_pos fun i _ => (hp i).not_dvd_one, h1]
      simp [this]
    · rw [if_neg ha]
      by_cases hf : f a = 0
      · simp [hg, hf]
      · obtain ⟨i, hi⟩ := hex a ha hf
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with S hS
        simp only [hg]
        rw [if_neg]
        intro h
        exact h i (hS (Finset.mem_singleton_self i)) hi
  rw [tsum_ite_eq] at lim1
  have pinj : Function.Injective p := fun i j h => hdvd i j (h ▸ dvd_rfl)
  have hl : Summable fun i => log (1 - f (p i)) :=
    Summable.clog_one_sub (hsum.of_norm.comp_injective pinj)
  have lim2 : Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - f (p i))) atTop
      (𝓝 (exp (∑' i, log (1 - f (p i))))) := Complex.hasProd_of_hasSum_log hne hl.hasSum
  have lim3 := lim2.mul_const (∑' a, f a)
  simp only [key] at lim3
  have := tendsto_nhds_unique lim3 lim1
  rw [tsum_neg, exp_neg]
  exact eq_inv_of_mul_eq_one_right this

theorem lseriesSummable_card_absNorm (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ (fun _ => Nat.cast_nonneg _)
    zero_le_one hs
  have h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  exact Asymptotics.isBigO_of_div_tendsto_nhds (by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    exact absurd (Nat.cast_eq_zero.1 h0) hn.ne') _ h

instance finite_absNorm_fiber (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

theorem summable_norm_absNorm_cpow (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ => by exact norm_nonneg _)]
  refine ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card_absNorm K hs).norm.congr fun n => ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ = ‖(n : ℂ) ^ (-s)‖ := by
    rintro ⟨I, rfl⟩; rfl
  rw [tsum_congr this, tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hs0]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg, norm_mul]
    simp

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIInfKerOfIsBaseChange
open TensorProduct Module

namespace GlobalTheory

theorem finrank_iInf_ker_of_isBaseChange : ∀ (L Ω M M' ι : Type) [Field L] [Field Ω] [Algebra L Ω]
    [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module Ω M'] [Module L M']
    [IsScalarTower L Ω M'] (J : M →ₗ[L] M') (f : ι → M →ₗ[L] M) (f' : ι → M' →ₗ[Ω] M'),
    IsBaseChange Ω J → (∀ i x, f' i (J x) = J (f i x)) →
      finrank Ω ↥(⨅ i, LinearMap.ker (f' i)) = finrank L ↥(⨅ i, LinearMap.ker (f i)) := by
  intro L Ω M M' ι _ _ _ _ _ _ _ _ _ J f f' hJ hf
  have h1 : ⨅ i, LinearMap.ker (f' i) =
      Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) := by
    rw [GlobalTheory.GaloisDescent.span_image_iInf hJ]
    exact iInf_congr fun i =>
      (GlobalTheory.GaloisDescent.span_image_ker hJ hJ (f i) (f' i) (fun v => hf i v)).symm
  have h2 : Submodule.span Ω (J '' (⨅ i, LinearMap.ker (f i) : Submodule L M)) =
      ((⨅ i, LinearMap.ker (f i) : Submodule L M).baseChange Ω).map hJ.equiv.toLinearMap := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 2
    ext x
    simp [IsBaseChange.equiv_tmul]
  rw [h1, h2, LinearEquiv.finrank_map_eq, GlobalTheory.finrank_baseChange]

end GlobalTheory
end
