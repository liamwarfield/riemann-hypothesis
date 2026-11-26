module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapDimensionFormula
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowGerm.starRing_ext_of_star {R : Type*} [NonUnitalNonAssocSemiring R] (s t : StarRing R)
    (h : ∀ a : R, s.toStarMul.toInvolutiveStar.toStar.star a =
      t.toStarMul.toInvolutiveStar.toStar.star a) :
    s = t := by
  rcases s with @⟨@⟨@⟨@⟨s⟩, _⟩, _⟩, _⟩
  rcases t with @⟨@⟨@⟨@⟨t⟩, _⟩, _⟩, _⟩
  obtain rfl : s = t := funext h
  rfl

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowGerm.starSt : _root_.GlobalTheory.PowGerm.StarSt := by
  unfold _root_.GlobalTheory.PowGerm.StarSt
  intro E _ _ _ H inst h
  exact _root_.GlobalTheory.PowGerm.starRing_ext_of_star _ _ fun a => (h a).trans rfl

end GlobalTheory.PowGerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.NabJet
open MvPowerSeries

variable {k : Type} [CommRing k] {d n : ℕ}

theorem coeff_mul_congr (N : ℕ) (f g E : PS k n d)
    (h : ∀ a : Fin n × Fin d →₀ ℕ, a.degree ≤ N → coeff a f = coeff a g)
    (a : Fin n × Fin d →₀ ℕ) (ha : a.degree ≤ N) : coeff a (f * E) = coeff a (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = a.degree := by rw [← hp', map_add (f := _)]
  rw [h p.1 (by omega)]

theorem coeff_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (N : ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + 1 → coeff mo f = coeff mo g)
    (mo : Fin n × Fin d →₀ ℕ) (hmo : mo.degree ≤ N) :
    coeff mo (DofN F b v f) = coeff mo (DofN F b v g) := by
  classical
  unfold DofN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add (f := _)]
  rw [coeff_pderiv, coeff_pderiv, h]
  rw [map_add (f := _), Finsupp.degree_single]
  omega

theorem coeff_iterate_DofN_congr (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (r : ℕ) :
    ∀ (N : ℕ) (f g : PS k n d),
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + r → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo ((DofN F b v)^[r] f) = coeff mo ((DofN F b v)^[r] g) := by
  induction r with
  | zero => intro N f g h mo hmo; exact h mo hmo
  | succ r ih =>
    intro N f g h mo hmo
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih N _ _ (coeff_DofN_congr F b v (N + r) f g h) mo hmo

theorem coeff_foldr_DofN_congr (F : Fin d → PS k 2 d) {Ix : Type} (cp : Ix → Fin n) (u : Ix → Fin d → k) (m : Ix → ℕ)
    (f g : PS k n d) (L : List Ix) :
    ∀ N : ℕ,
      (∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N + (L.map m).sum → coeff mo f = coeff mo g) →
      ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ N →
        coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) f) =
          coeff mo (L.foldr (fun l s => (DofN F (cp l) (u l))^[m l] s) g) := by
  induction L with
  | nil => intro N h mo hmo; exact h mo hmo
  | cons l L ih =>
    intro N h mo hmo
    rw [List.foldr_cons, List.foldr_cons]
    refine coeff_iterate_DofN_congr F (cp l) (u l) (m l) N _ _ (ih (N + m l) fun mo' h' => h mo' ?_) mo hmo
    rw [List.map_cons, List.sum_cons]
    omega

theorem constantCoeff_DmonN_congr (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) :
    constantCoeff (DmonN F cp u m f) = constantCoeff (DmonN F cp u m g) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  unfold DmonN
  refine coeff_foldr_DofN_congr F cp u m f g _ 0 (fun mo' h' => h mo' ?_) 0 (by simp)
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum, zero_add] at h'

theorem isLinearMap_DofN (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) :
    IsLinearMap k (DofN F b v : PS k n d → PS k n d) := by
  constructor
  · intro f g
    unfold DofN
    simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]
  · intro c f
    unfold DofN
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum]

theorem isLinearMap_iterate {M : Type} [AddCommGroup M] [Module k M] (φ : M → M) (hφ : IsLinearMap k φ) (r : ℕ) :
    IsLinearMap k φ^[r] := by
  induction r with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ r ih =>
    constructor
    · intro f g
      simp only [Function.iterate_succ_apply, hφ.map_add (f := _), ih.map_add (f := _)]
    · intro c f
      simp only [Function.iterate_succ_apply, hφ.map_smul, ih.map_smul]

theorem isLinearMap_DmonN (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) : IsLinearMap k (DmonN F cp u m : PS k n d → PS k n d) := by
  unfold DmonN
  induction (Finset.univ : Finset Ix).toList with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons l L ih =>
    have hl := isLinearMap_iterate _ (isLinearMap_DofN F (cp l) (u l)) (m l)
    constructor
    · intro f g
      simp only [List.foldr_cons]
      rw [ih.map_add (f := _), hl.map_add (f := _)]
    · intro c f
      simp only [List.foldr_cons]
      rw [ih.map_smul, hl.map_smul]

theorem constantCoeff_DpolyN_eq (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (P : MvPolynomial Ix k) (f : PS k n d) (S : Finset (Ix →₀ ℕ)) (hS : P.support ⊆ S) :
    constantCoeff (DpolyN F cp u P f) = ∑ m ∈ S, P.coeff m * constantCoeff (DmonN F cp u m f) := by
  unfold DpolyN
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, constantCoeff_C]
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul]

end GlobalTheory.PowGerm.NabJet

namespace GlobalTheory.PowGerm
open MvPowerSeries

theorem nabJet : NabJetSt := by
  intro R _ d O _ _ B k _ _ _ h w0 q n Ix _ cp u
  classical
  refine ⟨fun P f g hfg => ?_, fun P J _ c f => ?_, fun f J _ c P => ?_⟩
  · unfold nabValN
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    refine NabJet.constantCoeff_DmonN_congr _ cp u m _ _ fun mo hmo => ?_
    refine NabJet.coeff_mul_congr P.totalDegree f g _ hfg mo (hmo.trans ?_)
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.degree_apply]
  · unfold nabValN
    simp only [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hl := NabJet.isLinearMap_DmonN (B.FK k) cp u m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, ← IsLinearMap.mk'_apply hl, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, IsLinearMap.mk'_apply, smul_eq_C_mul, map_mul, constantCoeff_C]
    ring
  · unfold nabValN
    set S : Finset (Ix →₀ ℕ) := (∑ j, c j • P j).support ∪ Finset.univ.biUnion fun j => (P j).support with hS
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u _ _ S Finset.subset_union_left]
    have hj : ∀ j, (P j).support ⊆ S := fun j =>
      (Finset.subset_biUnion_of_mem (fun j => (P j).support) (Finset.mem_univ j)).trans Finset.subset_union_right
    simp only [fun j => NabJet.constantCoeff_DpolyN_eq (B.FK k) cp u (P j)
      (f * FB.expS k ((q : k) • ∑ b, ev ![pt k d b] (B.hL k h w0))) S (hj j), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, _root_.mul_assoc]

end GlobalTheory.PowGerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsModular
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsUnitary
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapUnitary

theorem diag_single {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    PI.UpqRep.Jm ε * Matrix.single b a (1 : ℂ) * PI.UpqRep.Jm ε
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Matrix.single b a (1 : ℂ) := by
  ext i j
  unfold PI.UpqRep.Jm Formalism.REAL.sgn
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

theorem adj_unit {n : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    (Qᴴ * PI.UpqRep.Jm ε * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q)
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • (Q⁻¹ * Matrix.single b a 1 * Q) := by
  have h1 : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  have hi : Q⁻¹ = Qᴴ := Matrix.inv_eq_right_inv h1
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Q * (Qᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_single, star_one, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diag_single]
  simp only [Matrix.mul_assoc, h2]

theorem isUnitary_of_isE : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  intro hK k r ε mu R hR Q E hQ hE a b x y
  obtain ⟨-, -, hlin, -, -, hadj⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * PI.UpqRep.Jm ε * Q := hQ.1.2.symm
  have h0 : R.dC 0 (y : R.H) = 0 := by
    have := hlin 0 0 1 y y.2
    simpa using this
  have hs : ∀ (c : ℂ) Y, R.dC (c • Y) (y : R.H) = c • R.dC Y (y : R.H) := fun c Y => by
    have := hlin Y 0 c y y.2
    rwa [add_zero, h0, add_zero] at this
  rw [Submodule.coe_inner, Submodule.coe_inner, hE, hE, hadj _ _ x.2 _ y.2, hH, adj_unit ε Q hQ.2, hs,
    inner_smul_right]

end GlobalTheory.CapUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsUnitaryStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_endomorphisms_unitary : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  first | exact @GlobalTheory.CapUnitary.isUnitary_of_isE | exact GlobalTheory.CapUnitary.isUnitary_of_isE | (intros; apply GlobalTheory.CapUnitary.isUnitary_of_isE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsModular
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem isMod_smooth_of_isDS : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  intro hH k r ε mu R hk hDS Q E hQ hE
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hU : IsUnit Q := by
    have h1 : Q * star Q = 1 := (Matrix.mem_unitaryGroup_iff).1 hQ.2
    have h2 : star Q * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQ.2
    exact ⟨⟨Q, star Q, h1, h2⟩, rfl⟩
  have hG : Formalism.REAL.GlRel E := (GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hDS Q E hU hE).1
  refine ⟨hG, GlobalTheory.T.cayley_endomorphisms_unitary hK k r ε mu R hDS Q E hQ hE, ?_⟩
  exact GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue R.smSub (2 * r + k + 1) E mu (by omega) hG
    (GlobalTheory.T.quantum_determinant_eigenvalue hH k r ε mu R hDS Q E hU hE)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsModularStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_endomorphisms_modular : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  first | exact @GlobalTheory.isMod_smooth_of_isDS | exact GlobalTheory.isMod_smooth_of_isDS | (intros; apply GlobalTheory.isMod_smooth_of_isDS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimate
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSumDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSumDecomposition
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KapBes

variable {k r : ℕ}

theorem dsigW_zero (R : Rep k r) (W : List (Mx k r)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]

theorem smMap_zero (R R' : Rep k r) : SmMap R R' (fun _ => 0) := by
  refine ⟨fun _ _ => R'.smSub.zero_mem, ?_, ?_, ?_⟩
  · intros
    simp
  · intros
    simp
  · intro W _
    exact ⟨0, [], by simp, fun v _ => by simp [dsigW_zero]⟩

theorem smMap_congr {R R' : Rep k r} {T T' : R.H → R'.H} (h : SmMap R R' T)
    (e : ∀ v ∈ R.sm, T' v = T v) : SmMap R R' T' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [e v hv]
    exact h.mem v hv
  · intro v hv w hw
    rw [e v hv, e w hw, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hv hw), h.add v hv w hw]
  · intro a v hv
    rw [e v hv, e _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a hv), h.smul a v hv]
  · intro W hW
    obtain ⟨C, Ws, h1, h2⟩ := h.cont W hW
    refine ⟨C, Ws, h1, fun v hv => ?_⟩
    change ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (T' v)‖ ≤ _
    rw [e v hv]
    exact h2 v hv

theorem smMap_sum {R R' : Rep k r}
    (hl : ∀ (T T' : R.H → R'.H) (a : ℂ), SmMap R R' T → SmMap R R' T' → SmMap R R' (fun v => a • T v + T' v))
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (T : ι → R.H → R'.H) (hT : ∀ i, SmMap R R' (T i)) :
    SmMap R R' (fun v => ∑ i ∈ s, a i • T i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smMap_zero R R'
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact hl _ _ _ (hT i) ih

theorem mem_GG_of_mem_Sset {z : Fin (2 * r + k + 1) → ℂ} {s : Mx k r} (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) :
    s ∈ GG k r := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have h1 : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh.1
  have h2 : mᴴ * Formalism.QuantumDeterminants.Hpk k r * m = Formalism.QuantumDeterminants.Hpk k r := hm.1
  show (h * m)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = Formalism.QuantumDeterminants.Hpk k r
  rw [conjTranspose_mul]
  calc mᴴ * hᴴ * Formalism.QuantumDeterminants.Hpk k r * (h * m) = mᴴ * (hᴴ * Formalism.QuantumDeterminants.Hpk k r * h) * m := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem ev_eq {ι : Type} [Fintype ι] (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) :
    ev Γ R a x = ∑ j, (star a ᵥ* Γ) j • x j := by
  unfold ev
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  rfl

theorem vecMul_inv {ι : Type} [Fintype ι] (Γ A : Matrix ι ι ℂ) (a : ι → ℂ) (hA : Aᴴ * Γ * A = Γ)
    (ha : A *ᵥ a = a) : (star a ᵥ* Γ) ᵥ* A = star a ᵥ* Γ := by
  have h : star a ᵥ* Aᴴ = star a := by rw [← star_mulVec, ha]
  conv_rhs => rw [← hA, ← vecMul_vecMul, ← vecMul_vecMul, h]

theorem main : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI Wp _ _ _ _ z π om hR hRI hF hT hom I
  obtain ⟨-, -, hlin, hcw⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε mu (muI I) mu R (RI I) R hR (hRI I) hR
  obtain ⟨-, -, hlin', -⟩ := GlobalTheory.T.smooth_maps_closure hK k r ε (muI I) mu mu (RI I) R R (hRI I) hR hR
  refine ⟨fun lI hl => ?_, fun s hs y hy => ?_, ?_⟩
  · have hP : SmMap R (RI I) (fun v => ∑ c, pr I c (tm R om v c)) :=
      smMap_congr (smMap_sum hlin Finset.univ om (pr I) (hT.pr_sm I)) (fun v hv =>
        Finset.sum_congr rfl fun c _ => (hT.pr_sm I c).smul (om c) v hv)
    obtain ⟨h1, h2, h3, h4⟩ := hl
    refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun h hh m hm v hv => ?_, hcw Wp _ lI hP h4⟩
    · have := hP.add v hv w hw
      simp only at this ⊢
      rw [this]; exact h1 _ (hP.mem v hv) _ (hP.mem w hw)
    · have := hP.smul c v hv
      simp only at this ⊢
      rw [this]; exact h2 c _ (hP.mem v hv)
    · have hs : h * m ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨h, hh, m, hm, rfl⟩
      have e : tm R om (R.σ (h * m) v) = act ρ R (h * m) (tm R om v) := by
        funext i
        have := congrFun (hom _ hs) i
        simp only [tm, act, map_smul, smul_smul, ← Finset.sum_smul]
        rw [← this]; rfl
      have e2 := hT.pr_eq I _ (mem_GG_of_mem_Sset hs) (tm R om v)
        (fun c => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul (om c) hv)
      simp only
      rw [e, e2]
      exact h3 h hh m hm _ (hP.mem v hv)
  · have hG := mem_GG_of_mem_Sset hs
    rw [hT.io_eq I s hG y hy, ev_eq, ev_eq]
    have hv := vecMul_inv Γ (ρ s) om (hF.2.2.2.2.1 s hG) (hom s hs)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [act, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul, ← congrFun hv j]
    rfl
  · exact smMap_congr (smMap_sum hlin' Finset.univ (star om ᵥ* Γ) (io I) (hT.io_sm I))
      (fun y _ => ev_eq Γ R om _)

end GlobalTheory.KapBes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSumDecompositionStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
  first | exact @GlobalTheory.KapBes.main | exact GlobalTheory.KapBes.main | (intros; apply GlobalTheory.KapBes.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimate
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KappaDual

theorem mul_mem_GG {k r : ℕ} {g h : Mx k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) : g * h ∈ GG k r := by
  simp only [GG, Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hg hh ⊢
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * h) = hᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]

theorem ae_pair {k r : ℕ} {U V : Set (Mx k r)} {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : PI.BesselPeriodGGP.IsHaarOn V ν) :
    ∀ᵐ p ∂(μ.prod ν), Matrix.of p.1 ∈ U ∧ Matrix.of p.2 ∈ V := by
  haveI := hμ.1
  haveI := hν.1
  have h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ U := ae_iff.2 hμ.2.2.1
  have h2 : ∀ᵐ x ∂ν, Matrix.of x ∈ V := ae_iff.2 hν.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)

theorem kappa_dual : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (l : R.H → Wp), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → IsBeL R z π μW μN l → NzOn R l → ∀ I lI, IsBeL (RI I) z π μW μN lI → (∃ κ₀ : ℂ, ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ ∀ κ₀ : ℂ, (∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ z π u μW μN μG νq om l hR hRI hF hT hS hom
    hl hnz I lI hlI
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hbes, hS_eq, hsm⟩ :=
    GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth hK k r ι κ ρ Γ d R RI io pr ε mu muI Wp z π om hR hRI hF hT.raw hom I
  refine ⟨GlobalTheory.T.bessel_functional_side_growth hH k r ε mu R Wp z π u μW μN μG νq l _ hR hS hl.1 hnz (hbes lI hlI.1), ?_⟩
  intro κ₀ hκ y hy
  obtain ⟨v, hvTK, hv0⟩ := GlobalTheory.T.exists_K_type_nonzero_bessel hH k r ε mu R Wp z π l hR hl.1 hnz
  obtain ⟨-, -, -, -, hTKsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε mu R hR
  obtain ⟨-, -, -, hIsm, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε (muI I) (RI I) (hRI I)
  obtain ⟨hadj, -, hev, -⟩ := GlobalTheory.T.frep_discrete_series_sum hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT
  obtain ⟨-, -, -, hprTK⟩ := GlobalTheory.T.tensor_raw_of_frep hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw
  have hvsm : v ∈ R.sm := hTKsm v hvTK
  have htmTK : ∀ c, tm R om v c ∈ R.TK := fun c => R.TK.smul_mem _ hvTK
  have hPTK : (∑ c, pr I c (tm R om v c)) ∈ (RI I).TK :=
    Submodule.sum_mem _ fun c _ => hprTK I c _ (htmTK c)
  have h1 := (hl.2 _ (hsm.mem y hy) v hvTK).2
  have h2 := (hlI.2 y hy _ hPTK).2
  have h3 : be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (ev Γ R om (fun c => io I c y)) v =
      (ep I : ℂ) • be z Formalism.QuantumDeterminants.cStd π (RI I).σ μW μN y (∑ c, pr I c (tm R om v c)) := by
    unfold be
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [ae_pair hS.2.2.2.2.1 hS.2.2.2.2.2.1] with p hp
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Sset k r z := ⟨_, hp.1, _, hp.2, rfl⟩
    have hg : Matrix.of p.1 * Matrix.of p.2 ∈ GG k r := mul_mem_GG hp.1.1 hp.2.1
    unfold beInt
    rw [← hS_eq _ hs y hy, ← hev, hadj I _ (hIsm _ hg y hy) _ (fun c => hTKsm _ (htmTK c)), smul_smul, mul_assoc]
  rw [h1, h2, hκ v hvsm] at h3
  have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T (l v)) h3
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left] at h4
  have hne : ⟪l v, l v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  apply smul_right_injective Wp hne
  simp only
  rw [h4, smul_smul, smul_smul]
  congr 1
  simp only [starRingEnd_apply]
  ring

end GlobalTheory.KappaDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimateStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (l : R.H → Wp), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → IsBeL R z π μW μN l → NzOn R l → ∀ I lI, IsBeL (RI I) z π μW μN lI → (∃ κ₀ : ℂ, ∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ ∀ κ₀ : ℂ, (∀ v ∈ R.sm, lI (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → ∀ y ∈ (RI I).sm, l (ev Γ R om (fun c => io I c y)) = ((ep I : ℂ) * star κ₀) • lI y := by
  first | exact @GlobalTheory.KappaDual.kappa_dual | exact GlobalTheory.KappaDual.kappa_dual | (intros; apply GlobalTheory.KappaDual.kappa_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFramesEL
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem exists_frames_eL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
    (t : SAB H (Sp V)) (L' : LB t.G.left) (h : t.PP.L = L')
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (wP : PrimTyG t)
    (hch : IsChartG t (𝟙 (Sp V)) d FT act tg uv x) (hfr : IsFrameG t (𝟙 (Sp V)) d x FT act ph1 ph2 sy ad e)
    (hpr : IsPrimG t wP) :
    ∃ τ : Frames L' (κ := Fin 1 × Fin d) x, τ.Gen ∧
      (∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → L'.ι), Good L' y J →
        val (τ m) (𝟙 _) y J = val (genCast h _ _ (eLG t (𝟙 (Sp V)) d x act e wP m)) (𝟙 _) y J) ∧
      (FrTrunc t (𝟙 (Sp V)) d x e → τ.Trunc) := by
  subst h
  have hL := t.PP.isLB
  have heL : ∀ m, (eLG t (𝟙 (Sp V)) d x act e wP m).IsGen := fun m =>
    ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hpr.1 _)
      (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ (hfr.gen m) _)
  have hτ : ∀ m, ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG (𝟙 (Sp V)) d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (1 : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (eLG t (𝟙 (Sp V)) d x act e wP m) r z J := by
    intro m
    refine exists_gen hL ?_ _ (heL m)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
      GermD.formEq_eL hch m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  choose τ hτg hτv using hτ
  refine ⟨τ, hτg, fun m y J hJ => hτv m _ (𝟙 _) y J hJ, fun htr m y J hJ => ?_⟩
  exact (hτv (m + 1) _ (GermD.ρT (𝟙 (Sp V)) d m).left y J hJ).trans
    ((GermD.val_eL_trunc hch e wP htr m y J hJ).trans (hτv m _ (𝟙 _) y J hJ).symm)

theorem frame1St_holds : Frame1St := by
  intro E _ _ _ H V _ _ _ _ t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr
  exact exists_frames_eL t P.U.LG.L (congrArg RigLB.L P.bundle).symm d FT act ph1 ph2 sy ad tg _ xT eT wPT hch hfr hpr

end GlobalTheory.PowGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivPow

variable {V : Type} [CommRing V]

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (g : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) =
    Spec.map (CommRingCat.ofHom ((g.comp f : A →ₐ[V] C) : A →+* C))
  rw [← Spec.map_comp]
  rfl

theorem jet_ext {κ : Type} {m : ℕ} {B : Type} [CommRing B] [Algebra V B] (f g : Jet V κ m →ₐ[V] B)
    (h : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) = g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

theorem jetCopy_X {n d m : ℕ} (i : Fin n) (p : Fin 1 × Fin d) :
    (jetCopy d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, p.2)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun p : Fin 1 × Fin d =>
    (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) V)) (MvPolynomial.X p : MvPolynomial _ V)) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i : MvPolynomial κ V) = 0
  rw [MvPolynomial.aeval_X]

theorem jetTrunc_mk {κ : Type} {m : ℕ} (p : MvPolynomial κ V) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

theorem zV_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n d : ℕ} (pG : IsPowGrp G' G n)
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) (i : Fin n) :
    zV pG xT m ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m i) ≫ xT m :=
  pG.lim.fac _ ⟨i⟩

theorem pow_ext {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)}
    (f g : T ⟶ G') (h : ∀ i, f ≫ pG.pr i = g ≫ pG.pr i) : f = g :=
  pG.lim.hom_ext fun i => h i.as

theorem one_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)} (i : Fin n) :
    (1 : T ⟶ G') ≫ pG.pr i = 1 := by
  haveI := pG.hom i
  exact MonObj.one_comp _

end GlobalTheory.PowGerm.UnivPow

namespace GlobalTheory.PowGerm
open UnivPow

theorem univPow : UnivPowSt := by
  intro V _ G G' _ _ n d pG xT ⟨hT, hA, hU⟩
  refine ⟨fun m => pow_ext pG _ _ fun i => ?_, fun m => pow_ext pG _ _ fun i => ?_, ?_⟩
  · rw [Category.assoc, zV_pr, zV_pr, ← hT m, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetCopy_X, jetTrunc_mk, jetTrunc_mk, jetCopy_X]
  · rw [Category.assoc, zV_pr, one_pr, ← hA m, ← Category.assoc, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
  · intro A _ _ aug m hm y hy
    have hi : ∀ i : Fin n, ∃! ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
        aug.comp ψ = jetAug ∧ y ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ xT m := fun i =>
      hU A aug m hm (y ≫ pG.pr i) (by rw [← Category.assoc, hy, one_pr])
    choose ψ hψ hψu using hi
    let a : Fin n × Fin d → A := fun p => ψ p.1 (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))
    have ha : ∀ p, aug (a p) = 0 := fun p => by
      have := congrArg (fun f : Jet V (Fin 1 × Fin d) m →ₐ[V] V =>
        f (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))) (hψ p.1).1
      simp only [AlgHom.comp_apply, jetAug_X] at this
      exact this
    have hsp : Ideal.span (Set.range fun p => (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A)
        (MvPolynomial.X p)) ^ (m + 1) = ⊥ := by
      apply le_bot_iff.1
      rw [← hm]
      apply Ideal.pow_right_mono
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      simp only [MvPolynomial.aeval_X]
      exact ha p
    let Ψ : Jet V (Fin n × Fin d) m →ₐ[V] A := liftJet (MvPolynomial.aeval a) hsp
    have hΨ : ∀ p, Ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = a p := fun p => by
      show (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A) (MvPolynomial.X p) = a p
      rw [MvPolynomial.aeval_X]
    have hc : ∀ i, Ψ.comp (jetCopy d m i) = ψ i := fun i => by
      apply jet_ext
      rintro ⟨u, j⟩
      obtain rfl : u = 0 := Subsingleton.elim _ _
      rw [AlgHom.comp_apply, jetCopy_X, hΨ]
    refine ⟨Ψ, ⟨?_, pow_ext pG _ _ fun i => ?_⟩, ?_⟩
    · apply jet_ext
      intro p
      rw [AlgHom.comp_apply, hΨ, ha, jetAug_X]
    · rw [Category.assoc, zV_pr, ← Category.assoc, homAt_comp, hc]
      exact (hψ i).2
    · rintro Φ ⟨h1, h2⟩
      have hd : ∀ i, Φ.comp (jetCopy d m i) = ψ i := fun i => by
        apply hψu i
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, h1]
          apply jet_ext
          intro p
          rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
        · rw [h2, Category.assoc, zV_pr, ← Category.assoc, homAt_comp]
      apply jet_ext
      rintro ⟨i, j⟩
      rw [hΨ]
      show _ = ψ i _
      rw [← hd i, AlgHom.comp_apply, jetCopy_X]

end GlobalTheory.PowGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalJets_power_product : UnivPowSt := by
  first | exact @GlobalTheory.PowGerm.univPow | exact GlobalTheory.PowGerm.univPow | (intros; apply GlobalTheory.PowGerm.univPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientDerivativeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientDerivativeBound
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem l2SG_of_ae_smul {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F G : Mx k r → Wp) (c : ℝ)
    (h : ∀ᵐ x ∂νq, F (Matrix.of x) = (c : ℂ) • G (Matrix.of x)) :
    PI.BesselPeriodGGP.l2SG νq F = ENNReal.ofReal (c ^ 2) * PI.BesselPeriodGGP.l2SG νq G := by
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx, nnnorm_smul, ENNReal.coe_mul, mul_pow]
  congr 1
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg c), ← Real.norm_eq_abs, ← Complex.norm_real,
    ofReal_norm_eq_enorm]
  rfl

theorem scaled_bessel_isometric : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → IsBeL R z π μW μN l → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → NzOn R l → IsIsoB R z π νq (fun w => ((Real.sqrt dd : ℝ) : ℂ) • l w) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq l dd hDS hgap hok hS hl hd hnz
  refine ⟨Formalism.FourierDecayAlt.P.DDSmoothness.bessel_smul hl.1 _, fun w hw => ?_⟩
  obtain ⟨v, hv, hlv⟩ := GlobalTheory.bessel_nonzero_on_translates hH k r ε mu R Wp z π l hDS hl.1 hnz
  obtain ⟨-, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r ε mu R hDS
  obtain ⟨-, -, hdd, hP⟩ := GlobalTheory.T.bessel_integral_l2_norm_eq_div_formal_degree hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS dd hd v hv (l v)
  obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hn : 0 < ‖l v‖ := norm_pos_iff.mpr hlv
  have hin : ⟪l v, l v⟫_ℂ = ((‖l v‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; first | rfl | norm_cast | simp
  have hbe : ∀ y ∈ R.sm, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN y v (l v) = ((‖l v‖ ^ 2 : ℝ) : ℂ) • l y := by
    intro y hy
    rw [(hl.2 y hy v hv).2, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hin]
  have hre : (⟪l v, be z Formalism.QuantumDeterminants.cStd π R.σ μW μN v v (l v)⟫_ℂ).re = ‖l v‖ ^ 2 * ‖l v‖ ^ 2 := by
    rw [hbe v (hTK v hv), inner_smul_right, hin, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [l2SG_of_ae_smul νq _ (fun g => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN (R.σ g w) v (l v))
    (Real.sqrt dd / ‖l v‖ ^ 2), hP w hw, hre, ← ENNReal.ofReal_mul (sq_nonneg _)]
  · congr 1
    rw [div_pow, Real.sq_sqrt hdd.le]
    field_simp
  · filter_upwards [hae] with x hx
    rw [hbe _ (hsm _ hx w hw), smul_smul, ← Complex.ofReal_mul, div_mul_cancel₀ _ (pow_pos hn 2).ne']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapCoefficientDerivativeBoundStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → IsBeL R z π μW μN l → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) → NzOn R l → IsIsoB R z π νq (fun w => ((Real.sqrt dd : ℝ) : ℂ) • l w) := by
  first | exact @GlobalTheory.scaled_bessel_isometric | exact GlobalTheory.scaled_bessel_isometric | (intros; apply GlobalTheory.scaled_bessel_isometric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeries
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LowestVector

theorem _root_.GlobalTheory.LowestVector.exists_lowest_vector : _root_.PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : _root_.BranchingSupport.Rep k r), R.IsDS ε mu → ∀ (Q : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), _root_.PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ _root_.Formalism.REAL.KHighest ε E (_root_.Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (_root_.Formalism.REAL.kSpan ε E w) := by
  intro hKS k r ε mu R hDS Q E hQ hE
  have hFV := (_root_.GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R hDS Q hQ
  unfold _root_.PI.UpqRep.IsDS at hFV
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hFV
  unfold _root_.PI.UpqRep.IsKTypeOf at hS
  obtain ⟨hSfd, hSK, -, ⟨v, hvS, hv0, hvw⟩, hhigh⟩ := hS
  have hlow : _root_.PI.UpqRep.lowK ε mu = _root_.Formalism.QuantumDeterminants.lowK ε mu := rfl
  have hstab := _root_.GlobalTheory.CompactStable.kStable_smooth_and_stable hKS k r ε mu R hDS Q hQ S hSfd hSK
  unfold _root_.BranchingSupport.Rep.IsE at hE
  set w0 : R.H := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw0def
  have hw0S : w0 ∈ S := S.smul_mem _ hvS
  have hw0wt : _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) (fun g ↦ R.σ (Q⁻¹ * g * Q)) (_root_.PI.UpqRep.lowK ε mu) w0 := by
    unfold _root_.PI.UpqRep.IsWtOn at hvw ⊢
    intro θ hθ
    rw [hw0def, ContinuousLinearMap.map_smul, hvw θ hθ, smul_comm]
  have hnorm : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  let w : R.smSub := ⟨w0, (hstab.1 w0 hw0S).2⟩
  have htor := _root_.GlobalTheory.TorusWeight.torus_weight_action hKS k r ε mu R hDS Q E hQ hE (_root_.PI.UpqRep.lowK ε mu) w hw0wt
  let T : Submodule ℂ R.smSub := S.comap R.smSub.subtype
  have hT : _root_.Formalism.REAL.KStable ε E T := by
    unfold _root_.Formalism.REAL.KStable
    intro a b hab x hx
    show ((E a b x : R.smSub) : R.H) ∈ S
    rw [hE]
    exact hstab.2 a b hab x hx
  have hTfd : FiniteDimensional ℂ T := by
    let f : T →ₗ[ℂ] S :=
      LinearMap.codRestrict S (R.smSub.subtype.comp T.subtype) (fun x => x.2)
    refine Module.Finite.of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    exact hval
  have hle : _root_.Formalism.REAL.kSpan ε E w ≤ T := by
    unfold _root_.Formalism.REAL.kSpan
    exact sInf_le ⟨hw0S, hT⟩
  refine ⟨w, hnorm, (hstab.1 w0 hw0S).1, ?_, Submodule.finiteDimensional_of_le hle⟩
  unfold _root_.Formalism.REAL.KHighest
  refine ⟨htor.1, ?_⟩
  intro a b hab hεab
  by_contra hne
  have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
    rw [hE]
    exact hstab.2 a b hεab w0 hw0S
  have hne' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => hne (Submodule.coe_eq_zero.mp h)
  exact _root_.GlobalTheory.DominantRootSums.not_cDom_add_root _ ε (_root_.PI.UpqRep.lowK ε mu) a b hab
    (hhigh _ _ hmem hne' (htor.2 a b))

end GlobalTheory.LowestVector
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLowestKFiniteVectorDiscreteSeriesStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → ∃ w : R.smSub, ‖w‖ = 1 ∧ R.KFin (w : R.H) ∧ Formalism.REAL.KHighest ε E (Formalism.QuantumDeterminants.lowK ε mu) w ∧ FiniteDimensional ℂ (Formalism.REAL.kSpan ε E w) := by
  first | exact @GlobalTheory.LowestVector.exists_lowest_vector | exact GlobalTheory.LowestVector.exists_lowest_vector | (intros; apply GlobalTheory.LowestVector.exists_lowest_vector <;> assumption)
end
end
