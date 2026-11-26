module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGradedChartsNearGenericPointClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAbelianSchemeProjectiveClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGeometricTestOfHasUniformisedTest
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointTranslatePure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureTestsExistAndReductionIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeForms
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.FibCone

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := _root_.GlobalTheory.ZH.eval_eq_zero_of_hilb_le

theorem isIntegral_G {k : Type} [Field k] (Φ : FibPre k) : IsIntegral Φ.G.left := by
  have h : IsSemiAbelian Φ.G := GlobalTheory.isSemiAbelian_of_isGt _ Φ.E Φ.G ⟨Φ.D⟩
  have := h.smooth
  have := h.geomConnected
  have : GeometricallyIntegral Φ.G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ Φ.G
  exact GeometricallyIntegral.isIntegral_of_subsingleton Φ.G.hom

theorem exists_ne_zero_of_mem_cone {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) (J₀ : Set J) (hH : H.IsLB) (hc : ⨆ i ∈ J₀, Out.nonzeroLocus (s i) = ⊤) (v : J → k)
    (hv : v ∈ cone p H s) : ∃ i ∈ J₀, v i ≠ 0 := by
  obtain ⟨x, -, hx⟩ := hv
  let pt : Sp k := IsLocalRing.closedPoint k
  have hm : x pt ∈ (⨆ i ∈ J₀, Out.nonzeroLocus (s i)) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hm
  obtain ⟨i, hi, hm⟩ := hm
  refine ⟨i, hi, ?_⟩
  have hu := (((GlobalTheory.ZH.CrdCalc.crd_calculus X H J s hH).1 k x).2.2 v i hx).2 (by
    intro y _
    have : y = pt := Subsingleton.elim (α := PrimeSpectrum k) _ _
    subst this
    exact hm)
  exact hu.ne_zero

theorem mem_cone_iff : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  intro hL hL2 k _ _ Φ g N N' q J _ cls F π hB hG hg hN hsm hh v
  have hH := Φ.H_isLB 1
  have himm := GlobalTheory.T.immBy_weight_zero' hL hL2 k Φ g N N' q J cls F π hB hG hg
  constructor
  · intro hv
    exact ⟨exists_ne_zero_of_mem_cone _ _ F _ hH himm.1 v hv, fun d Pf hd hP ht =>
      GlobalTheory.T.form_vanishes_of_torsion_torusExtension hL hL2 k Φ g N N' q J cls F π hB hG hg hN d Pf hd hP ht v hv⟩
  · rintro ⟨h0, hv⟩
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.vanishing_ideal_cone_prime_homogeneous k _ Φ.G.hom (Φ.H 1) J F _ hH himm (isIntegral_G Φ) g hsm
    refine GlobalTheory.ZH.ConeClosed.mem_cone_of_vanishing k _ Φ.G.hom (Φ.H 1) J F _ hH himm v h0 ?_
    refine eval_eq_zero_of_hilb_le k J _ g N h1 h2 h3 h4 hh v fun d Pf hd hP hI => hv d Pf hd hP ?_
    intro x _
    obtain ⟨w, hw⟩ := ((GlobalTheory.ZH.CrdCalc.crd_calculus _ (Φ.H 1) J F hH).1 k x.left).1
    refine ⟨w, hw, ?_⟩
    have := (MvPolynomial.mem_vanishingIdeal_iff.1 hI) w ⟨x.left, Over.w x, hw⟩
    simpa [MvPolynomial.aeval_eq_eval] using this

end GlobalTheory.ZH.FibCone
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemTorusExtensionConeIffSmallDegreeFormsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_torusExtensionCone_iff_smallDegreeForms : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (g N N' : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec) (π : Φ.Pol N), Big g N N' → Φ.Good N q cls F → π.PB.g + Module.finrank ℤ Φ.E.X = g → (N' : k) ≠ 0 → SmoothOfRelativeDimension g Φ.G.hom → (∀ d, 1 ≤ d → hilb (cone Φ.G.hom (Φ.H 1) F) d ≤ (N * d) ^ g) → ∀ v : J → k, v ∈ cone Φ.G.hom (Φ.H 1) F ↔ ((∃ i, cls i = 0 ∧ v i ≠ 0) ∧ ∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → (∀ x : Φ.Pt, x ^ N' = 1 → ∃ w, Crd (Φ.H 1) F x.left w ∧ MvPolynomial.eval w Pf = 0) → MvPolynomial.eval v Pf = 0)) := by
  first | exact @GlobalTheory.ZH.FibCone.mem_cone_iff | exact GlobalTheory.ZH.FibCone.mem_cone_iff | (intros; apply GlobalTheory.ZH.FibCone.mem_cone_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsSpecialFibreSupportCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsSpecialFibreSupportCoordinates
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsCrd

theorem exists_unit_smul {O C J : Type} [CommRing O] [Field C] [Fintype J] [DecidableEq J] (φ : O →+* C)
    (hφ : Function.Injective φ) (m : Matrix J J O) (hm : IsUnit m.det) (w u : J → O) (lam : C)
    (h : ∀ i, φ (u i) = lam * φ (m.mulVec w i)) {i k : J} (hi : IsUnit (w i)) (hk : IsUnit (u k)) :
    ∃ mu : Oˣ, m.mulVec (fun j => (mu : O) * w j) = u := by
  have h1 : φ (m⁻¹.mulVec u i) = lam * φ (w i) := by
    have e : m⁻¹.mulVec (m.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec]
    conv_rhs => rw [← e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h ⊢
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h j]; ring
  obtain ⟨v, hv⟩ := hi.exists_right_inv
  have h2 : φ (m⁻¹.mulVec u i * v) = lam := by
    rw [map_mul, h1, _root_.mul_assoc, ← map_mul, hv, map_one, _root_.mul_one]
  have h3 : ∀ j, u j = (m⁻¹.mulVec u i * v) * m.mulVec w j := fun j => hφ (by rw [map_mul, h2, h])
  have h4 : IsUnit (m⁻¹.mulVec u i * v) := isUnit_of_mul_isUnit_left (h3 k ▸ hk)
  refine ⟨h4.unit, funext fun j => ?_⟩
  rw [h3 j, IsUnit.unit_spec]
  exact congrFun (Matrix.mulVec_smul m (m⁻¹.mulVec u i * v) w) j

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem sec_mem (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) (i : S.J) :
    (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
  refine (hB.sec z x₀ hx h hh).1 _ ?_
  rw [Q.basis l z hz]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem sec_unit (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} {z : M.Z} (hz : z ∈ Q.W l)
    {x₀ h : S.Gam} (hx : x₀ ∈ S.supI M z) (hh : h ∈ S.HH M z) :
    ∃ i, IsUnit (⟨_, sec_mem hB Q hz hx hh i⟩ : M.O z) := by
  obtain ⟨h1, i, h2, h3⟩ := hB.sec z x₀ hx h hh
  set v : S.J → Ω := fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i) with hv
  have hvE : v ∈ EE.E z := by
    have e : v = ∑ j, (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) • (Pi.single j (1 : Ω) : S.J → Ω) := by
      ext j
      simp [hv, Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def, Algebra.algebraMap_eq_smul_one]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB.mem z j)
  have hu : IsUnit (⟨_, h1 v hvE⟩ : M.O z) :=
    (RatModel.isUnit_O_iff _).2 ⟨div_ne_zero h2 hx.1, by simpa using h3⟩
  have hvE' := hvE
  rw [Q.basis l z hz] at hvE'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (M.O z) (v := fun k j => Q.B l k j)).1 hvE'
  have e : (⟨_, h1 v hvE⟩ : M.O z) = ∑ k, c k * ⟨_, sec_mem hB Q hz hx hh k⟩ := by
    refine Subtype.ext ?_
    show v ⬝ᵥ S.ev h / S.th x₀ = _
    rw [← hc, sum_dotProduct, Finset.sum_div]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_dotProduct, Subalgebra.smul_def, smul_eq_mul, mul_div_assoc]
  rw [e] at hu
  by_contra hn
  push_neg at hn
  refine (IsLocalRing.mem_maximalIdeal _).1 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ?_) hu
  exact (IsLocalRing.mem_maximalIdeal _).2 (hn k)

variable {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

theorem cen {Q : Clos ρ M U₀ EE} {u : ρ.UTest p y₀} (c : Q.Fac y u) : M.Cen U₀ (y (cPt p)) y := by
  refine ⟨rfl, ?_⟩
  have e : gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e2 : gPt p ≫ y = (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) ≫ U₀.ι := by
    rw [Category.assoc, c.yK_fac, ← Category.assoc, ← e, Category.assoc, c.fac]
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ c.yK) w).2

theorem val_gen (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) {l : Q.Λ} (hz : y (cPt p) ∈ Q.W l)
    (hc : M.Cen U₀ (y (cPt p)) y) (ha : S.At M y y₀) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) (h : S.Gam) (i : S.J) :
    M.val (gPt p ≫ y) ((Q.B l i ⬝ᵥ S.ev h) / S.th x₀) = M.val (gPt p ≫ y) (S.th x₀)⁻¹ *
      ((Q.B l).map (M.val (gPt p ≫ y))).mulVec (fun j => y₀ ⟨S.ev h j, S.ev_mem h j⟩) i := by
  let s : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  set ξ := (gPt p ≫ y) s with hξ
  have hr : Set.range (gPt p ≫ y) = {ξ} := RatModel.range_eq_singleton _ s
  have hU : ξ ∈ U₀ := hc.2 ⟨s, rfl⟩
  have hW : ξ ∈ Q.W l := (RatModel.gPt_specializes rfl s).mem_open (Q.W l).isOpen hz
  have hBm : ∀ j, Q.B l i j ∈ M.O ξ := by
    have : Q.B l i ∈ EE.E ξ := by
      rw [Q.basis l ξ hW]
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hB.ee.1 ξ hU] at this
    exact (RatModel.Lat.mem_const_iff M).1 this
  have hev : ∀ j, S.ev h j ∈ M.O ξ := fun j => RatModel.mem_ringOn.1 (hB.ov.le (S.ev_mem h j)) ξ hU
  have hth : (S.th x₀)⁻¹ ∈ M.O ξ := RatModel.mem_ringOn.1 (hB.ov.th_unit x₀ hx) ξ hU
  let e : M.O ξ := ⟨_, hth⟩ * ∑ j, ⟨_, hBm j⟩ * ⟨_, hev j⟩
  have he : (Q.B l i ⬝ᵥ S.ev h) / S.th x₀ = (e : Ω) := by
    simp only [e]
    push_cast
    rw [div_eq_inv_mul]
    rfl
  rw [he, ← RatModel.valHom_apply _ _ hr]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, map_mul, map_sum, RatModel.valHom_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (_ * ·) (ha ⟨_, S.ev_mem h j⟩).symm

theorem ker_eq (t : ρ.GeoTest p y₀) : t.τ.yy.ker = t.l.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  ext a
  have := he a 0
  rw [map_zero] at this
  exact this

theorem big (ρ : S.Real) (h : S.Big) : Big S.g S.N (S.r * S.N) := by
  refine ⟨?_, h.1, h.2.1⟩
  have h1 : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  rw [ρ.N_eq]
  nlinarith

theorem crd_red (hL : GlobalTheory.UT.LL) [ArithBase o Ω] (hB : BaseFacts S M U₀ EE) {Q : Clos ρ M U₀ EE}
    {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c) (hS : S.Big) {x₀ a : S.Gam}
    (hx : x₀ ∈ S.supI M (y (cPt p))) (ha : a ∈ S.HH M (y (cPt p))) (cc : Sp (OO p) ⟶ t.u.G.left) (a' : t.u.PtC)
    (x : t.mod.Φ.Pt) (h₁ : cc ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ cc = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) (h₄ : rPt p ≫ cc = x.left ≫ t.mod.r) :
    ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧
      (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w =
        fun i => M.val (rPt p ≫ y) ((Q.B tm.l i ⬝ᵥ S.ev a) / S.th x₀) := by
  have hv := (GlobalTheory.T.torsionValues_coords_operator_permute hL o Ω S ρ).1 _ y₀ a
  rw [← h₃] at hv
  have hb := t.link a' _ hv
  obtain ⟨wc, hwc⟩ := CrdCalc.crd_exists t.mod.isLB t.σ cc
  have hg := CrdCalc.crd_map (OO p).subtype hwc
  rw [← h₂] at hb
  obtain ⟨κ, hκ⟩ := CrdCalc.crd_unique hg hb
  obtain ⟨⟨i, -, hi⟩, -⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords hL.1 hL.2.1 p t.u.V t.u.j t.u.G S.g S.N (S.r * S.N) _ t.l.q _ S.J t.σ t.cls
    t.mod (big ρ hS) cc wc h₁ hwc
  obtain ⟨k, hk⟩ := sec_unit hB Q tm.mem hx ha
  let u : S.J → OO p := fun i => RatModel.valLoc y (y (cPt p)) specializes_rfl ⟨_, sec_mem hB Q tm.mem hx ha i⟩
  have hm : IsUnit (tm.m.map t.u.j).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map _
  obtain ⟨mu, hmu⟩ := exists_unit_smul (OO p).subtype Subtype.val_injective (tm.m.map t.u.j) hm wc u
    (M.val (gPt p ≫ y) (S.th x₀)⁻¹ * κ) (fun i => by
      refine (RatModel.val_spMap_comp (OO p).subtype y specializes_rfl _).symm.trans ?_
      refine (val_gen hB Q tm.mem (cen c) c.at_ hx.1 a i).trans ?_
      rw [tm.m_eq, ← Matrix.mulVec_mulVec, funext hκ, _root_.mul_assoc]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact mul_left_comm _ _ _) hi (hk.map _)
  have hr := CrdCalc.crd_map (IsLocalRing.residue (OO p)) (CrdCalc.crd_smul mu hwc)
  obtain ⟨w', hw'⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F (R := kb p) x.left
  have hw'' := t.mod.red x w' hw'
  rw [← h₄] at hw''
  obtain ⟨ν, hν⟩ := CrdCalc.crd_unique hw'' hr
  refine ⟨fun j => IsLocalRing.residue (OO p) (mu * wc j), ?_, funext fun i => ?_⟩
  · rw [funext hν]
    exact CrdCalc.crd_smul ν hw'
  · refine Eq.trans ?_ (RatModel.val_spMap_comp (IsLocalRing.residue (OO p)) y specializes_rfl
      ⟨_, sec_mem hB Q tm.mem hx ha i⟩).symm
    refine Eq.trans ?_ (congrArg (IsLocalRing.residue (OO p)) (congrFun hmu i))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem tors_crd : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → (∀ x : t.mod.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w ∈ Q.Tors (rPt p ≫ y) tm.l) ∧ ∀ v ∈ Q.Tors (rPt p ≫ y) tm.l, ∃ (x : t.mod.Φ.Pt) (w : S.J → kb p), x ^ (S.r * S.N) = 1 ∧ Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w = v := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [c.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hH : S.HH M (y (cPt p)) = t.l.yy.ker := (hB.atTest _ p y y₀ t.τ (cen c) c.at_).trans (ker_eq t)
  obtain ⟨-, g₁, g₂⟩ := GlobalTheory.T.specialFibre_torsion_eq_reductions hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint
  have hr : Set.range (rPt p ≫ y) = {y (cPt p)} := by
    rw [RatModel.range_eq_singleton (K := kb p) _ (IsLocalRing.closedPoint (kb p))]
    exact congrArg (fun s => ({y s} : Set M.Z)) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))
  constructor
  · intro x hx
    obtain ⟨a, ha, cc, a', h₁, h₂, h₃, h₄⟩ := g₁ x hx
    obtain ⟨x₀, hx₀⟩ := hB.ov.div (y (cPt p))
    rw [← hH] at ha
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨w, hw, y (cPt p), by rw [hr]; rfl, x₀, hx₀, a, ha, e⟩
  · rintro v ⟨z, hz, x₀, hx₀, a, ha, rfl⟩
    rw [hr] at hz
    obtain rfl : z = y (cPt p) := hz
    obtain ⟨cc, a', x, h₁, h₂, h₃, h₄, h₅⟩ := g₂ a (hH ▸ ha)
    obtain ⟨w, hw, e⟩ := crd_red hL hB tm hS hx₀ ha cc a' x h₁ h₂ h₃ h₄
    exact ⟨x, w, h₅, hw, e⟩

end GlobalTheory.ZH.TorsCrd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsSpecialFibreSupportCoordinatesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoints_specialFibre_supportCoordinates : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → (∀ x : t.mod.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ w, Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w ∈ Q.Tors (rPt p ≫ y) tm.l) ∧ ∀ v ∈ Q.Tors (rPt p ≫ y) tm.l, ∃ (x : t.mod.Φ.Pt) (w : S.J → kb p), x ^ (S.r * S.N) = 1 ∧ Crd (t.mod.Φ.H 1) t.mod.F x.left w ∧ (tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)).mulVec w = v := by
  first | exact @GlobalTheory.ZH.TorsCrd.tors_crd | exact GlobalTheory.ZH.TorsCrd.tors_crd | (intros; apply GlobalTheory.ZH.TorsCrd.tors_crd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankSpanReductionLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankSpanResidueLe
namespace GlobalTheory.ResidueSpanScale

theorem exists_scale {O K J : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite J] (c : J → K) (j : J) (hj : c j ≠ 0) :
    ∃ (j₀ : J) (d : J → O), c j₀ ≠ 0 ∧ d j₀ = 1 ∧ ∀ i, c i = c j₀ * algebraMap O K (d i) := by
  classical
  haveI : Nonempty J := ⟨j⟩
  obtain ⟨j₀, h₀⟩ := Finite.exists_max (fun i => ValuationRing.valuation O K (c i))
  have hv : ValuationRing.valuation O K (c j₀) ≠ 0 := by
    intro h
    have h1 := h₀ j
    rw [h, le_zero_iff] at h1
    exact hj ((Valuation.zero_iff _).1 h1)
  have hc : c j₀ ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hex : ∀ i, ∃ a : O, algebraMap O K a = c i / c j₀ := by
    intro i
    rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (h₀ i) zero_le
  choose d hd using hex
  refine ⟨j₀, d, hc, ?_, fun i => ?_⟩
  · apply IsFractionRing.injective O K
    rw [hd, div_self hc, map_one]
  · rw [hd]; field_simp

theorem finrank_span_residue_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K)
    (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i : I,
      f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O)
        (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  classical
  obtain ⟨κ, e, he, hsp, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField O) g
  haveI : Finite κ := Finite.of_injective e he
  haveI : Fintype κ := Fintype.ofFinite κ
  have hf : LinearIndependent K (f ∘ e) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    obtain ⟨j₀, d, hc₀, hd₀, hd⟩ := exists_scale (O := O) c j hj
    have hz : ∑ i, IsLocalRing.residue O (d i) • (g ∘ e) i = 0 := by
      funext b
      obtain ⟨a, w, hw⟩ := h b
      have h1 := congrFun hc a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply] at h1 ⊢
      have h2 : c j₀ * algebraMap O K (∑ i, d i * w (e i)) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← h1, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, (hw (e i)).1, ← mul_assoc, ← hd i]
      have h3 : ∑ i, d i * w (e i) = 0 := by
        apply IsFractionRing.injective O K
        rw [map_zero]
        exact (mul_eq_zero.1 h2).resolve_left hc₀
      have h4 := congrArg (IsLocalRing.residue O) h3
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, (hw (e i)).2]
    have := Fintype.linearIndependent_iff.1 hli _ hz j₀
    rw [hd₀, map_one] at this
    exact one_ne_zero this
  haveI : Module.Finite K (Submodule.span K (Set.range f)) :=
    Module.Finite.span_of_finite K (Set.finite_range f)
  rw [← hsp, finrank_span_eq_card hli, ← finrank_span_eq_card hf]
  exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range e f))

end GlobalTheory.ResidueSpanScale
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

namespace ModHilb

theorem finrank_span_reduction_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K) (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i, f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O) (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le
  | (apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanScale.finrank_span_residue_le ..)

theorem hilb_eq_finrank_span {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n)) := by
  unfold hilb
  have : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) =
      Submodule.span k (Set.range
      fun (m : {m : J →₀ ℕ // m.degree = d}) (v : C) => m.1.prod fun j n => v.1 j ^ n) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    rw [AddMonoidAlgebra.supported_eq_span_single, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨⟨m, hm⟩, ?_⟩
      funext v
      change _ = MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k))
      simp [MvPolynomial.aeval_monomial]
    · rintro ⟨⟨m, hm⟩, rfl⟩
      refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
      funext v
      change MvPolynomial.aeval v.1 (MvPolynomial.monomial m (1 : k)) = _
      simp [MvPolynomial.aeval_monomial]
  rw [this]

theorem hilb_reduction_le : (∀ (O K J : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Fintype J] (C : Set (J → K)) (C' : Set (J → IsLocalRing.ResidueField O)), (∀ v' ∈ C', ∃ w : J → O, (fun j => algebraMap O K (w j)) ∈ C ∧ v' = fun j => IsLocalRing.residue O (w j)) → ∀ d, hilb C' d ≤ hilb C d) := by
  intro O K J _ _ _ _ _ _ _ C C' h d
  rw [hilb_eq_finrank_span, hilb_eq_finrank_span]
  haveI : Finite {m : J →₀ ℕ // m.degree = d} :=
    (Finsupp.finite_of_degree_eq d).to_subtype
  apply finrank_span_reduction_le
  rintro ⟨v', hv'⟩
  obtain ⟨w, hw, rfl⟩ := h v' hv'
  refine ⟨⟨_, hw⟩, fun m => m.1.prod fun j n => w j ^ n, fun m => ⟨?_, ?_⟩⟩
  · simp [Finsupp.prod]
  · simp [Finsupp.prod]

end ModHilb

theorem Mod.hilb_special_le_generic : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls) (d : ℕ), hilb (cone m.Φ.G.hom (m.Φ.H 1) m.F) d ≤ hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ G.left, a ≫ G.hom = gPt p ≫ spMap j ∧ Crd H σ a w} d := by
  intro p _ V _ j G _ g N _ X _ q H J _ σ cls m d
  refine ModHilb.hilb_reduction_le (OO p) (PadicAlgCl p) J _ _ ?_ d
  rintro v ⟨x, hx, hv⟩
  have hred : Crd H σ (x ≫ m.r) v := m.red (Over.homMk x hx) v hv
  haveI := m.smooth
  haveI : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨c, hc, hcx⟩ := GlobalTheory.ZJ.exists_classical_lift_of_smooth p G.left (Sp V) G.hom (spMap j)
    (x ≫ m.r) (by
      rw [Category.assoc, m.cart.1.w, ← Category.assoc, hx]
      exact Category.id_comp _)
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists m.isLB σ c
  have hw' : Crd H σ (x ≫ m.r) (fun i => IsLocalRing.residue (OO p) (w i)) := by
    rw [← hcx]
    exact CrdCalc.crd_map _ hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw' hred
  obtain ⟨u₀, hu₀⟩ := IsLocalRing.residue_surjective (u : kb p)
  have hunit : IsUnit u₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu₀]
    exact u.ne_zero
  obtain ⟨u₁, rfl⟩ := hunit
  refine ⟨fun i => (u₁ : OO p) * w i, ⟨gPt p ≫ c, by rw [Category.assoc, hc], ?_⟩, ?_⟩
  · exact CrdCalc.crd_map (OO p).subtype (CrdCalc.crd_smul u₁ hw)
  · funext i
    rw [hu, map_mul, hu₀]

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependent
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TestFib

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ} [Fact p.Prime]

theorem level_ne_zero (S : ThetaSys o Ω) (y : Sp (OO p) ⟶ M.Z) : ((S.r * S.N : ℕ) : kb p) ≠ 0 := by
  have h := S.unit.map (Spec.preimage (rPt p ≫ y ≫ M.s)).hom
  rw [map_natCast] at h
  exact h.ne_zero

variable {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}

abbrev mb (tm : Q.TMap t c) : Matrix S.J S.J (kb p) :=
  tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)

theorem isUnit_det_mb (tm : Q.TMap t c) : IsUnit (mb tm).det := by
  have h := tm.unit.map ((IsLocalRing.residue (OO p)).comp t.u.j)
  rw [RingHom.map_det] at h
  exact h

theorem crd_image (tm : Q.TMap t c) (x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left) (hx : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _)
    (v : S.J → kb p) (hv : Crd (t.mod.Φ.H 1) t.mod.F x₀ v) :
    (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧
      Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) ((x₀ ≫ t.mod.r) ≫ tm.f) ((mb tm).mulVec v) := by
  have h1 : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
    rw [Category.assoc, t.mod.cart.1.w, ← Category.assoc, hx]
    exact Category.id_comp _
  refine ⟨h1, tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v (h1.trans ?_)
    (t.mod.red (Over.homMk x₀ hx) v hv)⟩
  exact (Spec.map_comp _ _).symm

theorem image_over (tm : Q.TMap t c) (c' : Sp (kb p) ⟶ t.u.G.left) (h : c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j) :
    (c' ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
  rw [Category.assoc, tm.f_over, ← Category.assoc, h, Category.assoc, c.fac]

theorem mem_cone_iff [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (tm : Q.TMap t c) (hS : S.Big)
    (v : S.J → kb p) :
    v ∈ cone t.mod.Φ.G.hom (t.mod.Φ.H 1) t.mod.F ↔ (∃ i, t.cls i = 0 ∧ v i ≠ 0) ∧
      ∀ (d : ℕ) (Pf : MvPolynomial S.J (kb p)), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d →
        (∀ w ∈ Q.Tors (rPt p ≫ y) tm.l, MvPolynomial.eval w Pf = 0) →
        MvPolynomial.eval ((mb tm).mulVec v) Pf = 0 := by
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback t.mod.cart.1 t.mod.smooth
  have hbig : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre hL o Ω S ρ p y₀ t.u).2.2.2.1, hS.1, hS.2.1⟩
  have key := GlobalTheory.T.mem_torusExtensionCone_iff_smallDegreeForms hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N (S.r * S.N) _ S.J _ t.mod.F t.mod.pol hbig
    t.mod.good t.mod.dim (level_ne_zero S y) hsm
    (fun d hd => (Mod.hilb_special_le_generic p _ _ _ _ _ 0 _ _ _ _ _ _ t.mod d).trans
      (GlobalTheory.T.degreeFormsDimension_genericFibre_le hL o Ω S ρ p y₀ t.u S.J t.σ d hd)) v
  obtain ⟨T₁, T₂⟩ := GlobalTheory.T.torsionPoints_specialFibre_supportCoordinates hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS
  have hinv : ∀ w, (mb tm)⁻¹.mulVec ((mb tm).mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_mb tm), Matrix.one_mulVec]
  refine key.trans (and_congr (exists_congr fun i => and_congr (map_eq_zero_iff _ t.mod.xe.symm.injective) Iff.rfl)
    ⟨fun H d Pf hd hPf hT => ?_, fun H d Pf hd hPf hT => ?_⟩)
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm) hPf
    rw [← hev]
    refine H d F hd hF fun x hx => ?_
    obtain ⟨w, hw, hw'⟩ := T₁ x hx
    exact ⟨w, hw, (hev w).trans (hT _ hw')⟩
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm)⁻¹ hPf
    rw [← hinv v, ← hev]
    refine H d F hd hF fun w hw => ?_
    obtain ⟨x, w₀, hx, hw₀, rfl⟩ := T₂ w hw
    obtain ⟨w₁, hw₁, h0⟩ := hT x hx
    obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw₁ hw₀
    rw [hev, hinv, show w₀ = fun j => (u : kb p) * w₁ j from funext hu, InFibChart.eval_scale _ _ hPf, h0, mul_zero]

theorem image_special_fibre_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x hx
  constructor
  · rintro ⟨c', hc', rfl⟩
    let x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left := t.mod.cart.1.lift c' (𝟙 _) (hc'.trans (Category.id_comp _).symm)
    have h₁ : x₀ ≫ t.mod.r = c' := t.mod.cart.1.lift_fst _ _ _
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := t.mod.cart.1.lift_snd _ _ _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hcr := (crd_image tm x₀ h₂ v hv).2
    rw [h₁] at hcr
    have hov := image_over tm c' hc'
    obtain ⟨k₁, k₂⟩ := (mem_cone_iff hL hB tm hS v).1 ⟨x₀, h₂, hv⟩
    rw [← Category.assoc]
    refine ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2 k₁,
      InFibChart.inFib_of_chart o Ω S ρ M U₀ EE hB Q _ tm.l _ _ hcr ?_⟩
    rw [hov]
    exact k₂
  · rintro ⟨hG, hF⟩
    obtain ⟨x', rfl⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
      refine ⟨IsOpenImmersion.lift _ x ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom (x w) = y (rPt p w) :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans
          ((congrArg (fun f : Sp (kb p) ⟶ M.Z => f w) hx).trans (Scheme.Hom.comp_apply _ _ _))
      show Q.P.hom (x w) ∈ Q.W tm.l
      rw [e]
      exact ((IsLocalRing.specializes_closedPoint (rPt p w)).map y.continuous).mem_open (Q.W tm.l).isOpen tm.mem
    have hLB : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := LB.isLB_pull Q.isLB _
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists hLB (Q.σ tm.l) x'
    obtain ⟨v, rfl⟩ : ∃ v, (mb tm).mulVec v = w := ⟨(mb tm)⁻¹.mulVec w, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_mb tm), Matrix.one_mulVec]⟩
    have hx' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := (Category.assoc _ _ _).symm.trans hx
    have k₂ := hF tm.l x' _ rfl hw
    rw [hx] at k₂
    obtain ⟨x₀, h₂, hv⟩ := (mem_cone_iff hL hB tm hS v).2
      ⟨(GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x' v hx' hw).1 hG, k₂⟩
    obtain ⟨h₁, hcr⟩ := crd_image tm x₀ h₂ v hv
    refine ⟨x₀ ≫ t.mod.r, h₁, ?_⟩
    have e : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ∣_ Q.W tm.l) = x' ≫ (Q.P.hom ∣_ Q.W tm.l) := by
      rw [← cancel_mono (Q.W tm.l).ι, Category.assoc, Category.assoc x', morphismRestrict_ι, hx']
      exact image_over tm _ h₁
    rw [← Category.assoc, ImmSep.eq_of_crd_eq _ _ _ _ _ _ _ hLB (Q.imm tm.l) (kb p) _ x' _
      (by rw [← Category.assoc, e, Category.assoc]) hcr hw]

end GlobalTheory.ZH.TestFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependentStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialFibre_image_test_independent : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  first | exact @GlobalTheory.ZH.TestFib.image_special_fibre_iff | exact GlobalTheory.ZH.TestFib.image_special_fibre_iff | (intros; apply GlobalTheory.ZH.TestFib.image_special_fibre_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IndepOfNestedSpecialFibreImages
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IndepOfNestedSpecialFibreImages
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.indep_of_special_fibres : ∀ C : Core, C.HasTests → (∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' → rPt p ≫ y = rPt p ≫ y' → ∃ (τ : C.Test y) (τ' : C.Test y'), ∀ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j → ∃ c' : Sp (kb p) ⟶ τ'.H.left, c' ≫ τ'.H.hom = rPt p ≫ spMap τ'.j ∧ c' ≫ τ'.f = c ≫ τ.f) → C.Indep := by
  intro C _ h p _ y y' hy hy' hr b hb
  obtain ⟨τ, τ', hτ⟩ := h p y y' hy hy' hr
  obtain ⟨c, hc, hcb⟩ := τ.lift b hb
  obtain ⟨c', hc', hcf⟩ := hτ (rPt p ≫ c) (by rw [Category.assoc, hc])
  have := τ'.smooth
  have : Smooth τ'.H.hom := SmoothOfRelativeDimension.smooth C.g τ'.H.hom
  obtain ⟨d, hd, hdr⟩ := GlobalTheory.T.exists_classical_lift_of_smooth' p _ _ τ'.H.hom (spMap τ'.j) c' hc'
  refine ⟨d ≫ τ'.f, ?_, ?_⟩
  · rw [Category.assoc, τ'.f_over, ← Category.assoc, hd, τ'.fac]
  · rw [← Category.assoc, hdr, hcf, Category.assoc, hcb]

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IndepOfNestedSpecialFibreImagesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.indep_of_nested_special_fibre_images : ∀ C : Core, C.HasTests → (∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' → rPt p ≫ y = rPt p ≫ y' → ∃ (τ : C.Test y) (τ' : C.Test y'), ∀ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j → ∃ c' : Sp (kb p) ⟶ τ'.H.left, c' ≫ τ'.H.hom = rPt p ≫ spMap τ'.j ∧ c' ≫ τ'.f = c ≫ τ.f) → C.Indep := by
  first | exact @GlobalTheory.ZJ.Core.indep_of_special_fibres | exact GlobalTheory.ZJ.Core.indep_of_special_fibres | (intros; apply GlobalTheory.ZJ.Core.indep_of_special_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureTestsExistAndReductionIndependent
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.CoreTests

theorem image_iff {T H B G B' F P : Scheme.{0}} (h : H ⟶ B) (s : T ⟶ B) (g : G ⟶ B') (s' : T ⟶ B')
    (r : F ⟶ G) (q : F ⟶ T) (cart : IsPullback r q g s') (u : H ⟶ P) (v : G ⟶ P)
    (e : pullback h s ≅ F) (e₁ : e.hom ≫ q = pullback.snd _ _) (e₂ : e.hom ≫ r ≫ v = pullback.fst _ _ ≫ u)
    (x : T ⟶ P) :
    (∃ c : T ⟶ H, c ≫ h = s ∧ c ≫ u = x) ↔ ∃ c' : T ⟶ G, c' ≫ g = s' ∧ c' ≫ v = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨pullback.lift c (𝟙 T) (by simpa using hc) ≫ e.hom ≫ r, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [cart.w, reassoc_of% e₁, pullback.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [e₂, pullback.lift_fst_assoc]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨cart.lift c (𝟙 T) (by simpa using hc) ≫ e.inv ≫ pullback.fst _ _, ?_, ?_⟩
    · simp only [Category.assoc]
      rw [pullback.condition, ← reassoc_of% e₁, e.inv_hom_id_assoc, cart.lift_snd_assoc, Category.id_comp]
    · simp only [Category.assoc]
      rw [← e₂, e.inv_hom_id_assoc, cart.lift_fst_assoc]

theorem exists_test (hL : GlobalTheory.UT.LL) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (ex : Q.Ext) (hS : S.Big) (hG : ρ.HasGeo)
    (p : ℕ) [Fact p.Prime] (y : Sp (GlobalTheory.ZJ.OO p) ⟶ ex.core.Z) (hy : ex.core.Cl y) :
    ∃ τ : ex.core.Test y, ∀ x : Sp (GlobalTheory.ZJ.kb p) ⟶ Q.P.left, x ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y →
      ((∃ c : Sp (GlobalTheory.ZJ.kb p) ⟶ τ.H.left, c ≫ τ.H.hom = GlobalTheory.ZJ.rPt p ≫ spMap τ.j ∧ c ≫ τ.f ≫ Q.G.ι = x) ↔
        (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  obtain ⟨y₀, t, c, ⟨tm⟩⟩ := (GlobalTheory.T.exists_geometricTest_map_classicalPoint hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hy
  obtain ⟨τ, e, e₁, e₂⟩ := GlobalTheory.T.exists_uniformisationTest_of_geometricTest hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t c tm hS
  refine ⟨τ, fun x hx => ?_⟩
  exact (image_iff _ _ _ _ _ _ t.mod.cart.1 _ _ e e₁ e₂ x).trans
    (GlobalTheory.T.specialFibre_image_test_independent hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x hx)

end GlobalTheory.ZH.CoreTests

theorem GlobalTheory.ZH.Clos.Ext.hasTests_and_indep : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.HasTests ∧ ex.core.Indep := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have key := GlobalTheory.ZH.CoreTests.exists_test hL o Ω S ρ M U₀ EE hB Q ex hS hG
  have hT : ex.core.HasTests := fun p _ y hy => ⟨(key p y hy).choose⟩
  refine ⟨hT, GlobalTheory.T.indep_of_nested_special_fibre_images _ hT fun p _ y y' hy hy' hr => ?_⟩
  obtain ⟨τ, hτ⟩ := key p y hy
  obtain ⟨τ', hτ'⟩ := key p y' hy'
  refine ⟨τ, τ', fun c hc => ?_⟩
  have hx : (c ≫ τ.f ≫ Q.G.ι) ≫ Q.P.hom = GlobalTheory.ZJ.rPt p ≫ y := by
    have h : c ≫ τ.f ≫ ex.core.GG.hom = GlobalTheory.ZJ.rPt p ≫ y := by
      rw [τ.f_over, reassoc_of% hc, τ.fac]
    simp only [Category.assoc]
    exact h
  obtain ⟨c', hc', hf⟩ := (hτ' _ (hx.trans hr)).2 ((hτ _ hx).1 ⟨c, hc, rfl⟩)
  refine ⟨c', hc', ?_⟩
  have : Mono ex.core.G.ι := inferInstance
  rw [← cancel_mono ex.core.G.ι, Category.assoc, Category.assoc]
  exact hf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureTestsExistAndReductionIndependentStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_tests_exist_and_reduction_independent : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.HasTests ∧ ex.core.Indep := by
  first | exact @GlobalTheory.ZH.Clos.Ext.hasTests_and_indep | exact GlobalTheory.ZH.Clos.Ext.hasTests_and_indep | (intros; apply GlobalTheory.ZH.Clos.Ext.hasTests_and_indep <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem baseFacts_hasGeo_exists_clos : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Big → ρ.HasU → S.Over₀ M U₀ → S.IsEE M U₀ EE → BaseFacts S M U₀ EE ∧ ρ.HasGeo ∧ ∃ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), ex.core.HasTests ∧ ex.core.Indep ∧ ex.core.Fib ∧ ex.core.HasCharts := by
  intro hL hT o Ω _ _ _ _ S ρ M U₀ EE hB hU hO hE
  have hTests : S.HasTests := by
    intro p _ y hy
    obtain ⟨_, _, τ, _⟩ := hU p y hy ∅
    exact ⟨τ⟩
  have hF : BaseFacts S M U₀ EE := baseFacts_of_isEE o Ω S M U₀ EE hTests hO hE
  have hG : ρ.HasGeo := GlobalTheory.T.hasGeometricTest_of_hasUniformisedTest hL hT o Ω S ρ hB hU
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_abelianSchemeProjectiveClosure hL o Ω S ρ M U₀ EE hF
  obtain ⟨ex⟩ := GlobalTheory.T.nonempty_closureExtension_abelianScheme hL o Ω S ρ M U₀ EE hF Q
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.closure_tests_exist_and_reduction_independent hL o Ω S ρ M U₀ EE hF Q ex hB hG
  have h₃ : ex.core.Fib := GlobalTheory.T.fibre_eq_specialFibre_of_reduction_indep ex.core h₂
  exact ⟨hF, hG, Q, ex, h₁, h₂, h₃, GlobalTheory.T.hasGradedCharts_near_generic_point_closure hL o Ω S ρ M U₀ EE hF Q ex hB hG h₃⟩

end GlobalTheory.ZH
