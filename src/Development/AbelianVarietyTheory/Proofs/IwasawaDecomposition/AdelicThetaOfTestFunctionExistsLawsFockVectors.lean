module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunction
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicThetaOfTestFunctionExistsLawsFockVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThBijFock
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker

theorem th_bij_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → (∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsZak (C.xB B) φ (C.Th (C.xB B) φ) ∧ C.IsFock B (C.Th (C.xB B) φ)) ∧ (∀ f, C.IsTh f → C.IsFock B f → ∃! φ : TF S.rank C.g, SW.IsSB φ ∧ f = C.Th (C.xB B) φ) := by
  intro D S T C B hB
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  refine ⟨fun φ hφ => ⟨(GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).1, ((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB φ hφ).1⟩, ?_⟩
  intro f hf hF
  obtain ⟨φ, hφ, rfl⟩ := GlobalTheory.T.exists_testFunction_of_fockVacuum_thetaFunction D S T C B hB f hf hF
  refine ⟨φ, ⟨hφ, rfl⟩, ?_⟩
  rintro ψ ⟨hψ, h⟩
  exact (((GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx φ hφ).1 ψ hψ).2 h).symm

end GlobalTheory.Ker
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicThetaOfTestFunctionExistsLawsFockVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem pureTensorL_rename {ι κ X : Type} {A : κ → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f)) {f : X → ℂ} (hf : P f)
    (e : ι → κ) (Q : MvPolynomial ι ℂ) :
    pureTensorL (fun i => A (e i)) f Q = pureTensorL A f (MvPolynomial.rename e Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [MvPolynomial.rename_monomial, Ker.FockAlg.pure_monomial, Ker.FockAlg.pure_monomial]
    congr 1
    unfold opPow
    rw [← List.foldr_map (f := e) (g := fun i g => A i g)]
    refine Ker.FockAlg.foldr_perm hA hc hf ?_
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
      Finsupp.toMultiset_map]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem unitMap_perm {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (π : Equiv.Perm (Fin m))
    (a : Fin m) (k : Fin n) : unitMap B (Z.submatrix id π) (π.symm a) k = unitMap B Z a k := by
  unfold unitMap
  congr 1
  ext i j
  by_cases h : j = k
  · subst h
    simp
  · simp [h]

theorem fvec_perm {D : D7} {S T : HSp D} (C : Ker.Ctx S T) (Z : Fam T) (π : Equiv.Perm (Fin T.rank))
    (hB : C.IsB fun ρ => (Z ρ).submatrix id π) {f : WO S T → ℂ} (hf : C.IsTh f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB fun ρ => (Z ρ).submatrix id π) (fun _ => 1) Z f Q =
      C.fvec (fun ρ => (Z ρ).submatrix id π) f (MvPolynomial.rename (fun v => (v.1, π.symm v.2.1, v.2.2)) Q) := by
  have h := pureTensorL_rename (P := C.IsTh)
    (A := aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB (fun ρ => (Z ρ).submatrix id π) τ)) (fun _ => 1)
      (fun ρ => (Z ρ).submatrix id π))
    (fun _ _ h => Ker.FockAlg.aPlus_th C _ _ _ h)
    (fun i j _ h => Ker.FockAlg.aPlus_comm C i.1 _ hB j.1 _ h) hf
    (fun v : FVar D T.rank S.rank => (v.1, π.symm v.2.1, v.2.2)) Q
  refine Eq.trans ?_ h
  unfold pureTensorO
  congr 2
  funext i
  simp only [aPlusAll, unitMap_perm]

theorem zak_laws : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → (∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → (∃ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) ∧ ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → (∀ f', Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f' → f' = f) ∧ (∀ φ', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f → φ' = φ) ∧ (∀ a : ℂ, Zak ψ θ hr eT bas idx (frOf hr eT Z) (a • φ) (a • f)) ∧ (∀ φ' f', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f' → Zak ψ θ hr eT bas idx (frOf hr eT Z) (φ + φ') (f + f')) ∧ (∀ y : Matrix (Fin S.rank) (Fin r) D.host.E, Zak ψ θ hr eT bas idx (frOf hr eT Z) (heisG X bas (-y) φ) (heisO ψ S T (finR S hr y) f)) ∧ (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) ∧ ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), fv ψ θ S T X.p0 Z f Q 0 = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT Z)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) → ∃ φ : TF S.rank g, GlobalTheory.SW.IsSB φ ∧ Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f := by
  intro D S T r g hr ψ θ X eT bas idx hS Z hZ
  have hq0 : X.p0 + (r - X.p0) = r := Nat.add_sub_cancel' X.p0_le
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, hheis, hZZ⟩ :=
    GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T r g hr ψ θ X eT bas idx hS (r - X.p0) hq0
  obtain ⟨hB, hrest⟩ := hZZ Z
  obtain ⟨hsB, hzak, hthP⟩ := hrest hZ
  have hB := hB.1 hZ
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  set B : C.Bas := fun ρ => (Z ρ).submatrix id π with hBdef
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have key : ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f,
      Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f ↔ f = C.Th (C.xB B) φ := by
    intro φ hφ f
    rw [← hzak]
    exact ⟨(GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).2 f, fun h => h ▸ (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ hx φ hφ).1⟩
  refine ⟨fun φ hφ => ⟨⟨_, (key φ hφ _).2 rfl⟩, fun f hf => ?_⟩, fun f hf hF => ?_⟩
  · have hth : C.IsTh f := hf.1
    obtain rfl := (key φ hφ f).1 hf
    obtain ⟨l1, l2, l3, -⟩ := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx φ hφ
    obtain ⟨f1, f2⟩ := (GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 B hB φ hφ
    refine ⟨fun f' hf' => (key φ hφ f').1 hf', fun φ' hφ' h => ?_, fun a => ?_, fun φ' f' hφ' h => ?_,
      fun y => ?_, fun ρ => ?_, fun q0 hq Q => ?_⟩
    · exact ((l1 φ' hφ').2 ((key φ' hφ' _).1 h)).symm
    · exact (key _ ((GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ hφ hφ).2.1 a) _).2 (l2 a).symm
    · rw [(key φ' hφ' _).1 h]
      exact (key _ (GlobalTheory.SW.isSB_algebra_haar_linear _ _ _ φ φ' hφ hφ').1 _).2 (l1 φ' hφ').1.symm
    · refine (key _ ((heisG_laws _ r X g bas idx S.rank hS.2.2.2.2.2.2.2 hS.2.2.2.1).2.2.2 (-y) φ hφ).1 _).2 ?_
      rw [← hheis]
      exact l3 _
    · rw [← hsB]
      exact f1 ρ
    · obtain rfl : q0 = r - X.p0 := by omega
      rw [← hthP, fv, ← hsB]
      exact (congrFun (fvec_perm C Z π hB hth Q) 0).trans (f2 _)
  · obtain ⟨φ, ⟨hφ, h⟩, -⟩ := (Ker.th_bij_fock D S T C B hB).2 f hf (fun ρ => by rw [hsB]; exact hF ρ)
    exact ⟨φ, hφ, (key φ hφ f).2 h⟩

end GlobalTheory.OneMapRef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicThetaOfTestFunctionExistsLawsFockVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTheta_of_testFunction_exists_laws_fockVectors : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ Z : Fam T, IsONeg T X.p0 Z → (∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → (∃ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f) ∧ ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → (∀ f', Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f' → f' = f) ∧ (∀ φ', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f → φ' = φ) ∧ (∀ a : ℂ, Zak ψ θ hr eT bas idx (frOf hr eT Z) (a • φ) (a • f)) ∧ (∀ φ' f', GlobalTheory.SW.IsSB φ' → Zak ψ θ hr eT bas idx (frOf hr eT Z) φ' f' → Zak ψ θ hr eT bas idx (frOf hr eT Z) (φ + φ') (f + f')) ∧ (∀ y : Matrix (Fin S.rank) (Fin r) D.host.E, Zak ψ θ hr eT bas idx (frOf hr eT Z) (heisG X bas (-y) φ) (heisO ψ S T (finR S hr y) f)) ∧ (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) ∧ ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), fv ψ θ S T X.p0 Z f Q 0 = thP X hq bas idx φ (toP S hr eT hq Q) (frOf hr eT Z)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO 1 (cartZ T X.p0 Z ρ)) f) → ∃ φ : TF S.rank g, GlobalTheory.SW.IsSB φ ∧ Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f := by
  first | exact @GlobalTheory.OneMapRef.zak_laws | exact GlobalTheory.OneMapRef.zak_laws | (intros; apply GlobalTheory.OneMapRef.zak_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdele
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdele
noncomputable section

namespace GlobalTheory.UnipApproxGL

open NumberField IsDedekindDomain Matrix PIW.ClassFinD

variable {F : Type} [Field F] [NumberField F]

theorem approx (x e : FiniteAdeleRing (𝓞 F) F) :
    ∃ r : F, e * (x + algebraMap F (FiniteAdeleRing (𝓞 F) F) r) ∈ Ohat F := by
  have hU : IsOpen ((fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) ⁻¹'
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F)) :=
    ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_Oint.preimage (continuous_const.mul (continuous_const.add continuous_id))
  have h0 : (fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) (-x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F := by
    show e * (x + -x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F
    rw [add_neg_cancel, mul_zero]
    exact (Ohat F).zero_mem
  obtain ⟨r, hr⟩ := (PI.UnipApproxD.additive_dense_integers F).exists_mem_open hU ⟨-x, h0⟩
  exact ⟨r, hr⟩

theorem row_exists (n : ℕ) (u : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hu : IsUpperUni u) (i : Fin n) (e : Fin n → FiniteAdeleRing (𝓞 F) F) :
    ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j, i < j → e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
  classical
  have key : ∀ m : ℕ, ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j : Fin n, i < j → j.val < m →
        e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun k => if k = i then 1 else 0, by simp, fun k hk => ?_, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
      simp [ne_of_lt hk]
    | succ m ih =>
      obtain ⟨y, hy1, hy0, hyc⟩ := ih
      by_cases h : ∃ hm : m < n, i < (⟨m, hm⟩ : Fin n)
      · obtain ⟨hm, him⟩ := h
        obtain ⟨r, hr⟩ := approx (∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k ⟨m, hm⟩)
          (e ⟨m, hm⟩)
        have hsum : ∀ j, ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F)
              (y k + if k = (⟨m, hm⟩ : Fin n) then r else 0) * u k j
            = ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j +
                algebraMap F (FiniteAdeleRing (𝓞 F) F) r * u ⟨m, hm⟩ j := by
          intro j
          simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, apply_ite (algebraMap F _), map_zero,
            ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        refine ⟨fun k => y k + if k = (⟨m, hm⟩ : Fin n) then r else 0, ?_, ?_, ?_⟩
        · simp [hy1, ne_of_lt him]
        · intro k hk
          simp [hy0 k hk, ne_of_lt (hk.trans him)]
        · intro j hij hjm
          rw [hsum]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
          · rw [hu.1 ⟨m, hm⟩ j (by rw [Fin.lt_def]; exact hj), mul_zero, add_zero]
            exact hyc j hij hj
          · have hjM : j = ⟨m, hm⟩ := Fin.ext hj
            subst hjM
            rw [hu.2, mul_one]
            exact hr
      · refine ⟨y, hy1, hy0, fun j hij hjm => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
        · exact hyc j hij hj
        · exfalso
          have hm : m < n := hj ▸ j.isLt
          exact h ⟨hm, by rwa [show (⟨m, hm⟩ : Fin n) = j from Fin.ext hj.symm]⟩
  obtain ⟨y, h1, h2, h3⟩ := key n
  exact ⟨y, h1, h2, fun j hij => h3 j hij j.isLt⟩

theorem matInt_inv_of_upperUni {n : ℕ} (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hg : IsUpperUni g.val) (hi : MatInt g.val) : MatInt g⁻¹.val := by
  have hdet : g.val.det = 1 := by
    rw [det_of_upperTriangular (fun i j hij => hg.1 i j hij)]
    simp [hg.2]
  have h1 : g.val * adjugate g.val = 1 := by rw [mul_adjugate, hdet, one_smul]
  have hinv : g⁻¹.val = adjugate g.val := by
    calc g⁻¹.val = g⁻¹.val * (g.val * adjugate g.val) := by rw [h1, mul_one]
      _ = adjugate g.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
  let W' : Matrix (Fin n) (Fin n) (Ohat F) := fun i j => ⟨g.val i j, hi i j⟩
  have hW : g.val = (Ohat F).subtype.mapMatrix W' := by ext i j; rfl
  intro i j
  rw [hinv, hW, ← RingHom.map_adjugate]
  exact ((adjugate W') i j).2

theorem unipApprox : PIW.ClassFinD.UnipApprox := by
  classical
  intro F _ _ n u t hu ht
  obtain ⟨τ, rfl⟩ := diag_eq_diagGL t ht
  choose y hy1 hy0 hyc using fun i => row_exists n u.val hu i
    (fun j => (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j)
  let Y : Matrix (Fin n) (Fin n) F := fun i k => y i k
  have hdet : Y.det = 1 := by
    rw [det_of_upperTriangular (fun i k hki => hy0 i k hki)]
    simp [Y, hy1]
  let Yg : GL (Fin n) F :=
    ((Matrix.isUnit_iff_isUnit_det Y).mpr (by rw [hdet]; exact isUnit_one)).unit

  let P : Fin n → Fin n → FiniteAdeleRing (𝓞 F) F := fun i j =>
    ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y i k) * u.val k j
  have hPlow : ∀ i j, j < i → P i j = 0 := by
    intro i j hji
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hy0 i k hk, map_zero, zero_mul]
    · rw [hu.1 k j (lt_of_lt_of_le hji hk), mul_zero]
  have hPdiag : ∀ i, P i i = 1 := by
    intro i
    show ∑ k, _ = _
    rw [Finset.sum_eq_single i]
    · rw [hy1 i, map_one, one_mul, hu.2]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hy0 i k hk, map_zero, zero_mul]
      · rw [hu.1 k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  let w := (diagGL n τ)⁻¹ * glIncl F n Yg * u * diagGL n τ
  have hw : ∀ i j, w.val i j =
      (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j := by
    intro i j
    simp only [w, ← map_inv, Units.val_mul, diagGL_val, Matrix.mul_assoc, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [Matrix.mul_apply]
    rfl
  have hwu : IsUpperUni w.val := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hw, hPlow i j hji, mul_zero, zero_mul]
    · rw [hw, hPdiag, mul_one, Units.inv_mul]
  have hwi : MatInt w.val := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hw]
      have := hyc i j hij
      rw [show (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j =
        (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j * P i j by ring]
      exact this
    · rw [hwu.2]; exact (Ohat F).one_mem
    · rw [hwu.1 i j hji]; exact (Ohat F).zero_mem
  refine ⟨Yg⁻¹, w, ⟨hwi, matInt_inv_of_upperUni w hwu hwi⟩, ?_⟩
  simp only [w, map_inv]
  group

end GlobalTheory.UnipApproxGL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdeleStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strongApproximation_upperUnitriangular_finiteAdeles : PIW.ClassFinD.UnipApprox := by
  first | exact @GlobalTheory.UnipApproxGL.unipApprox | exact GlobalTheory.UnipApproxGL.unipApprox | (intros; apply GlobalTheory.UnipApproxGL.unipApprox <;> assumption)
end
end
