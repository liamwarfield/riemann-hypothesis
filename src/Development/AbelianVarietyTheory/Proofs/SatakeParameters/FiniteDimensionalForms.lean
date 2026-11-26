module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgFormsFin

section General

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => maximalRealSubfield L

theorem ALint_le : ReciprocityTheory.Aut.ALint L ≤ Formalism.MainNotions.S.IntAf (L⁺) L := by
  rw [ReciprocityTheory.Aut.ALint, Subring.closure_le]
  rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem le_ALint : Formalism.MainNotions.S.IntAf (L⁺) L ≤ ReciprocityTheory.Aut.ALint L := by
  show Subring.closure _ ≤ _
  rw [Subring.closure_le]
  rintro x (⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)

theorem exists_approx {N : ℕ} (hN : 0 < N) {x : ReciprocityTheory.Aut.AL L} (hx : x ∈ ReciprocityTheory.Aut.ALint L) :
    ∃ a : 𝓞 L, ∃ r ∈ ReciprocityTheory.Aut.ALint L, x = ((a : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) + (N : ReciprocityTheory.Aut.AL L) * r := by
  obtain ⟨a, r, hr, e⟩ := PIW.AdelClassFin.dual_dense (L⁺) L N hN x (ALint_le L hx)
  exact ⟨a, r, le_ALint L hr, e⟩

theorem exists_class {N : ℕ} (hN : 0 < N) : ∃ (Q : Type) (_ : Finite Q) (c : ReciprocityTheory.Aut.AL L → Q),
    ∀ x ∈ ReciprocityTheory.Aut.ALint L, ∀ y ∈ ReciprocityTheory.Aut.ALint L, c x = c y →
      ∃ r ∈ ReciprocityTheory.Aut.ALint L, x - y = (N : ReciprocityTheory.Aut.AL L) * r := by
  classical
  have hN0 : Ideal.span {(N : 𝓞 L)} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have hfin : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hN0
  refine ⟨𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}, hfin, fun x =>
    if h : x ∈ ReciprocityTheory.Aut.ALint L then Ideal.Quotient.mk _ (exists_approx L hN h).choose else 0, ?_⟩
  intro x hx y hy e
  simp only [dif_pos hx, dif_pos hy] at e
  obtain ⟨r, hr, ex⟩ := (exists_approx L hN hx).choose_spec
  obtain ⟨s, hs, ey⟩ := (exists_approx L hN hy).choose_spec
  set a := (exists_approx L hN hx).choose
  set b := (exists_approx L hN hy).choose
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at e
  obtain ⟨d, hd⟩ := e
  have hab : a = b + (N : 𝓞 L) * d := by rw [← hd]; ring
  have hi : ∀ z : 𝓞 L, ((z : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) ∈ ReciprocityTheory.Aut.ALint L :=
    fun z => Subring.subset_closure (Or.inl ⟨z, rfl⟩)
  refine ⟨((d : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) + r - s, sub_mem (add_mem (hi d) hr) hs, ?_⟩
  have hinc : ((a : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) = ((b : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) +
      (N : ReciprocityTheory.Aut.AL L) * ((d : L) ⊗ₜ[L⁺] (1 : ReciprocityTheory.Aut.AFplus L)) := by
    rw [hab, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.add_tmul]
    push_cast
    rfl
  rw [ex, ey, hinc]
  ring

theorem exists_cover {N : ℕ} (hN : 0 < N) : ∃ J : Finset (GAf L n), ∀ u ∈ ReciprocityTheory.Aut.Umax L n,
    ∃ j ∈ J, ∃ κ, Formalism.L2.NG.Cong L n N κ ∧ u = j * κ := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := exists_class L hN
  let φ : GAf L n → Fin n → Fin n → Q := fun g i j => c ((g.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) i j)
  let rep : (Fin n → Fin n → Q) → GAf L n := fun q =>
    if h : ∃ u ∈ ReciprocityTheory.Aut.Umax L n, φ u = q then h.choose else 1
  have hfin : Fintype (Fin n → Fin n → Q) := Fintype.ofFinite _
  refine ⟨Finset.univ.image rep, fun u hu => ?_⟩
  have hex : ∃ w ∈ ReciprocityTheory.Aut.Umax L n, φ w = φ u := ⟨u, hu, rfl⟩
  have hrep : rep (φ u) = hex.choose := dif_pos hex
  obtain ⟨hj, hφ⟩ := hex.choose_spec
  rw [← hrep] at hj hφ
  set j := rep (φ u) with hjdef
  refine ⟨j, Finset.mem_image.2 ⟨φ u, Finset.mem_univ _, rfl⟩, j⁻¹ * u, ⟨mul_mem (inv_mem hj) hu, ?_⟩, by simp⟩
  intro a b
  have hdiff : ∀ k, ∃ r ∈ ReciprocityTheory.Aut.ALint L, (u.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) k b -
      (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) k b = (N : ReciprocityTheory.Aut.AL L) * r := fun k =>
    hc _ (hu k b) _ (hj k b) (congrFun (congrFun hφ k) b).symm
  choose r hr e using hdiff
  have hinv : (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) * (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hmat : (((j⁻¹ * u : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) - 1 =
      (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) *
        ((u.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) - (j.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L))) := by
    rw [Matrix.mul_sub, hinv, Subgroup.coe_mul, Units.val_mul]
  refine ⟨∑ k, (((j⁻¹ : GAf L n)).1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) a k * r k,
    sum_mem fun k _ => mul_mem (inv_mem hj a k) (hr k), ?_⟩
  have := congrFun (congrFun hmat a) b
  rw [Matrix.sub_apply, Matrix.mul_apply] at this
  rw [this, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, e k]
  ring

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def fixedForms (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W) (N : ℕ) : Submodule ℂ (GAf L n → W) where
  carrier := {f | (∀ (γ : ReciprocityTheory.Aut.GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
    ∀ κ, Formalism.L2.NG.Cong L n N κ → ∀ g, f (g * κ) = f g}
  zero_mem' := ⟨fun γ g => by simp, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨fun γ g => by simp [h1 γ g, h1' γ g], fun κ hκ g => by simp [h2 κ hκ g, h2' κ hκ g]⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨fun γ g => by simp [h1 γ g], fun κ hκ g => by simp [h2 κ hκ g]⟩

theorem fixedForms_finite [FiniteDimensional ℂ W] (ρ : Representation ℂ (ReciprocityTheory.Aut.GQ L n) W)
    (hT : ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : GAf L n) (u : GAf L n),
      t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : GAf L n) * t * u)
    {N : ℕ} (hN : 0 < N) : FiniteDimensional ℂ (fixedForms L n ρ N) := by
  classical
  obtain ⟨T, hT⟩ := hT
  obtain ⟨J, hJ⟩ := exists_cover L n hN
  let Φ : fixedForms L n ρ N →ₗ[ℂ] (↥(T ×ˢ J) → W) :=
    { toFun := fun f p => (f : GAf L n → W) (p.1.1 * p.1.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, t, u, ht, hu, rfl⟩ := hT g
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJ u hu
  have h0 : (f : GAf L n → W) (t * j) = 0 :=
    congrFun hf ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩⟩
  have e : (γ : GAf L n) * t * (j * κ) = ((γ : GAf L n) * (t * j)) * κ := by simp only [mul_assoc]
  show (f : GAf L n → W) _ = 0
  rw [e, f.2.2 κ hκ, f.2.1 γ, h0, map_zero]

end General

theorem finiteDimensional_forms : ∀ (D : D7) (n : ℕ) (a : AlgWt D.host.E n), (∃ T : Finset (GAf D.host.E n), ∀ g : GAf D.host.E n, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (t : GAf D.host.E n) (u : GAf D.host.E n), t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E n ∧ g = (γ : GAf D.host.E n) * t * u) → ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ AFall D.host.E n a.ρ ∧ ∀ κ, Cong D.host.E n N κ → ∀ g, f (g * κ) = f g}) := by
  intro D n a hT N hN
  have hW : FiniteDimensional ℂ a.W := a.alg.1
  have h := fixedForms_finite D.host.E n a.ρ hT hN
  refine Submodule.finiteDimensional_of_le (S₂ := fixedForms D.host.E n a.ρ N) (Submodule.span_le.2 ?_)
  rintro f ⟨hf, hκ⟩
  exact ⟨hf.1, hκ⟩

end GlobalTheory.AlgFormsFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne
open scoped TensorProduct

namespace GlobalTheory.RowTie.EigTwist

theorem roots_charpoly_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) :
    (u • M).charpoly.roots = M.charpoly.roots.map (· * u) := by
  have hM := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)
  have hc : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  suffices (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod by
    rw [this, roots_multiset_prod_X_sub_C]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hc]
  · refine Polynomial.funext fun x => ?_
    have h1 := congrArg (eval (x / u)) hM
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp
        field_simp
      · simp [Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
    simp
    field_simp

theorem roots_charpoly_smul {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (u : ℂ) : (u • f).charpoly.roots = f.charpoly.roots.map (· * u) := by
  rw [← LinearMap.charpoly_toMatrix (u • f) (Module.finBasis ℂ V),
    ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), map_smul, roots_charpoly_smul_matrix]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem eig_lpTw (x : WD h) {φ : Weil h} (hφ : deg φ = 1) (s : ℝ) :
    (x.lpTw s).eig φ = (x.eig φ).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) := by
  induction x using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.eig_mk, WD.eig_mk, WDRep.tw_ρ, hφ, zpow_one, roots_charpoly_smul]

theorem eig_lpChar (x y : WD h) (φ : Weil h) (hy : y.lpDim = 1) (c : ℂ) (hc : y.eig φ = {c}) :
    (x.lpChar y).eig φ = (x.eig φ).map (· * c) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk, Module.finrank_fin_fun] at hy
    subst hy
    rw [WD.eig_mk] at hc
    have hb : b.ρ φ = c • 1 := by
      have hp : (b.ρ φ).charpoly = X - C c := by
        rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic _), hc]
        simp
      have h3 := LinearMap.aeval_self_charpoly (b.ρ φ)
      rw [hp, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h3
      exact h3
    rw [WD.lpChar_mk, WD.eig_mk, WD.eig_mk, WDRep.tensor_ρ, hb]
    let e : (Fin n → ℂ) ⊗[ℂ] (Fin 1 → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
      (TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
        (TensorProduct.rid ℂ _)
    have he : e.conj (TensorProduct.map (a.ρ φ) (c • 1)) = c • a.ρ φ := by
      refine LinearMap.ext fun v => ?_
      obtain ⟨t, rfl⟩ := e.surjective v
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [LinearEquiv.symm_apply_apply]
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [e, smul_smul, mul_comm]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [← LinearEquiv.charpoly_conj e, he, roots_charpoly_smul]

end GlobalTheory.RowTie.EigTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
namespace GlobalTheory.RowLaws

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem tie_unit (T : WDTie N A) (w : PlE H) :
    (T.e w (A.lpUnr w {1})).unr ∧ (T.e w (A.lpUnr w {1})).lpDim = 1 ∧
      (T.e w (A.lpUnr w {1})).frobEig = {1} := by
  obtain ⟨h1, h2, h3⟩ := A.lpUnr_spec w {1} (by simp)
  refine ⟨(T.unr w _).1 h1, ?_, ?_⟩
  · rw [T.dim, h3]; rfl
  · rw [← T.frobEig w _ h1, h2]

theorem paramLaws_of_tie (T : WDTie N A) : ParamLaws N A := by
  intro w
  refine ⟨fun a b χ h => (T.e w).injective ?_, fun χ h => (T.e w).injective ?_,
    fun a χ s h => (T.e w).injective ?_, fun a b χ h hab => ?_, fun a b c h => (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h, T.sum, T.sum, T.char _ _ _ h, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h, T.zero]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _
      (WD.lpZero (h := N.plOm.2 w)) (WD.lpZero (h := N.plOm.2 w)) _ 0).2.2.2.2.1
  · rw [T.char _ _ _ h, T.tw, T.tw, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.1
  · apply (T.e w).injective
    have hχ : (T.e w χ).lpDim = 1 := by rw [T.dim, h]
    have := congrArg (T.e w) hab
    rw [T.char _ _ _ h, T.char _ _ _ h] at this
    exact GlobalTheory.T.weilDeligneParameter_tensor_oneDim_injective _ _ _ _ _ _ _ _ hχ this
  · have := congrArg (T.e w) h
    rw [T.sum, T.sum] at this
    exact GlobalTheory.T.directSum_cancel_right _ _ _ _ _ _ _ _ this

theorem cancel_of_tie (T : WDTie N A) : Cancel N A := fun w a b c h => (paramLaws_of_tie T w).2.2.2.2 a b c h

theorem charLaws_of_tie (T : WDTie N A) : CharLaws N A := by
  intro w a b χ χ' s h1 h2
  have h3 : A.lpDim (A.lpTw χ s) = 1 := by rw [A.lpDim_tw, h1]
  have h4 : A.lpDim (A.lpChar χ χ') = 1 := by rw [A.lpDim_char _ _ h2, h1]
  have h5 : A.lpDim (A.lpUnr w {1}) = 1 := (A.lpUnr_spec w {1} (by simp)).2.2
  refine ⟨(T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_,
    (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h1, T.sum, T.sum, T.char _ _ _ h1, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h1, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.1
  · rw [T.char _ _ _ h3, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.2.1
  · rw [T.char _ _ _ h2, T.char _ _ _ h1, T.char _ _ _ h4, T.char _ _ _ h2]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).2.2.2.1
  · rw [T.char _ _ _ h5]
    obtain ⟨u1, u2, u3⟩ := tie_unit T w
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _
      (T.e w a) (WD.lpZero (h := N.plOm.2 w)) _ 0).2.2.2.2.2 u1 u2 u3

end GlobalTheory.RowLaws


open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain in
theorem GlobalTheory.RowLaws.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A → GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧ GlobalTheory.RowTie.Cancel N A :=
  fun _ _ _ _ _ T => ⟨GlobalTheory.RowLaws.paramLaws_of_tie T, GlobalTheory.RowLaws.charLaws_of_tie T, GlobalTheory.RowLaws.cancel_of_tie T⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentificationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A →
      GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧
        GlobalTheory.RowTie.Cancel N A :=
  GlobalTheory.RowLaws.main
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SpehRigid

def seg {C : Type} (p : C × ℕ) : Multiset (C × ℤ) :=
  (Multiset.range p.2).map fun a : ℕ => (p.1, (p.2 : ℤ) - 1 - 2 * (a : ℤ))

theorem seg_nodup {C : Type} (p : C × ℕ) : (seg p).Nodup := by
  refine (Multiset.nodup_range _).map ?_
  intro a b h
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem mem_seg {C : Type} (p : C × ℕ) (c : C) (e : ℤ) :
    (c, e) ∈ seg p ↔ p.1 = c ∧ ∃ a : ℕ, a < p.2 ∧ (p.2 : ℤ) - 1 - 2 * (a : ℤ) = e := by
  simp only [seg, Multiset.mem_map, Multiset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨h1, a, ha, h2⟩
  · rintro ⟨h1, a, ha, h2⟩
    exact ⟨a, ha, h1, h2⟩

theorem count_seg {C : Type} [DecidableEq C] (p : C × ℕ) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (seg p).count (c, (d : ℤ) - 1) = (seg p).count (c, (d : ℤ) + 1) + if (c, d) = p then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup (seg_nodup p), Multiset.count_eq_of_nodup (seg_nodup p)]
  obtain ⟨c', d'⟩ := p
  have e1 : (c, (d : ℤ) - 1) ∈ seg (c', d') ↔ c' = c ∧ d ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  have e2 : (c, (d : ℤ) + 1) ∈ seg (c', d') ↔ c' = c ∧ d + 2 ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d - 2) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  simp only [e1, e2, Prod.mk.injEq]
  by_cases hc : c' = c
  · subst hc
    simp only [true_and]
    split_ifs <;> omega
  · simp [hc, Ne.symm hc]

theorem count_bind_seg {C : Type} [DecidableEq C] (P : Multiset (C × ℕ)) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (P.bind seg).count (c, (d : ℤ) - 1) = (P.bind seg).count (c, (d : ℤ) + 1) + P.count (c, d) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons p P ih =>
    rw [Multiset.cons_bind, Multiset.count_add, Multiset.count_add, ih, count_seg p c d hd, Multiset.count_cons]
    omega

theorem eq_of_bind_seg {C : Type} (P P' : Multiset (C × ℕ)) (h : ∀ p ∈ P, 1 ≤ p.2) (h' : ∀ p ∈ P', 1 ≤ p.2)
    (e : P.bind seg = P'.bind seg) : P = P' := by
  classical
  ext ⟨c, d⟩
  by_cases hd : 1 ≤ d
  · have h1 := count_bind_seg P c d hd
    have h2 := count_bind_seg P' c d hd
    rw [e] at h1
    omega
  · rw [Multiset.count_eq_zero_of_notMem fun hm => hd (h _ hm),
      Multiset.count_eq_zero_of_notMem fun hm => hd (h' _ hm)]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def flat (p : Formalism.BasicNotions.Part A.CG) : List ((Σ a : ℕ, A.CG a) × ℝ) :=
  (List.range p.d).map fun k : ℕ => (⟨p.a, p.π⟩, ((p.d : ℝ) - 1) / 2 - (k : ℝ))

theorem twSum_append (L L' : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    GlobalTheory.RowTie.twSum N A (L ++ L') w = A.lpSum (GlobalTheory.RowTie.twSum N A L w) (GlobalTheory.RowTie.twSum N A L' w) := by
  unfold GlobalTheory.RowTie.twSum
  induction L with
  | nil => rw [List.nil_append, List.foldr_nil, A.lpSum_comm, A.lpSum_zero]
  | cons p L ih => rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih, A.lpSum_assoc]

theorem spehLoc_eq (p : Formalism.BasicNotions.Part A.CG) (w : PlE H) :
    spehLoc N A p w = GlobalTheory.RowTie.twSum N A (flat N A p) w := by
  unfold spehLoc GlobalTheory.RowTie.twSum flat
  have hl : (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = (List.range p.d).map (fun a : ℕ => (a : ℝ)) := by
    simp [List.map_eq_flatMap]
  rw [hl, List.foldr_map, List.foldr_map]

theorem isoLoc_eq (P : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) :
    isoLoc N A P w = GlobalTheory.RowTie.twSum N A (P.flatMap (flat N A)) w := by
  induction P with
  | nil => rfl
  | cons p P ih => rw [List.flatMap_cons, twSum_append, ← ih, ← spehLoc_eq]; rfl

def toPair (p : Formalism.BasicNotions.Part A.CG) : (Σ a : ℕ, A.CG a) × ℕ := (⟨p.a, p.π⟩, p.d)

theorem toPair_injective : Function.Injective (toPair N A) :=
  Function.LeftInverse.injective (g := fun q => ⟨q.1.1, q.1.2, q.2⟩) fun _ => rfl

theorem coe_flatMap (P : List (Formalism.BasicNotions.Part A.CG)) :
    Multiset.ofList (P.flatMap (flat N A)) =
      ((Multiset.ofList (P.map (toPair N A))).bind seg).map fun q => (q.1, (q.2 : ℝ) / 2) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, ← Multiset.cons_coe, Multiset.cons_bind,
      Multiset.map_add]
    congr 1
    unfold seg flat toPair
    rw [Multiset.map_map, ← Multiset.map_coe]
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring

theorem isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' he
  have hpos : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ P.flatMap (flat N A), 1 ≤ q.1.1 := by
    intro P hP q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
    exact (hP p hp).1
  have hd : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ Multiset.ofList (P.map (toPair N A)), 1 ≤ q.2 := by
    intro P hP q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hq)
    exact (hP p hp).2.1
  have h1 := hR _ _ (hpos Pa h) (hpos Pa' h') (by simpa only [isoLoc_eq] using he)
  have h2 := Multiset.coe_eq_coe.2 h1
  rw [coe_flatMap, coe_flatMap] at h2
  have hinj : Function.Injective fun q : (Σ a : ℕ, A.CG a) × ℤ => (q.1, (q.2 : ℝ) / 2) := by
    intro q q' e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e1 e2
    refine Prod.ext e1 ?_
    have : (q.2 : ℝ) = q'.2 := by linarith
    exact_mod_cast this
  have h3 := eq_of_bind_seg _ _ (hd Pa h) (hd Pa' h') (Multiset.map_injective hinj h2)
  rw [← Multiset.map_coe, ← Multiset.map_coe] at h3
  exact Multiset.coe_eq_coe.1 (Multiset.map_injective (toPair_injective N A) h3)

end GlobalTheory.SpehRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowClose

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem isoLoc_eq_twSum_zero (P : List (Part A.CG)) (h : ∀ p ∈ P, p.d = 1) (w : PlE H) :
    isoLoc N A P w =
      GlobalTheory.RowTie.twSum N A (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))) w := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    have hp : p.d = 1 := h p (by simp)
    have h1 : spehLoc N A p w = A.lpTw (A.locG p.π w) 0 := by
      simp [spehLoc, hp, A.lpSum_zero]
    change A.lpSum (spehLoc N A p w) (isoLoc N A P w) = A.lpSum (A.lpTw (A.locG p.π w) 0) _
    rw [h1, ih fun q hq => h q (by simp [hq])]
    rfl

theorem isobaricCuspidalMultiplicityOne_of_twisted : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' hw
  have key := hR (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (Pa'.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h p hp).1)
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h' p hp).1)
    (hw.mono fun w e => by
      rw [← isoLoc_eq_twSum_zero N A Pa (fun p hp => (h p hp).2),
        ← isoLoc_eq_twSum_zero N A Pa' (fun p hp => (h' p hp).2), e])
  have back : ∀ P : List (Part A.CG), (∀ p ∈ P, p.d = 1) →
      (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))).map
        (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG)) = P := by
    intro P hP
    rw [List.map_map]
    conv_rhs => rw [← List.map_id P]
    refine List.map_congr_left fun p hp => ?_
    have := hP p hp
    obtain ⟨a, π, d⟩ := p
    simp only at this
    subst this
    rfl
  have := key.map (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG))
  rwa [back Pa (fun p hp => (h p hp).2), back Pa' (fun p hp => (h' p hp).2)] at this

end GlobalTheory.RowClose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowSizeOfUnitarySphericalComponent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowSizeClosing

theorem rowSize_of_unitarySphericalComponent :
    ∀ (D : D7), GlobalTheory.RowSatakeBound.UnitarySphericalComponent D.nd D.naut → GlobalTheory.RowCopy.RowSize D :=
  fun D h => by
    intro i σ hσ w hw hu α hα
    have hb := GlobalTheory.RowSatakeBound.rowSize_of_component D.nd D.naut h i σ hσ w hw hu α hα
    simpa only [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hb

end GlobalTheory.RowSizeClosing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isoLoc_perm {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) :
    isoLoc N A Pa w = isoLoc N A Pa' w := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
    simp only [isoLoc, List.foldr_cons] at ih ⊢
    rw [ih]
  | swap p q l =>
    simp only [isoLoc, List.foldr_cons]
    rw [← A.lpSum_assoc (spehLoc N A q w), A.lpSum_comm (spehLoc N A q w) (spehLoc N A p w), A.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem locV_eq_of_pt (i : N.Loc) {P P' : A.AV i} {x : N.X i} (hx : A.ptV i P = some x)
    (hx' : A.ptV i P' = some x) {w : PlE H} (hso : SplitOut N i w) (hg : ∀ k, w ∉ placesOver H.E (H.g k))
    (hd : w ∉ placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)) :
    A.locV i P w = A.locV i P' w := by
  set c : ℝ := (1 - (R.nV : ℝ)) / 2
  have u : A.unr (A.lpTw (A.locV i P w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P w hso.1 hso.2.2.2 hg hd)
  have u' : A.unr (A.lpTw (A.locV i P' w) c) :=
    (A.unr_tw _ _).2 (A.locV_unr i P' w hso.1 hso.2.2.2 hg hd)
  have h1 := congrArg Polynomial.roots ((A.pt_loc i P x hx w hso).symm.trans (A.pt_loc i P' x hx' w hso))
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at h1
  have e : A.lpTw (A.locV i P w) c = A.lpTw (A.locV i P' w) c := by
    rw [A.unr_eq_lpUnr _ u, A.unr_eq_lpUnr _ u', h1]
  have back : ∀ a : A.LP w, A.lpTw (A.lpTw a c) (-c) = a := fun a => by
    rw [A.lpTw_add, add_neg_cancel, A.lpTw_zero]
  rw [← back (A.locV i P w), e, back]

theorem locOfPt_of_splitBC : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  intro R H what₂ N A i hBC hS P P' x hx hx' w hw
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hd0 : (if N.l i = H.pde then H.pde' else H.pde) ≠ 0 := by
    split_ifs
    exacts [H.pde'_prime.ne_zero, H.pde_prime.ne_zero]
  have hfin : (placesOver H.E (N.l i) ∪ (N.S i : Set (PlE H)) ∪ (N.Q i : Set (PlE H)) ∪
      placesOver H.E (H.g 0) ∪ placesOver H.E (H.g 1) ∪
      placesOver H.E (if N.l i = H.pde then H.pde' else H.pde)).Finite := by
    refine ((((( placesOver_finite_of_ne_zero _ _ (N.lPrime i).out.ne_zero).union (N.S i).finite_toSet).union
      (N.Q i).finite_toSet).union (placesOver_finite_of_ne_zero _ _ (H.g_prime 0).ne_zero)).union
      (placesOver_finite_of_ne_zero _ _ (H.g_prime 1).ne_zero)).union (placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl H v → A.locV i P v = A.locV i P' v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => locV_eq_of_pt N A i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  have hperm := hS P P' hev Pa Pa' hPa hPa'
  rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw]
  exact isoLoc_perm N A hperm w

end GlobalTheory.RowTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  first | exact @GlobalTheory.RowTie.locOfPt_of_splitBC | exact GlobalTheory.RowTie.locOfPt_of_splitBC | (intros; apply GlobalTheory.RowTie.locOfPt_of_splitBC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
open CategoryTheory Limits AlgebraicGeometry IsLocalRing

noncomputable section
namespace GlobalTheory.NCyc.StrictLocLift

theorem lift_unique {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (g₁ g₂ : Q →+* T)
    (h₁ : g₁.comp tQ = b) (h₂ : g₂.comp tQ = b)
    (h : (residue T).comp g₁ = (residue T).comp g₂) : g₁ = g₂ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let G₁ : Q →ₐ[R] T := { g₁ with commutes' := fun r => DFunLike.congr_fun h₁ r }
  let G₂ : Q →ₐ[R] T := { g₂ with commutes' := fun r => DFunLike.congr_fun h₂ r }
  have := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).1 (a₁ := G₁) (a₂ := G₂) (by
    ext q; exact DFunLike.congr_fun h q)
  ext q; exact DFunLike.congr_fun this q

theorem lift_exists {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (ψ : Q →+* ResidueField T)
    (hψ : ψ.comp tQ = (residue T).comp b) :
    ∃ g : Q →+* T, g.comp tQ = b ∧ (residue T).comp g = ψ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let Ψ : Q →ₐ[R] ResidueField T := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  obtain ⟨G, hG⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).2 Ψ
  refine ⟨G.toRingHom, RingHom.ext fun r => G.commutes r, RingHom.ext fun q => ?_⟩
  exact DFunLike.congr_fun hG q

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isIndEtale {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [HenselianLocalRing T]
    (a : R →+* S) (b : R →+* T) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale a) (ψ : S →+* ResidueField T)
    (hψ : ψ.comp a = (residue T).comp b) : ∃ g : S →+* T, g.comp a = b := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := ha
  have hts' : ∀ j, (s.app j).hom.comp (t.app j).hom = a := fun j => by
    have := congrArg CommRingCat.Hom.hom (hts j).2
    simpa using this
  have hψj : ∀ j, (ψ.comp (s.app j).hom).comp (t.app j).hom = (residue T).comp b := fun j => by
    rw [RingHom.comp_assoc, hts' j, hψ]
  choose g hg using fun j => lift_exists (t.app j).hom (hts j).1 b (ψ.comp (s.app j).hom) (hψj j)
  have nat : ∀ {j k : J} (u : j ⟶ k), (g k).comp (D.map u).hom = g j := by
    intro j k u
    have ht : (D.map u).hom.comp (t.app j).hom = (t.app k).hom := by
      have := congrArg CommRingCat.Hom.hom (t.naturality u)
      simpa using this.symm
    have hs' : (s.app k).hom.comp (D.map u).hom = (s.app j).hom := by
      have e : D.map u ≫ s.app k = s.app j := by
        have := s.naturality u
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        exact this
      have := congrArg CommRingCat.Hom.hom e
      rwa [CommRingCat.hom_comp] at this
    apply lift_unique (t.app j).hom (hts j).1 b
    · rw [RingHom.comp_assoc, ht, (hg k).1]
    · exact (hg j).1
    · rw [← RingHom.comp_assoc, (hg k).2, RingHom.comp_assoc, hs', (hg j).2]
  let c : Cocone D :=
    { pt := CommRingCat.of T
      ι := { app := fun j => CommRingCat.ofHom (g j)
             naturality := fun j k u => by
               ext q
               simpa using DFunLike.congr_fun (nat u) q } }
  refine ⟨(hs.desc c).hom, ?_⟩
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  have hf : (hs.desc c).hom.comp (s.app j).hom = g j := by
    have := congrArg CommRingCat.Hom.hom (hs.fac c j)
    simpa [c] using this
  rw [← hts' j, ← RingHom.comp_assoc, hf, (hg j).1]

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isStrictHenselisation {R S T : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [CommRing T] [HenselianLocalRing T] [IsSepClosed (ResidueField T)]
    (a : R →+* S) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation a) (b : R →+* T) [IsLocalHom b] :
    ∃ g : S →+* T, g.comp a = b := by
  letI : Algebra R S := a.toAlgebra
  haveI : IsLocalHom (algebraMap R S) := ha.2.2.1
  obtain ⟨-, -, hsep⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable R S ha.2.2.2
  letI : Algebra (ResidueField R) (ResidueField T) := (ResidueField.map b).toAlgebra
  let ι : ResidueField S →ₐ[ResidueField R] ResidueField T := IsSepClosed.lift
  refine exists_ringHom_of_isIndEtale a b ha.2.2.2 (ι.toRingHom.comp (residue S)) (RingHom.ext fun r => ?_)
  have h1 : residue S (a r) = algebraMap (ResidueField R) (ResidueField S) (residue R r) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h1, ι.commutes]
  rfl

end GlobalTheory.NCyc.StrictLocLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLiftOfPairLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem pairs_of_thetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (h : thetaOf N A i σ P) : GlobalTheory.ThetaExh.Pairs N A i σ P := by
  obtain ⟨hne, hle⟩ := h
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hF
  exact ⟨f, hf, _, hle hF, fun h0 => hF0 (inner_self_eq_zero.1 h0)⟩

theorem splitLift_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.ThetaExh.SplitLift N A i :=
  fun _ _ _ N A i h σ P hθ => h σ P (pairs_of_thetaLift N A i σ P hθ)

end GlobalTheory.RowTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

open GlobalTheory.WeilDeligne

theorem tempered_of_rank_le_one (D : D7) (T : WDTie D.nd D.naut) (h1 : RankOneUnitary T)
    (a : ℕ) (π : D.naut.CG a) (ha : a ≤ 1) (w : PlE D.host) : D.naut.tempered (D.naut.locG π w) := by
  rw [T.tempered]
  have hd : (T.e w (D.naut.locG π w)).lpDim = a := by rw [T.dim, D.naut.locG_dim]
  refine GlobalTheory.T.tempered_of_lpDim_le_one_of_unit_eigenvalues _ _ _ _ _ _ (hd.le.trans ha) fun φ hφ α hα => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · have hc := WD.card_eig (T.e w (D.naut.locG π w)) φ
    rw [hd, Multiset.card_eq_zero] at hc
    rw [hc] at hα
    exact absurd hα (Multiset.notMem_zero α)
  · refine h1 π w φ.1 (deg_eq_one_iff.mp hφ) α ?_
    rw [WDTie.eig, WD.inePol_of_mem _ φ.2]
    exact hα

theorem tempered_all_ranks : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.RowTie.RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → GlobalTheory.RowCopy.TempCSD D ∧ GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
  intro D T h1 h2
  have key : GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
    intro a π hc hr w
    rcases Nat.lt_or_ge a 2 with ha | ha
    · exact tempered_of_rank_le_one D T h1 a π (by omega) w
    · exact h2 a π ha hc hr w
  exact ⟨fun a π _ hc hr w => key a π hc hr w, key⟩

end GlobalTheory.RowTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_of_rank_one_unitary : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.RowTie.RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → GlobalTheory.RowCopy.TempCSD D ∧ GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
  first | exact @GlobalTheory.RowTie.tempered_all_ranks | exact GlobalTheory.RowTie.tempered_all_ranks | (intros; apply GlobalTheory.RowTie.tempered_all_ranks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlaces
namespace GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isoLoc_perm {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) : isoLoc N A Pa w = isoLoc N A Pa' w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l =>
    simp only [List.foldr_cons]
    rw [← A.lpSum_assoc, ← A.lpSum_assoc, A.lpSum_comm (spehLoc N A y w)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.RowTie.repDet_split : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i →
    ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  intro R H what₂ N A i hBC hSp hRep P P' hP
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hperm := hSp P P' hP Pa Pa' hPa hPa'
  have hiso := GlobalTheory.RowTie.RepDet.isoLoc_perm N A hperm
  apply hRep P P'
  · intro w hw
    rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw, hiso w]
  · intro w hw
    rw [← (hPa.2.2.2.2.1 w hw).2, ← (hPa'.2.2.2.2.1 w hw).2, hiso w]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  first | exact @GlobalTheory.RowTie.repDet_split | exact GlobalTheory.RowTie.repDet_split | (intros; apply GlobalTheory.RowTie.repDet_split <;> assumption)
end
end
