module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientPointModuli
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointsAllNormalisationsFamilyUnif
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PureLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finite_of_eq_off {ι : Type} {a b : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite)
    (h : ∀ p, p ≠ q → b p = a p) : (Function.mulSupport b).Finite := by
  refine (ha.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    rw [Function.mem_mulSupport] at hp ⊢
    rwa [h p hpq] at hp

theorem exists_cofactor {ι : Type} {a : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite) :
    ∃ C : ℂ, ∀ b : ι → ℂ, (∀ p, p ≠ q → b p = a p) → ∏ᶠ p, b p = b q * C := by
  refine ⟨∏ᶠ (p) (_ : p ≠ q), a p, fun b hb => ?_⟩
  rw [← mul_finprod_cond_ne q (finite_of_eq_off q ha hb)]
  congr 1
  exact finprod_congr fun p => finprod_congr fun hp => hb p hp

private theorem lineAt_fin_eq_zero_and_inf_other_eq_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) (i : Fin m) (j : Fin n) :
    finPart D (lineAt θ τ z t i j) = 0 ∧ ∀ ρ, ρ ≠ τ → θ ρ (infPart D (lineAt θ τ z t i j)) = 0 := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨by simpa using congrFun (congrFun (hfin t) i) j, fun ρ hρ => ?_⟩
  have h := congrFun (congrFun (hcomp t ρ) i) j
  simp only [hρ, if_false] at h
  simpa [compAt] using h

private theorem ae_eq_zero_of_fin_zero_of_theta_inf_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (a : AE D) (h1 : finPart D a = 0)
    (h2 : ∀ ρ, θ ρ (infPart D a) = 0) : a = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact hσ.ext a h1 h2

variable {D : D7}

theorem wAt_lineAt_self {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) : wAt (.inr τ) (lineAt θ τ z t) = lineAt θ τ z t := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt]
  rw [← sub_eq_zero]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_sub, map_mul, hf]
  · intro ρ
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [(hid.2.2.2.2.2.2 θ hθ ρ).1, one_mul, sub_self]
    · rw [hr ρ hρ, mul_zero, sub_zero]

theorem wAt_lineAt_ne {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) {p : Place D} (hp : p ≠ .inr τ) : wAt p (lineAt θ τ z t) = 0 := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt, Matrix.zero_apply, Pi.zero_apply]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_mul, hf]
  · intro ρ
    rw [map_mul, map_mul]
    rcases p with v | τ'
    · rw [(hid.2.2.2.1 v).1, map_zero, zero_mul]
    · have hτ' : τ' ≠ τ := fun h => hp (by rw [h])
      by_cases hρ : ρ = τ'
      · subst hρ
        rw [hr ρ hτ', mul_zero]
      · rw [(hid.2.2.2.2.2.2 θ hθ ρ).2 τ' (Ne.symm hρ), zero_mul]

theorem finite_ne_of_eq_off {ι X : Type} {x y : ι → X} {f₀ : X} (q : ι) (hx : {p | x p ≠ f₀}.Finite)
    (h : ∀ p, p ≠ q → y p = x p) : {p | y p ≠ f₀}.Finite := by
  refine (hx.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    simp only [Set.mem_setOf_eq] at hp ⊢
    rwa [h p hpq] at hp

theorem isPure_linear_and_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → (∀ (x y z : Place D → WO S T → ℂ) (f g : WO S T → ℂ) (q : Place D) (c : ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) → z q = c • x q + y q → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • f + g)) ∧ ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → (∀ p, p ≠ .inr τ → x' p = x p) → x' (.inr τ) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ)) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (f + g) := by
    refine ⟨?_, ?_, hf.cont.add hg.cont, fun k L h1 h2 w => (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)⟩
    · intro γ w
      simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine ⟨?_, ?_, hf.cont.const_smul c, fun k L h1 h2 w => contDiff_const.mul (hf.smooth k L h1 h2 w)⟩
    · intro γ w
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    · obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hthH : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨fun x y z f g q c hx hy hyx hzx hzq => ?_, fun x x' f τ z hx hx' hxτ => ?_⟩
  · unfold IsPure IsRestricted at hx hy ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx
    obtain ⟨⟨hyl, -⟩, hgθ, hyw⟩ := hy
    have hzl : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (z p) := by
      intro p
      by_cases hp : p = q
      · rw [hp, hzq]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x q) (hxl q).1).2 q (hxl q)).2.1 c (y q) (hyl q)
      · rw [hzx p hp]
        exact hxl p
    refine ⟨⟨hzl, finite_ne_of_eq_off q hxfin hzx⟩,
      theta_add (theta_smul c hfθ) hgθ, fun w => ?_⟩
    obtain ⟨hxs, hxe⟩ := hxw w
    obtain ⟨-, hye⟩ := hyw w
    obtain ⟨C, hC⟩ := exists_cofactor q hxs
    have ha := hC (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) (fun _ _ => rfl)
    have hb := hC (fun p => ipO μ 𝓕 (y p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hyx p hp])
    have hd := hC (fun p => ipO μ 𝓕 (z p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hzx p hp])
    beta_reduce at ha hb hd
    refine ⟨finite_of_eq_off q hxs (fun p hp => by simp only [hzx p hp]), ?_⟩
    have hG := hthH w f₀ hf₀
    have hGq := hthH (wAt q w) f₀ hf₀
    have e1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • f) (heisO ψ S T w f₀) (theta_smul c hfθ) hG
    have e2 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w f₀) hfθ hG
    have e3 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • x q) (heisO ψ S T (wAt q w) f₀)
      (theta_smul c (hxl q).1) hGq
    have e4 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x q) (heisO ψ S T (wAt q w) f₀) (hxl q).1 hGq
    rw [hd, hzq, (e3.2.2.2.1 (y q) (hyl q).1).1, (e4.2.2.1 c).1, (e1.2.2.2.1 g hgθ).1, (e2.2.2.1 c).1,
      hxe, hye, ha, hb]
    ring
  · have hx1 := hx
    unfold IsPure IsRestricted at hx1 ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx1
    have hx'l : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (x' p) := by
      intro p
      by_cases hp : p = .inr τ
      · rw [hp, hxτ]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x (.inr τ)) (hxl _).1).2 (.inr τ) (hxl _)).2.2 τ rfl z
      · rw [hx' p hp]
        exact hxl p
    refine ⟨⟨hx'l, finite_ne_of_eq_off (.inr τ) hxfin hx'⟩,
      GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hfθ, fun w => ?_⟩
    obtain ⟨hxs, -⟩ := hxw w
    obtain ⟨C, hC⟩ := exists_cofactor (.inr τ) hxs
    have key : ∀ t : ℝ, ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀) =
        ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C := by
      intro t
      have hP := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx (lineAt θ τ z t)
      unfold IsPure at hP
      have e := hC (fun p => ipO μ 𝓕 (heisO ψ S T (wAt p (lineAt θ τ z t)) (x p)) (heisO ψ S T (wAt p w) f₀))
        (fun p hp => by simp only [wAt_lineAt_ne hθ τ z t hp, GlobalTheory.WeilVacMove.heisO_zero])
      beta_reduce at e
      rw [(hP.2.2 w).2, e, wAt_lineAt_self hθ τ z t]
    have hG := hthH w f₀ hf₀
    have h1 := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ f (heisO ψ S T w f₀) hfθ hG τ z).1
    have h2 := ((GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ (x (.inr τ)) (heisO ψ S T (wAt (.inr τ) w) f₀)
      (hxl _).1 (hthH _ _ hf₀) τ z).1).mul_const C
    have h3 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀))
        (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C) 0 := by
      simpa only [key] using h2
    have hd := hC (fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hx' p hp])
    beta_reduce at hd
    refine ⟨finite_of_eq_off (.inr τ) hxs (fun p hp => by simp only [hx' p hp]), ?_⟩
    rw [hd, hxτ, h1.unique h3]

end GlobalTheory.PureLinear

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivRealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensor_linear_in_factor_and_heisenbergDeriv_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → (∀ (x y z : Place D → WO S T → ℂ) (f g : WO S T → ℂ) (q : Place D) (c : ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) → z q = c • x q + y q → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • f + g)) ∧ ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → (∀ p, p ≠ .inr τ → x' p = x p) → x' (.inr τ) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ)) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  first | exact @GlobalTheory.PureLinear.isPure_linear_and_dRho | exact GlobalTheory.PureLinear.isPure_linear_and_dRho | (intros; apply GlobalTheory.PureLinear.isPure_linear_and_dRho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHkIsogEtaleUnique
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePointLaw

open GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_objMap_comp {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
    [IsAlgClosed k] [CharZero k]
    {o o₁ o₂ : Obj D l b s} {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ l.M') {C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)}
    (hC : ∀ x ∈ C, x ^ p ^ 2 = 1) {ψ₁ : o.t.G ⟶ o₁.t.G} {ψ₂ : o.t.G ⟶ o₂.t.G} (h₁ : IsHeckeIsog o o₁ p C ψ₁)
    [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left] (h₂ : IsHeckeIsog o o₂ p C ψ₂) :
    ∃ m : ObjMap o₁ o₂ (𝟙 _), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hfacts := obj_isAbelianScheme_dim_rigidified_sym
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁
  obtain ⟨hom₂, lin₂, sur₂, ker₂, weil₂, lev₂⟩ := h₂
  obtain ⟨hab, hdim, -, -⟩ := hfacts E H D l B b _ s o
  obtain ⟨hab₁, hdim₁, -, -⟩ := hfacts E H D l B b _ s o₁
  obtain ⟨hab₂, hdim₂, -, -⟩ := hfacts E H D l B b _ s o₂
  let P := polOf o.t o.proper o.ample o.ktriv hdim
  let P₁ := polOf o₁.t o₁.proper o₁.ample o₁.ktriv hdim₁
  let P₂ := polOf o₂.t o₂.proper o₂.ample o₂.ktriv hdim₂
  have := o₁.proper
  have := o₂.proper
  obtain ⟨α, hα⟩ := exists_fac hab.smooth ψ₁ ψ₂ fun x hx => (ker₂ x).2 ((ker₁ x).1 hx)
  have homα : IsMonHom α := hL.rigidity _ _ _ hab₁ hab₂ α (by
    rw [← IsMonHom.one_hom ψ₁, Category.assoc, hα, IsMonHom.one_hom])
  have : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have : Epi ψ₁ := Over.epi_of_epi_left ψ₁
  have linα : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a => by
    rw [← cancel_epi ψ₁, ← reassoc_of% lin₁, hα, reassoc_of% hα, lin₂]
  let ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  have hlam : LBIso (abelian₂ o₁.t.G (lbPow o₁.t.PP.L 1)) (abelian₂ o₁.t.G (o₂.t.PP.L.pull α.left)) :=
    lam_iso_of_weil_pairings hL k P₁ P₂ α p 1 homα hp inferInstance fun n x y c hn hc hx hy h => by
      have lift := exists_torsion_lift ρ sur₁ (fun x hx => hC x ((ker₁ x).1 hx)) hn (hc.pow_right 2)
      obtain ⟨x₀, tx, ex⟩ := lift x hx
      obtain ⟨y₀, ty, ey⟩ := lift y hy
      obtain rfl : x₀ ≫ ψ₁ = x := ex
      obtain rfl : y₀ ≫ ψ₁ = y := ey
      obtain ⟨c₀, hc₀, -⟩ := (hL.weil _ P n _).1 x₀ y₀ tx ty
      obtain ⟨c₀, rfl⟩ := (unitOn_bijective k).2 c₀
      have e : c = c₀ ^ p ^ 2 := (unitOn_bijective k).1
        (((hL.weil _ P₁ n _).1 _ _ hx hy).unique h (weil₁ n x₀ y₀ c₀ hc hc₀))
      have w := weil₂ n x₀ y₀ c₀ hc hc₀
      rw [← hα, ← Category.assoc, ← Category.assoc, ← e] at w
      rw [pow_one]
      exact w
  have hiso := iso_of_lam o₁.t o₂.t α linα hlam
  have := mono_of_kTriv α o₁.t.PP.isLB o₂.t.PP.isLB hiso o₁.ktriv
  have : IsIso α := isIso_of_mono α hab₂.smooth fun y => by
    obtain ⟨x, rfl⟩ := sur₂ y
    exact ⟨x ≫ ψ₁, by rw [Category.assoc, hα]⟩
  have : IsMonHom (asIso α).hom := homα
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  refine ⟨{ cm := CubeMap.ofHom α, cart := isGrpPullback_of_iso (asIso α), base := rfl
            act := fun a => congrArg (fun q => q.left) (linα a)
            lin := isPullCubical_of_iso hL.globalFns hab₁ α _ _ hiso
            eta := fun a => ?_, etaA := fun a => ?_ }, congrArg (fun q => q.left) hα⟩
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).1, ← (lev₂ p₀ hp₀ a).1, ← hα, ← Category.assoc]; rfl
  · rw [Category.id_comp, ← (lev₁ p₀ hp₀ a).2, ← (lev₂ p₀ hp₀ a).2, ← hα, ← Category.assoc]; rfl

theorem exists_transfer_fst
    {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} (u : Obj D l b sX) {k : Type} [Field k]
    {s : Sp k ⟶ Sp B} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      e.hom ≫ pullback.fst _ _ = m.toSABMap.φ ∧
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c => weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart
      ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, m.cart.1.isoPullback_hom_fst, m.cart.1.isoPullback_hom_snd, fun x => ?_,
    fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

theorem exists_etale_isHkIsog (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (hC : Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C) :
    ∃ (y₁ : Sp k ⟶ Xo.X) (ψ₁ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁)
      (f₁ : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G)),
      IsHkIsog p y y₁ C ψ₁ f₁ ∧ IsFinite ψ₁ ∧ Etale ψ₁ ∧ Surjective ψ₁ ∧
      ∀ y₂ ψ₂ f₂, IsHkIsog p y y₂ C ψ₂ f₂ → y₂ = y₁ ∧ ψ₂ ≫ pullback.fst _ _ = ψ₁ ≫ pullback.fst _ _ := by
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hComp := ObjMaps.id_comp_cancel
  obtain ⟨c₁, c₂, c₃, c₄, c₅, -⟩ := hC
  have : CharZero k := charZero_of_injective_ringHom (Spec.preimage (y ≫ Xo.s)).hom.injective
  have pull : ∀ y' : Sp k ⟶ Xo.X, y' ≫ Xo.s = y ≫ Xo.s →
      ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') := fun y' h =>
    obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
      (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  obtain ⟨o, ⟨m⟩⟩ := pull y rfl
  obtain ⟨ρ, e, -, e₁, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_fst Xo.univ m
  let C' : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G) := C.comap ρ.toMonoidHom
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun _ => Iff.rfl
  obtain ⟨hC', o₁, ψ₁, h₁, hfin, het, hsur⟩ := exists_isHeckeIsog hL obj_isAbelianScheme_dim_rigidified_sym
    (exists_tateIso_heckeQuotient SimAlg.sim_group) (exists_heckeQuotient_triple_of_laws hL)
    (weilIs_along_hom hL.globalFns) LieEtale.lieMult_iff_of_etale o 𝔓 p h𝔓 hco hp
    hp𝔓 hpM C' (fun x hx a => (mem _).2 (by rw [e₃]; exact c₁ _ hx a))
    (fun J hJ x hx => c₂ J hJ fun a ha => (e₃ a x).symm.trans (by rw [hx a ha, map_one]))
    (fun x hx a ha => ρ.injective ((e₃ a x).trans ((c₃ hx a ha).trans (map_one ρ).symm)))
    (fun x hx x' hx' => by
      have := (e₄ ((p : ℤ) ^ 2) x x' 1).2
        ((congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) (ρ x) (ρ x')) unitOn_one).mpr (c₄ _ hx _ hx'))
      rw [Nat.cast_pow]
      exact (congrArg (Out.WeilIs _ _ ((p : ℤ) ^ 2) x x') unitOn_one).mp this)
    ((Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)).trans c₅)
  obtain ⟨y₁, ⟨hy₁, ⟨m₁⟩⟩, huniq⟩ := Xo.rep _ (y ≫ Xo.s) inferInstance o₁
  obtain ⟨ρ₁, f, f₀, f₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_fst Xo.univ m₁
  have h₁' := h₁
  obtain ⟨hom₁, lin₁, sur₁, ker₁, weil₁, lev₁⟩ := h₁'
  let σ : (𝟙_ (Over (Sp k)) ⟶ o.t.G) →* (𝟙_ (Over (Sp k)) ⟶ o₁.t.G) :=
    MonoidHom.mk' (fun z => z ≫ ψ₁) fun a c => MonObj.mul_comp a c ψ₁
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ ψ₁) := fun x => congrArg (fun z => ρ₁ (z ≫ ψ₁)) (ρ.symm_apply_apply x)
  refine ⟨y₁, e.inv ≫ ψ₁.left ≫ f.hom, ψp, ⟨hy₁, ?_, fun x => ?_, fun a x => ?_, fun z => ?_,
    Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩, inferInstance, inferInstance,
    inferInstance, ?_⟩
  · rw [Category.assoc, Category.assoc, f₁, Over.w, Iso.inv_comp_eq, e₁]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [hψ, e₂, f₂, Category.assoc, Iso.hom_inv_id_assoc, Over.comp_left, Category.assoc]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, lin₁, Category.assoc]
  · obtain ⟨z, rfl⟩ := ρ₁.surjective z
    obtain ⟨x, rfl⟩ := sur₁ z
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, ker₁, mem]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    exact (f₄ _ _ _ _).1 (weil₁ n x x' c hn ((e₄ _ _ _ _).2 h))
  · rw [← e₅, ← e₆, hψ, hψ, (lev₁ p' hp' a).1, (lev₁ p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩
  · rintro y₂ ψ ψq ⟨hy₂, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩
    obtain ⟨o₂, ⟨m₂⟩⟩ := pull y₂ hy₂
    obtain ⟨ρ₂, r, r₀, r₁, r₂, r₃, r₄, r₅, r₆⟩ := exists_transfer_fst Xo.univ m₂
    let ψ₂ : o.t.G ⟶ o₂.t.G := Over.homMk (e.hom ≫ ψ ≫ r.inv) (by
      rw [← r₁, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, g₁, e₁])
    have hψ : ∀ x, ρ₂ (x ≫ ψ₂) = ψq (ρ x) := fun x => fibPt_injective _ (by
      rw [r₂, ← g₂, e₂]
      show (x.left ≫ e.hom ≫ ψ ≫ r.inv) ≫ r.hom = _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have hab := isAbelianScheme_of_proper o.t o.proper
    have hab₂ := isAbelianScheme_of_proper o₂.t o₂.proper
    have := o₂.proper
    have one : ∀ (G : Over (Sp k)) [GrpObj G], (1 : 𝟙_ (Over (Sp k)) ⟶ G) = η[G] := fun G _ => by
      rw [Hom.one_def]; simp
    have h₂ : IsHeckeIsog o o₂ p C' ψ₂ := by
      refine ⟨hL.rigidity _ _ _ hab hab₂ ψ₂ ?_, fun a => hom_ext_pts hab.smooth fun x => ρ₂.injective ?_,
        fun z => ?_, fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ⟨ρ₂.injective ?_, ρ₂.injective ?_⟩⟩
      · rw [← one, ← one]
        exact ρ₂.injective (by rw [hψ, map_one, map_one, map_one])
      · rw [← Category.assoc, ← Category.assoc, hψ, r₃, hψ, e₃, g₃]
      · obtain ⟨x, hx⟩ := g₄ (ρ₂ z)
        obtain ⟨x, rfl⟩ := ρ.surjective x
        exact ⟨x, ρ₂.injective ((hψ x).trans hx)⟩
      · rw [mem, ← g₅, MonoidHom.mem_ker, ← hψ, map_eq_one_iff _ ρ₂.injective]
      · refine (r₄ _ _ _ _).2 ?_
        rw [hψ, hψ]
        exact g₆ n _ _ c hn ((e₄ _ _ _ _).1 h)
      · rw [hψ, e₅, r₅]; exact (g₇ p' hp' a).1
      · rw [hψ, e₆, r₆]; exact (g₇ p' hp' a).2
    obtain ⟨m', hm'⟩ := exists_objMap_comp hp hpM hC' h₁ h₂
    obtain ⟨m'', hm''⟩ := ((hComp E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y₂ (𝟙 _) m₂).1 m'
    have hy : 𝟙 _ ≫ y₂ = y₁ := huniq _ ⟨by rw [Category.id_comp, hy₂], ⟨m''⟩⟩
    refine ⟨(Category.id_comp _).symm.trans hy, ?_⟩
    have hφ : m''.toSABMap.φ = m₁.toSABMap.φ := by
      clear_value ψp σ
      subst hy
      exact objMap_unique_of_field hL.serre m'' m₁
    rw [Category.assoc, Category.assoc, f₀, ← hφ, hm'', reassoc_of% hm', ← r₀]
    show _ = e.inv ≫ (e.hom ≫ ψ ≫ r.inv) ≫ _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem isHkIsog_etale_unique (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    {k : Type} [Field k] [IsAlgClosed k] {y y₁ : Sp k ⟶ Xo.X} {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)}
    (hC : Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C)
    {ψ₁ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y₁}
    {f₁ : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y₁ ⟶ Xo.univ.t.G)} (h₁ : IsHkIsog p y y₁ C ψ₁ f₁) :
    (IsFinite ψ₁ ∧ Etale ψ₁ ∧ Surjective ψ₁) ∧
      (∀ y₂ ψ₂ f₂, IsHkIsog p y y₂ C ψ₂ f₂ → y₂ = y₁) ∧ ∀ ψ₂ f₂, IsHkIsog p y y₁ C ψ₂ f₂ → ψ₂ = ψ₁ := by
  obtain ⟨y₀, ψ₀, f₀, h₀, a, b, c, hu⟩ := exists_etale_isHkIsog Xo h𝔓 hco hp hp𝔓 hpM y C hC
  obtain ⟨rfl, -⟩ := hu _ _ _ h₁
  have key : ∀ ψ₂ f₂, IsHkIsog p y y₁ C ψ₂ f₂ → ψ₂ = ψ₀ := fun ψ₂ f₂ h₂ =>
    pullback.hom_ext (hu _ _ _ h₂).2 (h₂.2.1.trans h₀.2.1.symm)
  obtain rfl := key _ _ h₁
  exact ⟨⟨a, b, c⟩, fun _ _ _ h => (hu _ _ _ h).1, key⟩

end GlobalTheory.HeckePointLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ConjHol
variable {D : D7} {S T : HSp D}

theorem gram_conj_emb (C : Ctx S T) (hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ) (ρ : D.what₂.Tau)
    (M : Matrix (Fin T.rank) (Fin T.rank) ℂ) :
    FD.gram (C.m.e ρ).1 C.X.Gm (M.map (starRingEnd ℂ)) = Mᴴ * gramAt D T ρ * M := by
  ext a b
  have hh : ∀ i k, conj (gramAt D T ρ k i) = gramAt D T ρ i k := fun i k => by
    have := congrFun (congrFun (hH ρ) i) k
    rwa [Matrix.conjTranspose_apply] at this
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.map_apply, C.m.e_emb, C.m.gT, Matrix.transpose_apply,
    NumberField.ComplexEmbedding.conjugate_coe_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [gramAt, Matrix.map_apply] at hh ⊢
  simp only [Complex.conj_conj, hh, Finset.sum_mul, RCLike.star_def]
  rw [Finset.sum_comm]

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

theorem unitFr_conj_moved : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → (∀ a, GlobalTheory.HolRead.IsUnitFr C.X (C.xB (C.mvB a B))) ∧ (∀ y, GlobalTheory.HolRead.IsUnitFr C.X y → ∃ a ∈ GinfC T, C.xB (C.mvB a B) = y) ∧ (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, C.xB (C.mvB a B) = C.xB (C.mvB a' B) → a = a') := by
  intro D S T C B hB
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hT := GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C
  have hH : ∀ τ, (gramAt D T τ)ᴴ = gramAt D T τ := fun τ => (R.1 τ).1
  refine ⟨fun a => ?_, fun y hy => ?_, fun a ha a' ha' h => ?_⟩
  · exact (hT.2 _ ((hT.2 B hB).2.2.2.2.2 a).1).1
  · let Y : C.Bas := fun ρ => (FD.mat y (C.m.e ρ)).map (starRingEnd ℂ)
    have hY : ∀ ρ, (Y ρ)ᴴ * gramAt D T ρ * Y ρ = sgnM C.X := by
      intro ρ
      rw [← gram_conj_emb C hH ρ]
      have e : (Y ρ).map (starRingEnd ℂ) = FD.mat y (C.m.e ρ) := by
        ext i j; simp [Y]
      rw [e]
      exact hy (C.m.e ρ)
    have hu : ∀ ρ, Y ρ * (B ρ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
      intro ρ
      have hd := isUnit_det_B C hB ρ
      have hd' : IsUnit (B ρ)ᴴ.det := by rw [det_conjTranspose]; exact hd.star
      show (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) = gramAt D T ρ
      have e1 : (Y ρ * (B ρ)⁻¹)ᴴ * gramAt D T ρ * (Y ρ * (B ρ)⁻¹) =
          ((B ρ)⁻¹)ᴴ * ((Y ρ)ᴴ * gramAt D T ρ * Y ρ) * (B ρ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [e1, hY, ← hB ρ, conjTranspose_nonsing_inv]
      simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hd', Matrix.one_mul]
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
    obtain ⟨a, ha, hau⟩ := R.2.1 (fun ρ => Y ρ * (B ρ)⁻¹) hu
    refine ⟨a, ha, ?_⟩
    have hm : ∀ ρ, C.mvB a B ρ = Y ρ := by
      intro ρ
      simp only [Ctx.mvB]
      rw [show compAt C.θ ρ (mt T a) = Y ρ * (B ρ)⁻¹ from hau ρ, Matrix.mul_assoc,
        nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
    funext σ i j
    obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
    simp only [Ctx.xB, Equiv.symm_apply_apply, hm, Y, Matrix.map_apply, Complex.conj_conj, FD.mat, Matrix.of_apply]
  · have hm : ∀ ρ, C.mvB a B ρ = C.mvB a' B ρ := by
      intro ρ
      ext i j
      have := congrFun (congrFun (congrFun h (C.m.e ρ)) i) j
      simp only [Ctx.xB, Equiv.symm_apply_apply] at this
      simpa using congrArg (starRingEnd ℂ) this
    refine R.2.2.1 a ha a' ha' fun ρ => ?_
    have e := congrArg (· * (B ρ)⁻¹) (hm ρ)
    simp only [Ctx.mvB, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_B C hB ρ), Matrix.mul_one] at e
    exact e

end GlobalTheory.AdSpan.ConjHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateModel_unitFrames_eq_movedOrthonormalFrames : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → (∀ a, GlobalTheory.HolRead.IsUnitFr C.X (C.xB (C.mvB a B))) ∧ (∀ y, GlobalTheory.HolRead.IsUnitFr C.X y → ∃ a ∈ GinfC T, C.xB (C.mvB a B) = y) ∧ (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, C.xB (C.mvB a B) = C.xB (C.mvB a' B) → a = a') := by
  first | exact @GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved | exact GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved | (intros; apply GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIff
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.PairBC

section General

variable {S S' : Scheme.{0}} {j : S' ⟶ S}

theorem exists_proj {X : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (w : S' ⟶ X) (h : w = j ≫ x) :
    ∃ π : pullback G.hom w ⟶ pullback G.hom x, π ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j ∧
      IsGrpPullback ((Over.pullback w).obj G) ((Over.pullback x).obj G) j π := by
  have e : pullback.fst G.hom w ≫ G.hom = (pullback.snd _ _ ≫ j) ≫ x := by
    rw [Category.assoc, ← h, pullback.condition]
  exact ⟨pullback.lift _ _ e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G _).congr h (pullback.lift_fst _ _ e).symm) (pullback.lift_snd _ _ _)⟩

theorem id_pow_left {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {π : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G j π) (N : ℕ) : (𝟙 G' ^ N).left ≫ π = π ≫ (𝟙 G ^ N).left := by
  let U : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk π h.1.w
  have e : pushHom h G' (𝟙 G') = U := Over.OverMorphism.ext (Category.id_comp π)
  have e' : pushHom h G' (𝟙 G' ^ N) = U ≫ 𝟙 G ^ N := by
    rw [map_pow, e, MonObj.comp_pow, Category.comp_id]
  exact congrArg (fun u => u.left) e'

theorem eq_iff [Flat j] [Surjective j] {A B : Over S} {A' B' : Over S'} {α : A'.left ⟶ A.left}
    {β : B'.left ⟶ B.left} (hα : IsPullback α A'.hom A.hom j) (hβ : IsPullback β B'.hom B.hom j)
    {u v : A ⟶ B} {u' v' : A' ⟶ B'} (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ β = α ≫ v.left) :
    u = v ↔ u' = v' := by
  have : Flat α := MorphismProperty.of_isPullback (P := @Flat) hα.flip ‹_›
  have : Surjective α := MorphismProperty.of_isPullback (P := @Surjective) hα.flip ‹_›
  have : Epi α := Flat.epi_of_flat_of_surjective α
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (hβ.hom_ext (hu.trans hv.symm) (by rw [Over.w, Over.w]))
  · rintro rfl
    exact Over.OverMorphism.ext ((cancel_epi α).1 (hu.symm.trans hv))

theorem comp_sq {A B C : Over S} {A' B' C' : Over S'} {α : A'.left ⟶ A.left} {β : B'.left ⟶ B.left}
    {δ : C'.left ⟶ C.left} {u : A ⟶ B} {v : B ⟶ C} {u' : A' ⟶ B'} {v' : B' ⟶ C'}
    (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ δ = β ≫ v.left) :
    (u' ≫ v').left ≫ δ = α ≫ (u ≫ v).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% hu]

theorem map_sq {X : Scheme.{0}} {G : Over X} {x : S ⟶ X} {w : S' ⟶ X} (π : pullback G.hom w ⟶ pullback G.hom x)
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _) (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j) (a : G ⟶ G) :
    ((Over.pullback w).map a).left ≫ π = π ≫ ((Over.pullback x).map a).left := by
  apply pullback.hom_ext <;>
    simp [h₁, h₂, reassoc_of% h₁, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

end General

theorem exists_isBC_and_isPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w'
  refine ⟨fun hw hw' f => ?_, fun f f' g g' N hf hf' => ?_⟩
  · obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hw
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hw'
    have e : (π ≫ f.left) ≫ (Fib Xo x').hom = (Fib Xo w).hom ≫ spMap φ :=
      (Category.assoc _ _ _).trans ((congrArg (π ≫ ·) (Over.w f)).trans hπ.1.w)
    refine ⟨Over.homMk (hπ'.1.lift _ _ e) (hπ'.1.lift_snd _ _ e), hw, hw', fun ρ ρ' q₁ q₂ q₁' q₂' => ?_⟩
    obtain rfl : ρ = π := pullback.hom_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
    obtain rfl : ρ' = π' := pullback.hom_ext (q₁'.trans p₁'.symm) (q₂'.trans p₂'.symm)
    exact hπ'.1.lift_fst _ _ e
  · have := FieldBaseChange.flat_spMap φ
    have := FieldBaseChange.surjective_spMap φ
    obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hf.1
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hf.2.1
    have e := hf.2.2 π π' p₁ p₂ p₁' p₂'
    have e' := hf'.2.2 π' π p₁' p₂' p₁ p₂
    refine and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ hπ' g f e.symm).symm
      (and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ' hπ g' f' e'.symm).symm
      (and_congr (eq_iff hπ.1 hπ.1 (comp_sq e e') (id_pow_left hπ N))
      (and_congr (eq_iff hπ'.1 hπ'.1 (comp_sq e' e) (id_pow_left hπ' N))
      (and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_)))))
    · exact eq_iff hπ.1 hπ'.1 (comp_sq (map_sq π p₁ p₂ _) e)
        (comp_sq (u := f) (u' := g) (v := (Over.pullback x').map _) (v' := (Over.pullback w').map _) e
          (map_sq π' p₁' p₂' _))
    · exact eq_iff hπ'.1 hπ.1 (comp_sq (map_sq π' p₁' p₂' _) e')
        (comp_sq (u := f') (u' := g') (v := (Over.pullback x).map _) (v' := (Over.pullback w).map _) e'
          (map_sq π p₁ p₂ _))

end GlobalTheory.HkIntegral.PairBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFibreMapBaseChangeAndIsogenyPairIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreMap_baseChange_and_isogenyPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  first | exact @GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | exact GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff | (intros; apply GlobalTheory.HkIntegral.PairBC.exists_isBC_and_isPair_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjRowLevel

private theorem inner_R_eq_inner_R_inv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a : X.B.I.GA)
    (x z : X.B.I.L2 X.B.μf X.B.fund) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨h1, hmul, hnorm, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  let L : X.B.I.L2 X.B.μf X.B.fund →ₗᵢ[ℂ] X.B.I.L2 X.B.μf X.B.fund :=
    { toLinearMap := (X.B.R a⁻¹ : X.B.I.L2 X.B.μf X.B.fund →ₗ[ℂ] X.B.I.L2 X.B.μf X.B.fund)
      norm_map' := hnorm a⁻¹ }
  have hback : X.B.R a⁻¹ (X.B.R a z) = z := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, inv_mul_cancel, h1]
    rfl
  calc ⟪x, X.B.R a z⟫_ℂ = ⟪L x, L (X.B.R a z)⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
      show ⟪X.B.R a⁻¹ x, X.B.R a⁻¹ (X.B.R a z)⟫_ℂ = _
      rw [hback]

private theorem e_inv_mul_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2)
    (y : X.B.I.Gf) : X.B.e (k⁻¹ * y) = X.chi2 k * X.B.e y := by
  classical
  obtain ⟨_, hmulK, hinvK, hchi, hnorm⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have he : ∀ z, X.B.e z = if z ∈ X.K2 then star (X.chi2 z) / ((X.B.μf X.K2).toReal : ℂ) else 0 :=
    X.e_eq
  have hunit : X.chi2 k * star (X.chi2 k) = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hnorm k hk]
    norm_num
  by_cases hy : y ∈ X.K2
  · have hky : k⁻¹ * y ∈ X.K2 := hmulK _ (hinvK _ hk) _ hy
    have hsplit : X.chi2 y = X.chi2 k * X.chi2 (k⁻¹ * y) := by
      rw [← hchi _ hk _ hky, mul_inv_cancel_left]
    rw [he, he, if_pos hky, if_pos hy, hsplit, star_mul']
    linear_combination (-(star (X.chi2 (k⁻¹ * y)) / ((X.B.μf X.K2).toReal : ℂ))) * hunit
  · have hky : k⁻¹ * y ∉ X.K2 := fun h => hy (by simpa using hmulK _ hk _ h)
    rw [he, he, if_neg hky, if_neg hy, mul_zero]

theorem reg_comp_Re {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨-, hmul, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  ext1 y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_R_eq_inner_R_inv X, X.B.Re_spec.2, X.B.Re_spec.2]
  have hstep : ∀ g : X.B.I.Gf,
      ⟪X.B.R (1, k)⁻¹ x, X.B.R (1, g) y⟫_ℂ = ⟪x, X.B.R (1, k * g) y⟫_ℂ := by
    intro g
    have hprod : (((1 : X.B.I.Ginf), k * g) : X.B.I.GA) = (1, k) * (1, g) := by simp
    rw [hprod, hmul, ContinuousLinearMap.comp_apply]
    exact (inner_R_eq_inner_R_inv X (1, k) x _).symm
  simp_rw [hstep]
  have hinv := integral_mul_left_eq_self (μ := X.B.μf)
    (fun g' => X.B.e (k⁻¹ * g') * ⟪x, X.B.R (1, g') y⟫_ℂ) k
  simp only [inv_mul_cancel_left] at hinv
  rw [hinv]
  simp_rw [e_inv_mul_eq_chi2_mul X k hk, mul_assoc]
  exact integral_const_mul _ _
private theorem contRep_mul_right_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Φ : X.B.Hs →L[ℂ] L2X X)
    (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) (v : X.B.Hs) {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ v) ψ) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    ∀ z, ψ (z * ((1 : X.B.I.Ginf), κ)) = X.chi2 κ * ψ z := by
  obtain ⟨A, -, hA⟩ := Submodule.mem_map.1 hΦ
  have hΦv : Φ v = X.B.Re (A v) := by
    rw [← hA]
    rfl
  have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1 : X.B.I.Ginf), κ)
  have hR : X.B.R ((1 : X.B.I.Ginf), κ) (Φ v) = X.chi2 κ • Φ v := by
    rw [hΦv, ← ContinuousLinearMap.comp_apply, reg_comp_Re X κ hκ, ContinuousLinearMap.smul_apply]
  rw [hR] at h1
  have h2 := Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 κ) hψ
  have heq := Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 h2
  intro z
  simpa using congrFun heq z

theorem conjMap_level : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ _ _ t c _ hconj _ Φ hΦ hcont u k hk g
  obtain ⟨ψ, hψ⟩ := hcont u
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hmem, hval⟩ := hconj k
  have hk' : ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧
      ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hmem.1 hk
  have hv := hval hk
  obtain ⟨hp1, hp2⟩ := hk'
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 := ⟨_, rfl⟩
  have hq : (iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹) = ((1 : X.B.I.Ginf), κ) := Prod.ext hp1 hκdef.symm
  have hκ : κ ∈ X.K2 := by
    rw [hκdef]
    exact hp2
  have hv' : star (X.chi2 κ) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k := by
    rw [hκdef]
    exact hv
  have hsplit : (iotaX X h).toMulEquiv (g * k * t⁻¹) =
      (iotaX X h).toMulEquiv (g * t⁻¹) * ((1 : X.B.I.Ginf), κ) := by
    rw [← hq]
    calc (iotaX X h).toMulEquiv (g * k * t⁻¹)
        = (iotaX X h).toMulEquiv (g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹)) := by
          rw [show g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹) = g * k * t⁻¹ by group]
      _ = _ := map_mul _ _ _
  change star (ψ ((iotaX X h).toMulEquiv (g * k * t⁻¹))) = _ * star (ψ ((iotaX X h).toMulEquiv (g * t⁻¹)))
  rw [hsplit, contRep_mul_right_eq_chi2_mul X Φ hΦ _ hψ κ hκ, star_mul', hv']

end GlobalTheory.ConjRowLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedIntertwiner_hasColumnLevel : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  first | exact @GlobalTheory.ConjRowLevel.conjMap_level | exact GlobalTheory.ConjRowLevel.conjMap_level | (intros; apply GlobalTheory.ConjRowLevel.conjMap_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsProperModelOfExtendsFibreIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsProperModelOfExtendsFibreIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem isProper_of_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  intro E _ _ _ H Dw l Xo T x x' G G' t t' m₁ m₂ n₁ n₂ f f' F N ⟨ψ, _, hψ, hc⟩ hN hpos hG
  have hU : IsAbelianScheme Xo.univ.t.G :=
    ⟨Xo.univ.t.semi.comm, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩
  have hA : IsAbelianScheme (Fib Xo x') := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback x' _ hU
  have hB : IsAbelianScheme G.G := ⟨G.semi.comm, G.semi.smooth, hG, G.semi.geomConnected⟩
  have hch : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have hu : IsUnit (N : Γ(Sp T.Fr, ⊤)) := by
    have h0 : IsUnit (N : T.Fr) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hpos.ne')
    have := h0.map (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨-, -, -, hs⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ (Fib Xo x') N hA hu
  have hl : f'.left ≫ f.left = (𝟙 (Fib Xo x') ^ N).left := congrArg (·.left) hN
  have hf : Function.Surjective f.left := by
    intro y
    obtain ⟨z, hz⟩ := hs.1 y
    refine ⟨f'.left z, ?_⟩
    rw [← Scheme.Hom.comp_apply, hl, hz]
  have p₁ : IsPullback m₁.φ t.G.hom Xo.univ.t.G.hom x := m₁.cart.1
  have q₁ : IsPullback n₁.φ t'.G.hom Xo.univ.t.G.hom x' := n₁.cart.1
  have q₂ : IsPullback n₂.φ t'.G.hom G'.G.hom (spMap (algebraMap T.V T.Fr)) := n₂.cart.1
  have hsq := hc p₁.isoPullback.hom q₁.isoPullback.hom (by simp) (by simp) (by simp) (by simp)
  have hψs : Function.Surjective ψ.left := by
    intro y
    obtain ⟨z, hz⟩ := hf (q₁.isoPullback.hom y)
    obtain ⟨w, rfl⟩ := (inferInstance : Surjective p₁.isoPullback.hom).1 z
    refine ⟨w, q₁.isoPullback.hom.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
    exact hz
  refine (GlobalTheory.isAbelianScheme_of_generically_surjective T.V T.Fr G.G G'.G hB G'.semi F ?_).proper
  rintro y ⟨s, hs⟩
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback q₂ y s hs.symm
  obtain ⟨w, rfl⟩ := hψs z
  refine ⟨m₂.φ w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hψ, Scheme.Hom.comp_apply, hz]

end GlobalTheory.HkIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsProperModelOfExtendsFibreIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_model_of_extends_fibreIsogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x x' : Sp T.Fr ⟶ Xo.X) (G G' : SAB H (Sp T.V)) (t t' : SAB H (Sp T.Fr)) (m₁ : SABMap t Xo.univ.t x) (m₂ : SABMap t G (spMap (algebraMap T.V T.Fr))) (n₁ : SABMap t' Xo.univ.t x') (n₂ : SABMap t' G' (spMap (algebraMap T.V T.Fr))) (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (F : G.G ⟶ G'.G) (N : ℕ), Ext m₁ m₂ n₁ n₂ f F → f' ≫ f = 𝟙 _ ^ N → 0 < N → IsProper G.G.hom → IsProper G'.G.hom := by
  first | exact @GlobalTheory.HkIntegral.isProper_of_ext | exact GlobalTheory.HkIntegral.isProper_of_ext | (intros; apply GlobalTheory.HkIntegral.isProper_of_ext <;> assumption)
end
end
