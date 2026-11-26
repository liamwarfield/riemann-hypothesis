module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmAdjoinActionOfEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmAdjoinActionOfEquation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

private theorem okAct_group_identity {A : Type*} [CommGroup A] (i w : A) (k m n m' n' : ℤ) :
    i ^ (m * m' - n * n' * k) * w ^ (m * n' + n * m' + n * n') =
      (i ^ m * w ^ n) ^ m' * (w ^ m * (w * i ^ (-k)) ^ n) ^ n' := by
  have h1 : m * m' - n * n' * k = m * m' + (-k) * n * n' := by ring
  rw [h1]
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

theorem exists_okAct_of_equation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (W : G ⟶ G), IsMonHom W → (W ≫ W) * (𝟙 G) ^ ((1 + H.d) / 4) = W → ∃ a : OAct (OK H) G, a.act (wK H) = W ∧ ∀ m n : ℤ, a.act ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := by
  intro E _ _ _ H S G _ _ W hW hEq
  obtain ⟨-, hco, -, hsq, -⟩ := OK_isDedekindDomain_and_projective E H
  set k : ℕ := (1 + H.d) / 4 with hk
  choose c hc hcu using hco
  have hcoord : ∀ m n : ℤ, c ((m : OK H) + (n : OK H) * wK H) = (m, n) := fun m n =>
    (hcu _ (m, n) rfl).symm
  have hWW : W ≫ W = W * (𝟙 G) ^ (-(k : ℤ)) := by
    rw [zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    exact hEq
  let F : OK H → (G ⟶ G) := fun a => (𝟙 G) ^ (c a).1 * W ^ (c a).2
  have hF : ∀ m n : ℤ, F ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := fun m n => by
    simp only [F, hcoord]
  have hex : ∀ a : OK H, ∃ m n : ℤ, a = (m : OK H) + (n : OK H) * wK H := fun a => ⟨_, _, hc a⟩
  refine ⟨⟨F, fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, ?_, hF⟩
  · have h1 := Serre.isMonHom_zpow (𝟙 G) (c a).1
    have h2 := Serre.isMonHom_zpow W (c a).2
    exact Serre.isMonHom_mul _ _
  · have := hF 1 0
    simpa using this
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) * ((m' : OK H) + (n' : OK H) * wK H) =
        ((m * m' - n * n' * (k : ℤ) : ℤ) : OK H) + ((m * n' + n * m' + n * n' : ℤ) : OK H) * wK H := by
      push_cast
      linear_combination ((n : OK H) * (n' : OK H)) * hsq
    rw [e, hF, hF, hF]
    simp only [MonObj.comp_mul, GrpObj.comp_zpow, MonObj.mul_comp, GrpObj.zpow_comp, Category.comp_id,
      Category.id_comp, hWW]
    exact okAct_group_identity _ _ _ _ _ _ _
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) + ((m' : OK H) + (n' : OK H) * wK H) =
        ((m + m' : ℤ) : OK H) + ((n + n' : ℤ) : OK H) * wK H := by
      push_cast
      ring
    rw [e, hF, hF, hF, zpow_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _
  · have := hF 0 1
    simpa using this

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmAdjoinActionOfEquationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_cmAdjoin_action_of_equation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (W : G ⟶ G), IsMonHom W → (W ≫ W) * (𝟙 G) ^ ((1 + H.d) / 4) = W → ∃ a : OAct (OK H) G, a.act (wK H) = W ∧ ∀ m n : ℤ, a.act ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := by
  first | exact @GlobalTheory.CM.exists_okAct_of_equation | exact GlobalTheory.CM.exists_okAct_of_equation | (intros; apply GlobalTheory.CM.exists_okAct_of_equation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllExists

theorem isQuadLattice_of_linear {g g' : ℕ} (hg : g = 1) (hg' : g' = 1) {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} (hd : DiscreteTopology Λ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hF : ∀ z, z ∈ Λ ↔ F z ∈ Λ') {d : ℕ} {c : ℂ} (hc : c ≠ 0) (h : PureType.IsQuadLattice Λ' d c) :
    ∃ c' : ℂ, c' ≠ 0 ∧ PureType.IsQuadLattice Λ d c' := by
  subst hg hg'
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ z, F z = fun _ => a * z 0 := ⟨F (fun _ => 1) 0, fun z => by
    have e : z = z 0 • fun _ => (1 : ℂ) := by
      funext i
      fin_cases i
      simp
    funext i
    fin_cases i
    conv_lhs => rw [e, map_smul]
    simp [mul_comm]⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    have ht : (Λ : Set (Fin 1 → ℂ)) = Set.univ := Set.eq_univ_of_forall fun z => (hF z).2 (by
      rw [ha]
      simp only [zero_mul]
      exact Λ'.zero_mem)
    have h1 : IsDiscrete (Λ : Set (Fin 1 → ℂ)) := ⟨hd⟩
    rw [ht, isDiscrete_univ_iff] at h1
    have := (isClopen_discrete ({0} : Set (Fin 1 → ℂ))).eq_univ ⟨0, rfl⟩
    have h2 : (1 : Fin 1 → ℂ) ∈ ({0} : Set (Fin 1 → ℂ)) := this ▸ Set.mem_univ _
    exact one_ne_zero h2
  refine ⟨c / a, div_ne_zero hc ha0, fun z => ?_⟩
  rw [hF, h, ha]
  refine exists₂_congr fun m n => ⟨fun e => ?_, fun e => ?_⟩
  · funext i
    fin_cases i
    have := congrFun e 0
    field_simp
    field_simp at this
    simpa [mul_comm a] using this
  · funext i
    rw [e]
    field_simp

theorem isQuadLattice_of_isGrpPullback (hU : ThetaUnifAV) (hL : Out.Laws) {R : Type} [CommRing R]
    (P : Out.PolAV (Sp R)) (hg : P.g = 1) (σ : R →+* ℂ) {d : ℕ}
    (h : ∀ (Q : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ P.A.left), IsPolFibre σ P Q φ → ∀ u : HolUnif Q.A Q.L Q.g,
      ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c)
    (Q : Out.PolAV (Sp ℂ)) (hQ : Q.g = 1) (φ : Q.A.left ⟶ P.A.left) (hφ : IsGrpPullback Q.A P.A (spMap σ) φ)
    (u : HolUnif Q.A Q.L Q.g) : ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c := by
  obtain ⟨Q₀, φ₀, h₀⟩ := exists_isPolFibre hL.polBaseChange σ P
  obtain ⟨rig, hrig⟩ := Q₀.rigid
  obtain ⟨u₀, -, -, -, -, -, t₁, t₂, -⟩ := hU Q₀ rig hrig
  obtain ⟨c, hc, hΛ⟩ := h Q₀ φ₀ h₀ u₀
  obtain ⟨f, hf, ef⟩ := NormHom.exists_monHom_lift hφ h₀.2.1 (𝟙 P.A)
  obtain ⟨F, hF, hF', -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q₀.A Q.isAb Q₀.isAb Q.L Q₀.L Q.g Q₀.g u u₀ t₁ t₂ f hf
  refine isQuadLattice_of_linear hQ (h₀.1.trans hg) u.discrete F (fun z => ⟨hF' z, fun hz => ?_⟩) hc hΛ
  rw [← u₀.ker, hF] at hz
  rw [← u.ker]
  apply NormHom.push_inj hφ
  have e := NormHom.push_comp hφ h₀.2.1 ef (u.ex z)
  rw [hz, map_one, Category.comp_id] at e
  rw [map_one, e]

theorem exists_ell_pos (hC : CMCurve) (hU : ThetaUnifAV) (hL : Out.Laws) (hX : HomExtDvr) {E : Type} [Field E]
    [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ),
      ((ω : M) : ℂ) = (1 + Complex.I * √H.d) / 2 ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧
      C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, _, w, P, v, hw, hg, hv, ⟨P₀, φ, v₀, W, hφ, hv₀, hb₀, hW, hWW, hWv⟩, hΛ, n, hn0, hn, hx, -⟩ :=
    chowla_selberg_lie_lines hC (by omega) H.d_prime.squarefree (by omega) h2 hr hχ
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨a₀, ha₀, -⟩ := GlobalTheory.T.exists_cmAdjoin_action_of_equation E H _ P₀.A W hW hWW
  obtain ⟨a, ha⟩ := exists_oAct_extend_dedekind hX (𝓞 M) M (OK H) P.A P₀.A φ P.isAb hφ.2.1 a₀
  have hvt : IsTangent v := hv.1 0
  have := a.hom (wK H)
  obtain ⟨c, hc, -⟩ := hv.2 _ (HomLinear.isTangent_comp (a.act (wK H)) hvt)
  obtain ⟨ω, rfl⟩ : ∃ ω, c = ![ω] := ⟨c 0, by funext i; fin_cases i; rfl⟩
  have hc₀ := (lieComb_baseChange _ _ (algebraMap (𝓞 M) M) P.A P₀.A φ hφ.2.1 1 ![v] _ ![ω] ![v₀] (v₀ ≫ W)
    (fun j => by fin_cases j; exact hv₀) hc).1 (NormHom.isVecOver_comp hv₀ (ha₀ ▸ ha (wK H)))
  have hω : (ω : M) = w := congrFun ((hb₀.2 _ (HomLinear.isTangent_comp W (hb₀.1 0))).unique hc₀ hWv) 0
  have hσ : Function.Injective ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) :=
    (algebraMap M ℂ).injective.comp (IsFractionRing.injective (𝓞 M) M)
  obtain ⟨L', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_normalized_symmetric_ample_lb hL (𝓞 M) P (a.act (wK H)) (a.act (EllConj.barK H (wK H)))
    (a.hom _) (a.hom _) (by rw [← a.add, add_comm, EllConj.barK_wK_add, a.one])
    (GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P a hσ hg _ _ rfl)
  let P' : Out.PolAV (Sp (𝓞 M)) := ⟨P.A, P.isAb, P.g, P.smoothDim, L', h₁, h₂, h₃, h₄, h₅⟩
  have key : ∀ (s : M →+* ℂ) r, IsLieNormSq P' v (s.comp (algebraMap (𝓞 M) M)) r → r = n s := fun s r h => by
    have h1 : IsLieComb ![(1 : 𝓞 M)] ![v] (v ≫ 𝟙 P.A) := by
      rw [LieComb.isLieComb_iff_tanExp, Category.comp_id]
      have e : (![1] : Fin 1 → 𝓞 M) = Pi.single 0 1 := by
        funext i
        fin_cases i
        simp
      rw [e]
      exact (LieComb.tanExp_single hv.1 0).symm
    have e := NormHom.lieNormSq_comp hU hL (𝓞 M) P P' (𝟙 P.A) (𝟙 P.A) v 1 _ (n s) r inferInstance inferInstance h₆ hvt
      h1 ((hn s _).2 rfl) (by rwa [Category.comp_id])
    simpa using e
  refine ⟨M, inferInstance, ω, ⟨P', hg, a, v, hv, hc, GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P' a hσ hg, h₇⟩, -meanLog M n,
    hω ▸ hw, fun Q ψ hψ u => ?_, ⟨n, fun s => ⟨hn0 s, fun r => ⟨key s r, fun e => ?_⟩⟩, rfl⟩, hx⟩
  · refine isQuadLattice_of_isGrpPullback hU hL P hg _ (fun Q ψ hψ u => ?_) Q (hψ.1.trans hg) ψ hψ.2.1 u
    obtain ⟨c, hc, h⟩ := hΛ Q ψ hψ u
    rw [hw] at h
    exact ⟨c, hc, h⟩
  · obtain ⟨r', hr'⟩ := exists_isLieNormSq hU hL.polBaseChange P' hvt (s.comp (algebraMap (𝓞 M) M))
    rwa [e, ← key s r' hr']

theorem exists_ell : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ), 2 * ((ω : M) : ℂ) - 1 = ρ ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧ C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro hC hU hL hX E _ _ _ H _ χ hχ ρ hρ
  obtain ⟨M, _, ω, C, x, hω, hp, hx, hv⟩ := exists_ell_pos hC hU hL hX H hχ
  have e : ρ ^ 2 = (Complex.I * √H.d) ^ 2 := by
    rw [hρ, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with rfl | rfl
  · exact ⟨M, inferInstance, ω, C, x, by rw [hω]; ring, hp, hx, hv⟩
  · obtain ⟨a, -, h₁, h₂, h₃⟩ := EllConj.exists_conj_action E H (𝓞 M) ω C
    refine ⟨M, inferInstance, 1 - ω, ⟨C.P, C.dim, a, C.v, C.basis, h₁, h₂, h₃⟩, x, ?_, hp, hx, hv⟩
    have : (((1 - ω : 𝓞 M) : M) : ℂ) = 1 - ((ω : M) : ℂ) := by simp
    rw [this, hω]
    ring

end GlobalTheory.CM.EllExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmEllipticCurve_integers_with_period : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ), 2 * ((ω : M) : ℂ) - 1 = ρ ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧ C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  first | exact @GlobalTheory.CM.EllExists.exists_ell | exact GlobalTheory.CM.EllExists.exists_ell | (intros; apply GlobalTheory.CM.EllExists.exists_ell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem isDiffOf_mem_lieLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {f : P.A ⟶ P'.A} {D : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)} (hD : F.IsDiffOf F' f D)
    {c : Fin F.P₀.g → K} (hc : c ∈ F.lieLat) : D c ∈ F'.lieLat := by
  have key : F.lieLat ≤ (F'.lieLat).comap (D.restrictScalars (𝓞 K)) := by
    unfold GenFib.lieLat
    refine Submodule.span_le.mpr ?_
    rintro x ⟨u, hu⟩
    exact Submodule.subset_span ⟨u ≫ f, hD u x hu⟩
  exact key hc

theorem smul_image_mem_lieLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    (F' : GenFib P') (f : P.A ⟶ P'.A) (hf : IsMonHom f) (i : Fin F.P₀.g) (w : epsR K ⟶ F'.P₀.A)
    (U : Fin F'.P₀.g → K) (hw : w.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left) (hU : IsLieComb U F'.v w) (c : K)
    (hc : (Pi.single i c : Fin F.P₀.g → K) ∈ F.lieLat) : c • U ∈ F'.lieLat := by
  obtain ⟨⟨M, hM, -⟩, f₀, -, hf₀, hcomb⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  have hmem : M (Pi.single i c) ∈ F'.lieLat := isDiffOf_mem_lieLat hM hc
  have hv : IsLieComb (Pi.single i 1) F.v (F.v i) :=
    (GlobalTheory.LieComb.lieComb_algebra K F.P₀.A F.P₀.g F.v F.basis.1).2.2.2.1 i
  have h1 : IsLieComb (M (Pi.single i 1)) F'.v (F.v i ≫ f₀) := hcomb M hM _ _ hv
  have hw' : F.v i ≫ f₀ = w := by
    apply Over.OverMorphism.ext
    apply F'.fib.2.1.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hf₀, hw]
    · rw [Over.w, Over.w]
  rw [hw'] at h1
  have htan : IsTangent w :=
    (GlobalTheory.LieComb.lieComb_algebra K F'.P₀.A F'.P₀.g F'.v F'.basis.1).2.1 U w hU
  have hUeq : M (Pi.single i 1) = U := (F'.basis.2 w htan).unique h1 hU
  have hsingle : (Pi.single i c : Fin F.P₀.g → K) = c • Pi.single i 1 := by
    ext j
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hsingle, map_smul, hUeq] at hmem
  exact hmem

theorem image_integral_of_isLocGen {K : Type} [Field K] [NumberField K] {A B : Out.PolAV (Sp (𝓞 K))} {x y : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} {ψ : y.P.A.left ⟶ B.A.left} (hx : IsFibreOf A x (gmap K) φ)
    (hy : IsFibreOf B y (gmap K) ψ) (f : A.A ⟶ B.A) (hf : IsMonHom f) {i : Fin x.P.g} {ℓ : MLine K}
    (hℓ : IsVecLine A x φ i ℓ) {w : epsR K ⟶ y.P.A} {U : Fin y.P.g → K}
    (hw : w.left ≫ ψ = (x.v i).left ≫ φ ≫ f.left) (hU : IsLieComb U y.v w) {p : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin y.P.g) (Fin y.P.g) K} (hM : IsModelAt B y ψ p M) {cl : K} (hcl : IsLocGen p cl ℓ.I) (m) :
    p.valuation K (Matrix.vecMul (cl • U) M⁻¹ m) ≤ 1 := by
  have hfA : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).mp hx
  have hfB : IsPolFibre (algebraMap (𝓞 K) K) B y.P ψ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) B y ψ).mp hy
  have hI : ℓ.I ≠ 0 := hℓ.1.1
  obtain ⟨s, hs, hsI⟩ : ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • cl ∈ ℓ.I :=
    ((((local_global_ideal_lattice K).2.1 ℓ.I p hI).2 cl).mp hcl).2 cl |>.mp le_rfl
  have hA : (Pi.single i (s • cl) : Fin x.P.g → K) ∈ (GenFib.mk x.P φ hfA x.v x.basis : GenFib A).lieLat :=
    (isVecLine_mem_iff_mem_lieLat K A x φ hfA i ℓ hℓ (s • cl)).mp hsI
  have hB := smul_image_mem_lieLat (GenFib.mk x.P φ hfA x.v x.basis) (GenFib.mk y.P ψ hfB y.v y.basis) f hf i w U
    hw hU (s • cl) hA
  have key := (isModelAt_integral_iff_mem_lieLat K B y ψ hfB p M hM (cl • U)).mpr
    ⟨s, hs, by rw [← smul_assoc]; exact hB⟩
  exact key m

theorem letter_integral_of_isLocGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (M : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁), IsModelAt o.B o.xB o.φB p M → ∀ (k : Fin o.xB.P.g) (cl : o.K₁), IsLocGen p cl (L.ℓ k).I → ∀ m, p.valuation o.K₁ (Matrix.vecMul (cl • L.U k) M⁻¹ m) ≤ 1 := by
  intro E _ _ _ _ H l c nΨ n' f o La hgood L hL p M hM k cl hcl m
  obtain ⟨-, -, -, hB, hΨ, h', -, -, -, -, -, -, -, hiso, -, -, hℓΨ, hℓ', -⟩ := hgood
  obtain ⟨-, -, hlet, hline⟩ := hL
  obtain ⟨w, hwk, hU⟩ := hlet k
  have hlk := hline k
  unfold LamLetters.IsLetter at hwk
  rcases hsrc : L.src k with q | q <;> rw [hsrc] at hwk hlk
  · dsimp only at hwk hlk
    rw [hlk] at hcl
    exact image_integral_of_isLocGen hΨ hB (o.φΨ q.1) (hiso.1 q.1) (hℓΨ q.2) hwk hU hM hcl m
  · dsimp only at hwk hlk
    rw [hlk] at hcl
    exact image_integral_of_isLocGen h' hB (o.φ' q.1) (hiso.2.1 q.1) (hℓ' q.2) hwk hU hM hcl m

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralOfLocalGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLetter_integral_of_local_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (M : Matrix (Fin o.xB.P.g) (Fin o.xB.P.g) o.K₁), IsModelAt o.B o.xB o.φB p M → ∀ (k : Fin o.xB.P.g) (cl : o.K₁), IsLocGen p cl (L.ℓ k).I → ∀ m, p.valuation o.K₁ (Matrix.vecMul (cl • L.U k) M⁻¹ m) ≤ 1 := by
  first | exact @GlobalTheory.LamF.letter_integral_of_isLocGen | exact GlobalTheory.LamF.letter_integral_of_isLocGen | (intros; apply GlobalTheory.LamF.letter_integral_of_isLocGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEigLatEqOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFamIsometryInjective
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

namespace GlobalTheory.LamF

theorem hermFam_isometry_injective {K : Type*} [Field K] [NumberField K] {V V' : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s a b, h'.form s (M a) (M b) = h.form s a b) : Function.Injective M := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent K ![x] := by
    rw [linearIndependent_unique_iff]; simpa using h0
  have h1 := (h.posDef s 1 ![x] hli).diag_pos (i := 0)
  have h2 : h'.form s (M x) (M x) = 0 := by
    have := h'.smul_right s 0 (M x) (M x)
    rw [zero_smul, map_zero, zero_mul] at this
    rw [← this, hx]
  rw [hM] at h2
  simp [h2] at h1

theorem deg_map_isometry : ∀ (K : Type) [Field K] [NumberField K] (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V') (Λ : Submodule (𝓞 K) V), Λ.FG → (∀ s a b, h'.form s (M a) (M b) = h.form s a b) → ReciprocityTheory.GeometryOfNumbersTheory.deg h' (Λ.map (M.restrictScalars (𝓞 K))) = ReciprocityTheory.GeometryOfNumbersTheory.deg h Λ := by
  intro K _ _ V V' _ _ _ _ _ _ _ _ h h' M E hE hM
  have hinj := hermFam_isometry_injective h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [Set.range_comp, Submodule.span_image]
    exact ⟨x, hv.2.2 hx, rfl⟩
  rw [arakelovDegree_eq_degreeOfFamily h hE hv, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  unfold degreeOfFamily
  have e1 : ∀ s, h'.gram s (M ∘ v) = h.gram s v := fun s => by
    ext i j; simp [HermFam.gram, hM]
  have e2 : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, Set.range_comp]; rfl
  simp only [e1, e2, Submodule.map_toAddSubgroup]
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ (by exact hinj)]

end GlobalTheory.LamF
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF


open IntCoord in
theorem diff_mem_eigLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) {c : Fin F.P₀.g → K} (hc : c ∈ F.eigLat a τ) :
    M c ∈ F'.eigLat a' τ := by
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem map_eigLat_of_iso {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} (e : P.A ≅ P'.A)
    (hf : ∀ x, a.act x ≫ e.hom = e.hom ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    {M' : (Fin F'.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)}
    (hM : F.IsDiffOf F' e.hom M) (hM' : F'.IsDiffOf F e.inv M') (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) = F'.eigLat a' τ := by
  refine le_antisymm ?_ fun c hc => ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact diff_mem_eigLat hf hM τ hc
  · have hf' : ∀ x, a'.act x ≫ e.inv = e.inv ≫ a.act x := fun x => by
      rw [Iso.comp_inv_eq, Category.assoc, hf, Iso.inv_hom_id_assoc]
    refine ⟨M' c, diff_mem_eigLat hf' hM' τ hc, ?_⟩
    obtain ⟨u, hu, -⟩ := ((integral_tangent_coordinates K P' F').2.2.2.2.2 O a' τ c).1 hc
    have h2 := hM _ _ (hM' _ _ hu)
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
    exact ((integral_tangent_coordinates K P' F').1 u hu.1).unique h2 hu

theorem deg_eigLat_eq_of_iso : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (O : Type) [CommRing O] (a : OAct O P.A) (a' : OAct O P'.A) (e : P.A ≅ P'.A), F.IsHerm h → F'.IsHerm h' → Serre.IsLinearHom a a' e.hom → LamEq P'.L e.hom e.hom P.L (𝟙 P.A) (𝟙 P.A) → ∀ τ : O →+* 𝓞 K, deg h (F.eigLat a τ) = deg h' (F'.eigLat a' τ) := by
  intro hT hL K _ _ P P' F F' h h' O _ a a' e hh hh' hlin hlam τ
  have hm : IsMonHom e.hom := hlin.1
  have hm' : IsMonHom e.inv := inferInstance
  obtain ⟨M, hM, -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' e.hom hm).1
  obtain ⟨M', hM', -⟩ := (GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P' F' P F e.inv hm').1
  have hid : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hu => by simpa using hu
  have hiso := GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hT hL K P F P' F' h h' e.hom (𝟙 P.A) M LinearMap.id hh hh' hm inferInstance hlam hM hid
  have hle : F.eigLat a τ ≤ F.lieLat := Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
  have hfg : (F.eigLat a τ).FG := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1.of_le hle
  rw [← map_eigLat_of_iso e hlin.2 hM hM' τ]
  exact (deg_map_isometry K _ _ h h' M _ hfg hiso).symm

end GlobalTheory.LamF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_oAct_rosatiConj : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))), ∃ oa : T.pol.OAct (𝓞 E), oa.act = T.t.act.act ∧ RosatiConj T.pol oa := by
  intro hL E _ _ _ _ H hs K _ _ T
  have : IsCommMonObj T.pol.A := T.pol.isAb.comm
  obtain ⟨ra, hra⟩ := (ringAct_iff_oAct (𝓞 E) (Sp (𝓞 K)) T.pol.A).2 T.t.act
  have hlam : ∀ a : 𝓞 E, LamEq T.pol.L (ra.act a) (𝟙 T.pol.A) T.pol.L (𝟙 T.pol.A) (ra.act (star a)) := by
    intro a
    rw [hra, hs]
    have h := T.t.adj a
    simpa [LamEq] using h
  refine ⟨⟨ra, fun a => (GlobalTheory.RosLam.rosatiAdj_iff_lamEq hL.globalFns _ T.pol _ _ (ra.hom a) (ra.hom _)).2 (hlam a)⟩,
    hra, ?_⟩
  intro a Tb k x z c hk hx hz
  have hp : ∀ (n : ℕ) (p : Tb ⟶ T.pol.A), pnsmulPt n p = p ^ n := by
    intro n p
    induction n with
    | zero => rw [pow_zero]; rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have hu : toUnit Tb ≫ η[T.pol.A] = (1 : Tb ⟶ T.pol.A) := rfl
  rw [hp, hu] at hx hz
  have := GlobalTheory.T.commutatorPairings_eq_of_cubeLBPairingIso hL (𝓞 K) T.pol T.pol T.pol T.pol (ra.act a) (𝟙 _) (𝟙 _) (ra.act (star a)) (ra.hom a)
    inferInstance inferInstance (ra.hom _) (hlam a) Tb k x z c hk hx hz
  simpa using this

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRosatiActionWeilPairingBalancedTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rosatiAction_weilPairing_balanced_triple : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] (T : PAT H (Sp (𝓞 K))), ∃ oa : T.pol.OAct (𝓞 E), oa.act = T.t.act.act ∧ RosatiConj T.pol oa := by
  first | exact @GlobalTheory.LamF.exists_oAct_rosatiConj | exact GlobalTheory.LamF.exists_oAct_rosatiConj | (intros; apply GlobalTheory.LamF.exists_oAct_rosatiConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingHomExtRingOfIntegers
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.EigLine

theorem ringHom_ext_ringOfIntegers {E K : Type} [Field E] [NumberField E] [Field K] {f g : E →+* K}
    (h : ∀ a : 𝓞 E, f (a : E) = g (a : E)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem forall_apply_eq_smul_iff {K O : Type} [Field K] {n : ℕ} (r : O → Module.End K (Fin n → K)) (χ : Fin n → O → K)
    (hχ : Function.Injective χ) (hr : ∀ a j, r a (Pi.single j 1) = Pi.single j (χ j a)) (i : Fin n) (c : Fin n → K) :
    (∀ a, r a c = χ i a • c) ↔ ∃ s : K, c = Pi.single i s := by
  have hd : ∀ a (d : Fin n → K) j, r a d j = χ j a * d j := fun a d j => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [pi_eq_sum_univ' d, map_sum]
    simp only [map_smul, hr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk.symm]) (by simp), Pi.single_eq_same,
      mul_comm]
  constructor
  · intro h
    refine ⟨c i, funext fun j => ?_⟩
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj]
      by_contra hc
      refine hj (hχ (funext fun a => mul_right_cancel₀ hc ?_))
      rw [← hd, h a, Pi.smul_apply, smul_eq_mul]
  · rintro ⟨s, rfl⟩ a
    funext j
    rw [hd, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i
    · rw [hj]
    · rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]

theorem mem_eigLat_iff : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (oa : A.OAct (𝓞 E)) (act : OAct (𝓞 E) A.A) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)), act.act = oa.act → Function.Injective lab → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (t : 𝓞 E →+* 𝓞 K), (∀ a : 𝓞 E, (t a : K) = lab (τ i) (a : E)) → ∀ c, c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).eigLat act t ↔ c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat ∧ ∃ r : K, c = Pi.single i r := by
  intro E _ _ _ K _ _ A x φ hf oa act S τ lab hact hlab hty i t ht c
  obtain ⟨r, hr, he⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K A (GenFib.mk x.P φ hf x.v x.basis) (𝓞 E) act
  have := x.P.isAb.comm
  have halg := LieComb.lieComb_algebra K x.P.A x.P.g x.v x.basis.1
  have hdiag : ∀ (a : 𝓞 E) (j : Fin x.P.g), r a (Pi.single j 1) = Pi.single j (lab (τ j) (a : E)) := fun a j => by
    obtain ⟨-, f₀, -, e, h⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K A (GenFib.mk x.P φ hf x.v x.basis) A (GenFib.mk x.P φ hf x.v x.basis)
      (act.act a) (act.hom a)
    obtain ⟨w, hw, hw'⟩ := hty a j
    have h₁ : IsLieComb (r a (Pi.single j 1)) x.v (x.v j ≫ f₀) := h _ (hr a) _ _ (halg.2.2.2.1 j)
    have e' : f₀.left ≫ φ = φ ≫ (oa.act a).left := by rw [← hact]; exact e
    obtain rfl : x.v j ≫ f₀ = w := Over.OverMorphism.ext (hf.2.1.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, e', hw']) ((Over.w _).trans (Over.w _).symm))
    exact (x.basis.2 _ (halg.2.1 _ _ hw)).unique h₁ hw
  have hχ : Function.Injective fun (j : Fin x.P.g) (a : 𝓞 E) => lab (τ j) (a : E) := fun j k h =>
    τ.injective (Subtype.ext (hlab (ringHom_ext_ringOfIntegers fun a => congrFun h a)))
  refine (he t c).1.trans (and_congr_right fun _ => ?_)
  rw [← forall_apply_eq_smul_iff (fun a => r a) _ hχ hdiag i c]
  refine forall_congr' fun a => ?_
  rw [← ht a, ← algebraMap_smul K (t a) c]

end GlobalTheory.LamF.EigLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticeHermitianInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticeHermitianInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FibIndep

section Lattice

variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']


open scoped ComplexOrder in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] in
theorem injective_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') : Function.Injective M := by
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  by_contra hne
  have hli : LinearIndependent K ![c] := (linearIndependent_unique_iff (v := ![c])).2 (by simpa using hne)
  have hpos := (h.posDef s 1 ![c] hli).diag_pos (i := 0)
  have hzero : h'.form s 0 0 = 0 := by simpa using h'.smul_right s 0 0 0
  have hcc : h.form s c c = 0 := by rw [← hM, hc, hzero]
  simp only [Matrix.of_apply, Matrix.cons_val_fin_one] at hpos
  rw [hcc] at hpos
  exact lt_irrefl _ hpos

theorem deg_map_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') {E : Submodule (𝓞 K) V} (hE : E.FG) :
    deg h E = deg h' (E.map (M.restrictScalars (𝓞 K))) := by
  have hinj := injective_of_isometry h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  obtain ⟨hvE, hvli, hvsp⟩ := hv
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => Submodule.mem_map_of_mem (hvE i), hvli.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hvsp hx
    rw [Set.range_comp, Submodule.span_image]
    exact Submodule.mem_map_of_mem hx'
  rw [arakelovDegree_eq_degreeOfFamily h hE ⟨hvE, hvli, hvsp⟩, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  have hgram : ∀ σ, h'.gram σ (M ∘ v) = h.gram σ v := fun σ => by
    ext i j
    simp [HermFam.gram, hM]
  have hspan : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range (M ∘ v))).toAddSubgroup.relIndex
      (E.map (M.restrictScalars (𝓞 K))).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup := by
    rw [hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  unfold degreeOfFamily
  rw [hidx]
  simp only [hgram]

end Lattice

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))}

theorem existsUnique_coord (F : GenFib P) {u : epsR (𝓞 K) ⟶ P.A} (hu : IsTangent u) : ∃! c, F.IsCoord u c := by
  have hb := F.basis
  unfold IsLieBasis at hb
  have hf := F.fib
  unfold IsPolFibre at hf
  obtain ⟨-, hpb, -⟩ := hf
  obtain ⟨w, hw, hwu⟩ := existsUnique_isVecOver hpb.1 u
  obtain ⟨c, hc, hcu⟩ := hb.2 w (hw.isTangent hpb hu)
  refine ⟨c, ⟨hu, w, hw, hc⟩, ?_⟩
  rintro c' ⟨-, w', hw', hc'⟩
  obtain rfl := hwu w' hw'
  exact hcu c' hc'

theorem image_coord (F F' : GenFib P) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)} (hM : F.IsDiffOf F' (𝟙 P.A) M)
    (p : (epsR (𝓞 K) ⟶ P.A) → Prop) :
    Submodule.span (𝓞 K) {c | ∃ u, F'.IsCoord u c ∧ p u} =
      (Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u}).map (M.restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext c
  constructor
  · rintro ⟨u, hu, hp⟩
    obtain ⟨ht, -⟩ := id hu
    obtain ⟨c₀, hc₀, -⟩ := existsUnique_coord F ht
    refine ⟨c₀, ⟨u, hc₀, hp⟩, ?_⟩
    have h1 := hM u c₀ hc₀
    rw [Category.comp_id] at h1
    exact (existsUnique_coord F' ht).unique h1 hu
  · rintro ⟨c₀, ⟨u, hu, hp⟩, rfl⟩
    have h1 := hM u c₀ hu
    rw [Category.comp_id] at h1
    exact ⟨u, h1, hp⟩

theorem deg_lieLat_eq : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → deg h F.lieLat = deg h' F'.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K), deg h (F.eigLat act τ) = deg h' (F'.eigLat act τ) := by
  intro hU hL K _ _ P F F' h h' hh hh'
  obtain ⟨⟨M, hM, -⟩, -⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F' (𝟙 P.A) inferInstance
  have hN : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hc => by
    rw [Category.comp_id]
    exact hc
  have hlam : LamEq P.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) :=
    GlobalTheory.PolBaseChange.lbIso_refl (GlobalTheory.LamCalc.cubeLB_isLB P.isLB _)
  have hiso : ∀ s c c', h'.form s (M c) (M c') = h.form s c c' := fun s c c' => by
    simpa using GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hU hL K P F P F' h h' (𝟙 P.A) (𝟙 P.A) M LinearMap.id hh hh'
      inferInstance inferInstance hlam hM hN s c c'
  have hFG := (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).1
  refine ⟨?_, fun O _ act τ => ?_⟩
  · have e := image_coord F F' hM (fun _ => True)
    simp only [and_true] at e
    have e' : F'.lieLat = F.lieLat.map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG
  · have e := image_coord F F' hM (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a))
    have hle : F.eigLat act τ ≤ F.lieLat :=
      Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
    have hFG' : (F.eigLat act τ).FG := hFG.of_le hle
    have e' : F'.eigLat act τ = (F.eigLat act τ).map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG'

end GlobalTheory.FibIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticeHermitianInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_lie_lattice_hermitian_invariant : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → deg h F.lieLat = deg h' F'.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K), deg h (F.eigLat act τ) = deg h' (F'.eigLat act τ) := by
  first | exact @GlobalTheory.FibIndep.deg_lieLat_eq | exact GlobalTheory.FibIndep.deg_lieLat_eq | (intros; apply GlobalTheory.FibIndep.deg_lieLat_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FormLetterLe
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamEqOfWeilIsAllPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

private theorem pnsmulPt_eq_pow {S : Scheme.{0}} {G T : Over S} [GrpObj G] (n : ℕ) (a : T ⟶ G) :
    pnsmulPt n a = a ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem lamEq_of_weilIs_all_points : Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A) (g : A.A ⟶ A.A), IsMonHom f → IsMonHom g → (∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k → pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] → (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ g) y c)) → LamEq B.L f f A.L g (𝟙 A.A) := by
  intro laws K _ _ A B f g hf hg H
  have hβ : Function.Injective ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K)) :=
    (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective (𝓞 K) K)
  refine (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring laws (𝓞 K) A A B A f f g (𝟙 A.A) hf hf hg inferInstance (AlgebraicClosure K)
    ((algebraMap K (AlgebraicClosure K)).comp (algebraMap (𝓞 K) K))).2 inferInstance hβ ?_
  intro n p q c hn hp hq
  rw [Category.comp_id]
  refine H _ n p q (unitOn c) hn ?_ ?_
  · rw [pnsmulPt_eq_pow, hp]; rfl
  · rw [pnsmulPt_eq_pow, hq]; rfl

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianLengthImageEigenBasisVectorLe
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianLengthImageEigenBasisVectorLe
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LenOne

theorem re_form_smul_le {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V)
    (s : K →+* ℂ) (t : K) {x : V} (hx : x ≠ 0) : (h.form s x (t • x)).re ≤ ‖s t‖ * (h.form s x x).re := by
  have hp := (h.posDef s 1 ![x] (by simpa [linearIndependent_unique_iff] using hx)).diag_pos (i := 0)
  have hp' : 0 < h.form s x x := by simpa using hp
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hp'
  rw [h.smul_right, Complex.mul_re, ← h2, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right (Complex.re_le_norm _) h1.le

theorem diff_single_eq {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    (F' : GenFib P') {f : P.A ⟶ P'.A} {f₀ : F.P₀.A ⟶ F'.P₀.A} (e : f₀.left ≫ F'.φ = F.φ ≫ f.left)
    {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀)) (i : Fin F.P₀.g) {U : Fin F'.P₀.g → K}
    {w : epsR K ⟶ F'.P₀.A} (hU : IsLieComb U F'.v w) (hw : w.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left) :
    M (Pi.single i 1) = U := by
  have := F.P₀.isAb.comm
  have := F'.P₀.isAb.comm
  obtain rfl : w = F.v i ≫ f₀ := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext
    (by rw [hw, Over.comp_left, Category.assoc, e]) ((Over.w _).trans (Over.w _).symm))
  exact (F'.basis.2 _ ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 U _ hU)).unique
    (hM _ _ ((LieComb.lieComb_algebra K _ _ F.v F.basis.1).2.2.2.1 i)) hU

theorem form_image_le : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → ∀ (i : Fin F.P₀.g) (t : K) (w : epsR K ⟶ F.P₀.A) (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A), IsLieComb (Pi.single i t) F.v w → (F.v i).left ≫ F.φ ≫ g.left = w.left ≫ F.φ → IsLieComb U F'.v w' → w'.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left → ∀ s : K →+* ℂ, (h'.form s U U).re ≤ ‖s t‖ * (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  intro hT hL K _ _ P P' F F' h h' f g hh hh' hf hg hlam i t w U w' hw ew hU ew' s
  obtain ⟨⟨M, hM, -⟩, f₀, -, ef, hf₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f hf
  obtain ⟨⟨N, hN, -⟩, g₀, -, eg, hg₀⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  have h1 := diff_single_eq F F' ef (hf₀ M hM) i hU ew'
  have h2 := diff_single_eq F F eg (hg₀ N hN) i hw ew.symm
  have h3 := GlobalTheory.T.hermitianMetric_differential_eq_of_pairing_relation hT hL K P F P' F' h h' f g M N hh hh' hf hg hlam hM hN s (Pi.single i 1) (Pi.single i 1)
  have h4 : (Pi.single i t : Fin F.P₀.g → K) = t • (Pi.single i 1 : Fin F.P₀.g → K) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h1, h2, h4] at h3
  rw [h3]
  exact re_form_smul_le h s t (by simp)

end GlobalTheory.LamF.LenOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianLengthImageEigenBasisVectorLeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLength_image_eigenBasisVector_le : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → ∀ (i : Fin F.P₀.g) (t : K) (w : epsR K ⟶ F.P₀.A) (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A), IsLieComb (Pi.single i t) F.v w → (F.v i).left ≫ F.φ ≫ g.left = w.left ≫ F.φ → IsLieComb U F'.v w' → w'.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left → ∀ s : K →+* ℂ, (h'.form s U U).re ≤ ‖s t‖ * (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  first | exact @GlobalTheory.LamF.LenOne.form_image_le | exact GlobalTheory.LamF.LenOne.form_image_le | (intros; apply GlobalTheory.LamF.LenOne.form_image_le <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem form_letter_le (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [StarRing (𝓞 E)] {K : Type} [Field K] [NumberField K] {S : Set (E →+* ℂ)}
    (A B : Out.PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left)
    (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)) (hx : IsFibreOf A x (gmap K) φ)
    (hT : IsLieType A oa x φ τ lab) (F' : GenFib B) (h' : HermFam K (Fin F'.P₀.g → K)) (H' : F'.IsHerm h')
    (f : A.A ⟶ B.A) (hf : IsMonHom f) (a : 𝓞 E)
    (hW : ∀ (Tb : Over (Sp (𝓞 K))) (k : ℕ) (x y : Tb ⟶ A.A) (c : Γ(Tb.left, ⊤)ˣ), 0 < k →
      pnsmulPt k x = toUnit Tb ≫ η[A.A] → pnsmulPt k y = toUnit Tb ≫ η[A.A] →
      (Out.WeilIs B.A B.L k (x ≫ f) (y ≫ f) c ↔ Out.WeilIs A.A A.L k (x ≫ oa.act a) y c))
    (La : ℝ) (hb : ∀ τ : E →+* ℂ, ‖τ (a : E)‖ ≤ La ^ 2) (i : Fin x.P.g) (ℓ : MLine K) (hℓ : IsVecLine A x φ i ℓ)
    (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A) (hw : IsLieComb U F'.v w')
    (e : w'.left ≫ F'.φ = (x.v i).left ≫ φ ≫ f.left) (s : K →+* ℂ) :
    (h'.form s U U).re ≤ (La * ℓ.n s) ^ 2 := by
  have hp : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).1 hx
  obtain ⟨h, H⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL K A (GenFib.mk x.P φ hp x.v x.basis)).1
  have hg : IsMonHom (oa.act a) := oa.hom a
  obtain ⟨w, hw1, hw2⟩ := hT a i
  have h1 := GlobalTheory.T.hermitianLength_image_eigenBasisVector_le hU hL K A B (GenFib.mk x.P φ hp x.v x.basis) F' h h' f (oa.act a) H H' hf hg
    (lamEq_of_weilIs_all_points hL K A B f (oa.act a) hf hg hW) i _ w U w' hw1 hw2 hw e s
  have h2 := GlobalTheory.CM.LieMetric.vecLine_norm_sq_eq_form hU hL K A x φ hp h H i ℓ hℓ s
  refine h1.trans ?_
  rw [mul_pow]
  refine le_trans (le_of_eq (congrArg _ h2.symm)) ?_
  exact mul_le_mul_of_nonneg_right (hb (s.comp (lab (τ i)))) (sq_nonneg _)

theorem lamLen : ThetaUnifAV → Out.Laws → LamLenSt := by
  intro hU hL E _ _ _ _ H l c _ nΨ n' f o La hG L hLg σ
  obtain ⟨-, -, -, hB, hΨ, hA', -, -, -, tΨ, t', -, -, hI, hP, hb, vΨ, v', -, hgood, -, harch, -⟩ := hG
  have hp : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB :=
    (isFibreOf_iff_isPolFibre (𝓞 o.K₁) o.K₁ (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB o.φB).1 hB
  obtain ⟨h, Hh⟩ := (GlobalTheory.CM.LieMetric.exists_unique_isHerm hU hL o.K₁ o.B
    (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis)).1
  obtain ⟨g1, g2⟩ := gram_stdBasis_posDef_and_hq o.K₁ o.xB.P.g h σ
  refine ⟨_, g1, ?_, fun k => ?_⟩
  · have := GlobalTheory.T.topLieVector_norm_sq_eq_gramDet hU hL o.K₁ o.B o.xB o.φB hp h Hh o.Tl o.LamL σ (harch σ)
    exact ((congrArg Real.sqrt this).symm.trans (Real.sqrt_sq (hgood.2 σ).le)).symm
  · rw [g2]
    obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 k
    have h4 := hLg.2.2.2 k
    unfold LamLetters.IsLetter at hw1
    cases hs : L.src k with
    | inl q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.AΨ o.B o.oaΨ o.xΨ o.φΨg (S := psiSet H) o.τΨ _ hΨ tΨ
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φΨ q.1) (hI.1 _) (o.hΨ q.1) (hP.2.2.1 q.1) La
        (hb.1 q.1) q.2 _ (vΨ q.2) _ w hw2 hw1 σ
    | inr q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.A' o.B o.oa' o.x' o.φ'g (S := (psiSet H)ᶜ) o.τ' _ hA' t'
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φ' q.1) (hI.2.1 _) (o.h' q.1) (hP.2.2.2 q.1) La
        (hb.2 q.1) q.2 _ (v' q.2) _ w hw2 hw1 σ

end GlobalTheory.LamF
end
