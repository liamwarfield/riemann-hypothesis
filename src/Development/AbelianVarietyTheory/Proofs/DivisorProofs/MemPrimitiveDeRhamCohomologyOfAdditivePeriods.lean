module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationSquareAbelianVari
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationSquareAbelianVari
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_holUnif_square : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  intro A _ g L u hA
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hg := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨n, hn⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ (A ⊗ A) hAA
  obtain ⟨L', ⟨v⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif (A ⊗ A) n hAA hn
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨M₁, hM₁, hΛ₁, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (fst A A) inferInstance
  obtain ⟨M₂, hM₂, hΛ₂, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (snd A A) inferInstance
  refine ⟨n, L', v, M₁, M₂, hAA, hM₁, hM₂, fun w => ?_, fun l => hΛ₁ l l.2, fun l => hΛ₂ l l.2⟩
  rw [LinearMap.add_apply, u.ex_add, hM₁, hM₂, Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationSquareAbelianVariStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphicUniformisation_square_abelianVariety : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  first | exact @GlobalTheory.CechPer.exists_holUnif_square | exact GlobalTheory.CechPer.exists_holUnif_square | (intros; apply GlobalTheory.CechPer.exists_holUnif_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerPull
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsOfAffineBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsOfAffineBasis
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isPer_of_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  intro A _ g L u c K W k q hcomp hbasis hdiff hder hper
  classical
  obtain ⟨hopen, hvd, hpp, hvp, -, hmono, -, -, hres, halg, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  have hev := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u
  have hevres := GlobalTheory.T.evForm_restriction_eq A g L u
  let f : ∀ (U V : A.left.affineOpens), V ≤ U → Sec (str A) V.1 := fun U V h ↦
    c.1.1 (Opposite.op U) (Opposite.op V) (homOfLE h).op
  have hf : ∀ (U V T : A.left.affineOpens) (h : V ≤ U) (h' : T ≤ V), ∀ z ∈ pre u.ex T.1,
      val u.ex T.1 (f U T (h'.trans h)) z = val u.ex V.1 (f U V h) z + val u.ex T.1 (f V T h') z := by
    intro U V T h h' z hz
    have e : f U T (h'.trans h) = Sec.res (str A) h' (f U V h) + f V T h' :=
      cechDeRhamTotalCocyclesOne.comp c (homOfLE h).op (homOfLE h').op
    obtain ⟨ev, hev⟩ := halg T.1 z hz
    rw [← hres V.1 T.1 h' _ z hz, e]
    exact (hev _).trans ((map_add ev _ _).trans (congrArg₂ _ (hev _).symm (hev _).symm))
  let h : A.left.affineOpens → (Fin g → ℂ) → ℂ := fun U z ↦
    if hz : z ∈ pre u.ex U.1 then
      k (hbasis U z hz).choose z - val u.ex _ (f U _ (hbasis U z hz).choose_spec.1) z else 0
  have hh : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U z = k i z - val u.ex _ (f U _ hi) z := by
    intro U i hi z hz
    have hzU : z ∈ pre u.ex U.1 := hmono _ _ hi hz
    obtain ⟨hj, hzj⟩ := (hbasis U z hzU).choose_spec
    simp only [h, dif_pos hzU]
    generalize_proofs p1 p2
    generalize p1.choose = j at *
    obtain ⟨l, hli, hlj, hzl, e1, e2⟩ := hcomp i j z hz hzj
    have a1 := hf U _ _ hi hli z hzl
    have a2 := hf U _ _ hj hlj z hzl
    have b1 : k l z = k i z + val u.ex _ (f _ _ hli) z := e1 _
    have b2 : k l z = k j z + val u.ex _ (f _ _ hlj) z := e2 _
    linear_combination b1 - b2 - a1 + a2
  have hnhds : ∀ (U : A.left.affineOpens) i (hi : W i ≤ U), ∀ z ∈ pre u.ex (W i).1,
      h U =ᶠ[nhds z] fun y ↦ k i y - val u.ex _ (f U _ hi) y := fun U i hi z hz ↦
    Filter.eventually_of_mem ((hopen _).mem_nhds hz) fun y hy ↦ hh U i hi y hy
  refine ⟨c, h, rfl, ⟨fun U z hz ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    exact ((((hdiff i).differentiableAt n).sub ((hvd _ _).differentiableAt n)).congr_of_eventuallyEq
      (hnhds U i hi z hzi)).differentiableWithinAt
  · obtain ⟨i, hi, hzi⟩ := hbasis V z hz
    have hVU : V ≤ U := leOfHom a.unop
    have a1 := hf U V _ hVU hi z hzi
    change _ = _ + val u.ex V.1 (f U V hVU) z
    rw [hh V i hi z hzi, hh U i (hi.trans hVU) z hzi, a1]
    ring
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    have n := (hopen _).mem_nhds hzi
    refine (hnhds U i hi z hzi).fderiv_eq.trans ((fderiv_fun_sub ((hdiff i).differentiableAt n)
      ((hvd _ (f U _ hi)).differentiableAt n)).trans ?_)
    rw [hder i z hzi, sub_eq_iff_eq_add]
    refine (congrArg _ (cechDeRhamTotalCocyclesOne.conn c (homOfLE hi).op)).trans ((map_add _ _ _).trans ?_)
    exact congrArg₂ _ (hevres U (W i) (homOfLE hi).op _ z hzi) ((hev _ z hzi).2.2 _)
  · obtain ⟨i, hi, hzi⟩ := hbasis U z hz
    rw [hh U i hi z hzi, hh U i hi _ ((hpp _ l z).2 hzi), hper i l z hzi, hvp _ (f U _ hi)]
    ring

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCechDeRhamPeriodsOfAffineBasisStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : cechDeRhamTotalCocyclesOne (OAff (str A))) (K : Type) (W : K → A.left.affineOpens) (k : K → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ i j, ∀ z ∈ pre u.ex (W i).1, z ∈ pre u.ex (W j).1 → ∃ l, W l ≤ W i ∧ W l ≤ W j ∧ z ∈ pre u.ex (W l).1 ∧ (∀ a : Opposite.op (W i) ⟶ Opposite.op (W l), k l z = k i z + val u.ex (W l).1 (c.1.1 _ _ a) z) ∧ ∀ a : Opposite.op (W j) ⟶ Opposite.op (W l), k l z = k j z + val u.ex (W l).1 (c.1.1 _ _ a) z) → (∀ (U : A.left.affineOpens), ∀ z ∈ pre u.ex U.1, ∃ i, W i ≤ U ∧ z ∈ pre u.ex (W i).1) → (∀ i, DifferentiableOn ℂ (k i) (pre u.ex (W i).1)) → (∀ i, ∀ z ∈ pre u.ex (W i).1, fderiv ℂ (k i) z = evForm u.ex (W i).1 z (c.1.2 (Opposite.op (W i)))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (W i).1, k i (z + l) = k i z + q l) → IsPer u.ex u.Λ (Hyp1.mk _ c) q := by
  first | exact @GlobalTheory.CechPer.isPer_of_basis | exact GlobalTheory.CechPer.isPer_of_basis | (intros; apply GlobalTheory.CechPer.isPer_of_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationLinearPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationLinearPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.CechPer

theorem evForm_secPull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (CechDR.secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  intro A _ g L u A' _ g' L' u' φ M h hM p z hz
  have hpt : ∀ w, (u.ex (M w)).left = (u'.ex w).left ≫ φ.left := fun w => by rw [hM w]; rfl
  have hval : ∀ w ∈ pre u'.ex p.1.1.1, ∀ b, val u'.ex p.1.1.1 (CechDR.secPull (str A) (str A') p b) w =
      val u.ex p.1.2.1 b (M w) := by
    intro w hw b
    have k := valAt'_appLE (u'.ex w).left φ.left p.1.2.1 p.1.1.1 p.2 b hw
    rw [← hpt] at k
    exact k
  have hpre : ∀ w ∈ pre u'.ex p.1.1.1, M w ∈ pre u.ex p.1.2.1 := by
    intro w hw
    change ⊤ ≤ (u.ex (M w)).left ⁻¹ᵁ p.1.2.1
    rw [hpt, top_le_preimage_comp]
    exact fun x hx => p.2 (hw hx)
  refine ⟨hpre z hz, hval z hz, ?_⟩
  have hopen : ∀ U, IsOpen (pre u.ex U) := fun U => (u.hol U 0).1
  have hdiff : ∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U) := fun U b => (u.hol U b).2
  have hopen' : ∀ U, IsOpen (pre u'.ex U) := fun U => (u'.hol U 0).1
  obtain ⟨-, hsm, hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u p.1.2.1 (M z) (hpre z hz)
  obtain ⟨-, hsm', hD'⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' p.1.1.1 z hz
  intro ξ
  have hξ : ξ ∈ Submodule.span (Sec (str A) p.1.2.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) p.1.2.1))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [SemiHom.m1_D, hD', hD]
    have e : val u'.ex p.1.1.1 (CechDR.secPull (str A) (str A') p b) =ᶠ[nhds z] (val u.ex p.1.2.1 b) ∘ M :=
      Filter.eventually_of_mem ((hopen' p.1.1.1).mem_nhds hz) fun w hw => hval w hw b
    rw [e.fderiv_eq, fderiv_comp z ((hdiff _ b).differentiableAt ((hopen _).mem_nhds (hpre z hz)))
      M.differentiableAt, M.fderiv]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), ContinuousLinearMap.add_comp]
  | smul a x _ hx => rw [SemiHom.oneFormMap_smul_semilinear, hsm', hsm, hx, hval z hz a, ContinuousLinearMap.smul_comp]

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationLinearPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedOneFormEvaluation_linear_pullback : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (GlobalTheory.CechDR.secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  first | exact @GlobalTheory.CechPer.evForm_secPull | exact GlobalTheory.CechPer.evForm_secPull | (intros; apply GlobalTheory.CechPer.evForm_secPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerPull
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer.Nat

theorem isPer_pull : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  intro A _ g L u A' _ g' L' u' φ M h hex hM x x' q hp hx
  obtain ⟨c, h₀, rfl, ⟨hd, hc, hw⟩, hq⟩ := hx
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ x'
  have hp' : Hyp1.mk _ (pullZZ1 (pairPull h) c) = Hyp1.mk _ (pullZZ1 (pairRes φ.left (str A')) c') := hp
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 hp'
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9, a10, -, a12⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨b1, b2, b3, b4, b5, b6, -, b8, b9, b10, -, b12⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A' g' L' u'
  let Mc : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap M
  have hP := GlobalTheory.T.uniformisedOneFormEvaluation_linear_pullback A g L u A' g' L' u' φ Mc h hex
  have hpre : ∀ (U : A.left.Opens) z, z ∈ pre u'.ex (φ.left ⁻¹ᵁ U) ↔ M z ∈ pre u.ex U := by
    intro U z
    change ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ.left ⁻¹ᵁ U) ↔ ⊤ ≤ (u.ex (M z)).left ⁻¹ᵁ U
    rw [hex]
    rfl
  have hf : ∀ (p l : Pair φ.left) (e : l ≤ p) (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1)
      (a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2),
      (show Sec (str A') l.1.1.1 from b (Opposite.op l)) - Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p)) =
        CechDR.secPull (str A) (str A') l (c.1.1 _ _ a') - (show Sec (str A') l.1.1.1 from c'.1.1 _ _ a) := by
    intro p l e a a'
    exact congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.1 (Opposite.op p) (Opposite.op l) (homOfLE e).op) hb
  have hω : ∀ (p : Pair φ.left), KaehlerDifferential.D ℂ (Sec (str A') p.1.1.1) (b (Opposite.op p)) =
      (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) -
        (show Ω[Sec (str A') p.1.1.1⁄ℂ] from c'.1.2 (Opposite.op p.1.1)) := by
    intro p
    have e1 := congrArg (fun t : Tot1 (OPair φ.left (str A')) => t.2 (Opposite.op p)) hb
    have e2 : q1 (pairRes φ.left (str A')) (Opposite.op p) (c'.1.2 (Opposite.op p.1.1)) = c'.1.2 (Opposite.op p.1.1) :=
      SemiHom.oneFormMap_eq_self_of_id _ (fun _ => rfl) _
    exact e1.trans (congrArg (fun t => (semiHom_secPull h p).m1 (c.1.2 (Opposite.op p.1.2)) - t) e2)
  have hstep : ∀ (p l : Pair φ.left) (e : l ≤ p), ∀ z ∈ pre u'.ex l.1.1.1, ∀ (a : Opposite.op p.1.1 ⟶ Opposite.op l.1.1),
      h₀ l.1.2 (M z) - val u'.ex l.1.1.1 (b (Opposite.op l)) z =
        h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z + val u'.ex l.1.1.1 (c'.1.1 _ _ a) z := by
    intro p l e z hz a
    obtain ⟨hz', hv, -⟩ := hP l z hz
    let a' : Opposite.op p.1.2 ⟶ Opposite.op l.1.2 := (homOfLE (Pair.le_snd e)).op
    have hs : ∀ x y v w : Sec (str A') l.1.1.1, x - y = v - w →
        val u'.ex l.1.1.1 x z - val u'.ex l.1.1.1 y z = val u'.ex l.1.1.1 v z - val u'.ex l.1.1.1 w z := by
      intro x y v w e
      obtain ⟨ev, hev⟩ := b10 _ z hz
      rw [hev x, hev y, hev v, hev w, ← map_sub, ← map_sub, e]
    have e1 : val u'.ex l.1.1.1 (b (Opposite.op l)) z -
        val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex l.1.1.1 (CechDR.secPull (str A) (str A') l (c.1.1 _ _ a')) z - val u'.ex l.1.1.1 (c'.1.1 _ _ a) z :=
      hs _ _ _ _ (hf p l e a a')
    have e3 : val u'.ex l.1.1.1 (Sec.res (str A') (Pair.le_fst e) (b (Opposite.op p))) z =
        val u'.ex p.1.1.1 (b (Opposite.op p)) z := b9 _ _ _ _ z hz
    have e4 : val u'.ex l.1.1.1 (CechDR.secPull (str A) (str A') l (c.1.1 _ _ a')) z =
        val u.ex l.1.2.1 (c.1.1 _ _ a') (M z) := hv _
    have e2 := hc p.1.2 l.1.2 a' (M z) hz'
    linear_combination e2 - e1 - e3 - e4
  refine GlobalTheory.T.hasCechDeRhamPeriods_of_affine_basis A' g' L' u' c' (Pair φ.left) (fun p => p.1.1)
    (fun p z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z) _ ?_ ?_ ?_ ?_ ?_
  · intro p r z hzp hzr
    have h1 : M z ∈ pre u.ex (p.1.2.1 ⊓ r.1.2.1) := by
      rw [a5]; exact ⟨(hP p z hzp).1, (hP r z hzr).1⟩
    obtain ⟨U, hU, hzU⟩ := a8 _ _ h1
    have h2 : z ∈ pre u'.ex (p.1.1.1 ⊓ r.1.1.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5, b5]; exact ⟨⟨hzp, hzr⟩, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    let l : Pair φ.left := ⟨(W, U), hW.trans inf_le_right⟩
    have lp : l ≤ p := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ p.1.1.1 from hW.trans (inf_le_left.trans inf_le_left), show U.1 ≤ p.1.2.1 from hU.trans inf_le_left⟩)
    have lr : l ≤ r := Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨show W.1 ≤ r.1.1.1 from hW.trans (inf_le_left.trans inf_le_right), show U.1 ≤ r.1.2.1 from hU.trans inf_le_right⟩)
    exact ⟨l, Pair.le_fst lp, Pair.le_fst lr, hzW, hstep p l lp z hzW, hstep r l lr z hzW⟩
  · intro U' z hz
    obtain ⟨U, -, hzU⟩ := a8 _ _ (a12 (M z))
    have h2 : z ∈ pre u'.ex (U'.1 ⊓ φ.left ⁻¹ᵁ U.1) := by
      rw [b5]; exact ⟨hz, (hpre _ _).2 hzU⟩
    obtain ⟨W, hW, hzW⟩ := b8 _ _ h2
    exact ⟨⟨(W, U), hW.trans inf_le_right⟩, show W.1 ≤ U'.1 from hW.trans inf_le_left, hzW⟩
  · intro p
    exact ((hd p.1.2).comp Mc.differentiable.differentiableOn fun z hz => (hP p z hz).1).sub (b2 _ _)
  · intro p z hz
    obtain ⟨hz', -, hE⟩ := hP p z hz
    have d1 : DifferentiableAt ℂ (h₀ p.1.2) (Mc z) := (hd p.1.2).differentiableAt ((a1 _).mem_nhds hz')
    have d2 : DifferentiableAt ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z :=
      (b2 _ _).differentiableAt ((b1 _).mem_nhds hz)
    have d3 : HasFDerivAt (fun z => h₀ p.1.2 (M z) - val u'.ex p.1.1.1 (b (Opposite.op p)) z)
        ((fderiv ℂ (h₀ p.1.2) (Mc z)).comp Mc - fderiv ℂ (val u'.ex p.1.1.1 (b (Opposite.op p))) z) z :=
      (d1.hasFDerivAt.comp z Mc.hasFDerivAt).sub d2.hasFDerivAt
    have e1 := congrArg (evForm u'.ex p.1.1.1 z) (hω p)
    rw [map_sub, hE] at e1
    have e2 := ((GlobalTheory.T.uniformisedOneFormEvaluation_rules A' g' L' u' _ z hz).2.2 (b (Opposite.op p))).symm.trans e1
    rw [d3.fderiv, hw p.1.2 _ hz']
    exact (congrArg (fun t => _ - t) e2).trans (sub_sub_cancel _ _)
  · intro p l z hz
    have e1 := hq p.1.2 ⟨M l, hM l⟩ (M z) (hP p z hz).1
    change h₀ p.1.2 (M (z + l)) - _ = _
    have e2 : val u'.ex p.1.1.1 (b (Opposite.op p)) (z + l) = val u'.ex p.1.1.1 (b (Opposite.op p)) z := b4 _ _ l z
    rw [map_add (f := _), e2]
    change h₀ p.1.2 (M z + M l) = _ at e1
    rw [e1]
    ring

end GlobalTheory.CechPer.Nat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerPullStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPer_of_isPull1_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  first | exact @GlobalTheory.CechPer.Nat.isPer_pull | exact GlobalTheory.CechPer.Nat.isPer_pull | (intros; apply GlobalTheory.CechPer.Nat.isPer_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriods
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem mem_primDR_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  intro A _ g L u hA c p hp
  obtain ⟨n, L', v, M₁, M₂, hAA, h1, h2, h3, hM1, hM2⟩ := GlobalTheory.T.exists_holomorphicUniformisation_square_abelianVariety A g L u hA
  rw [mem_prim_iff]
  have key : ∀ (φ : A ⊗ A ⟶ A) (M : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (_hw : ∀ w, u.ex (M w) = v.ex w ≫ φ)
      (hM : ∀ l : v.Λ, M l ∈ u.Λ),
      IsPer v.ex v.Λ (cmp1 (str (A ⊗ A)) (pullOver (dp0 ℂ) (𝟙 _) φ c)) (fun l ↦ p ⟨M l, hM l⟩) := by
    intro φ M hw hM
    have hm := IsMor.of_over (dp0 ℂ) (φ := φ.left) (s := str A) (s' := str (A ⊗ A))
      (by rw [← Category.assoc, Over.w])
    exact GlobalTheory.T.isPer_of_isPull1_of_isPer A g L u (A ⊗ A) n L' v φ M hm.w hw hM _ _ _ (comparison_pullback hm c) hp
  have hμ := key μ[A] (M₁ + M₂) h3 (fun l ↦ add_mem (hM1 l) (hM2 l))
  have hf := key (fst A A) M₁ h1 hM1
  have hs := key (snd A A) M₂ h2 hM2
  obtain ⟨hlin, -⟩ := GlobalTheory.T.cechDeRhamPeriods_linear (A ⊗ A) n L' v
  have hdiff := (hlin _ _ _ _ hμ (hlin _ _ _ _ hf hs).1).2
  have hq : ((fun l : v.Λ ↦ p ⟨(M₁ + M₂) l, add_mem (hM1 l) (hM2 l)⟩) -
      ((fun l : v.Λ ↦ p ⟨M₁ l, hM1 l⟩) + fun l : v.Λ ↦ p ⟨M₂ l, hM2 l⟩)) = 0 := by
    funext l
    rw [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, sub_eq_zero, ← map_add (f := _)]
    rfl
  rw [hq] at hdiff
  have h0 := GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero (A ⊗ A) n L' v hAA _ hdiff
  rw [← map_add (f := _), ← map_sub] at h0
  exact sub_eq_zero.1 ((GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex (A ⊗ A) hAA).1 (h0.trans (map_zero _).symm))

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriodsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  first | exact @GlobalTheory.CechPer.mem_primDR_of_isPer | exact GlobalTheory.CechPer.mem_primDR_of_isPer | (intros; apply GlobalTheory.CechPer.mem_primDR_of_isPer <;> assumption)
end
