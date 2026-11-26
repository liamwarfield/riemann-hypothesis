module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointTranslatePure
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.TorusTranslate

theorem appLE_res_pullU {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ U) (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h (pullU f U u)).val = (g.appLE U ⊤ hg).hom u.val := by
  subst e
  have : f.app U ≫ Y.presheaf.map (homOfLE h).op ≫ m.appLE W ⊤ hm = (m ≫ f).appLE U ⊤ hg := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appLE]
  exact congrArg (fun φ => φ.hom u.val) this

theorem appLE_app {X Y Z : Scheme.{0}} (m : Z ⟶ Y) (f : Y ⟶ X) (g : Z ⟶ X) (e : m ≫ f = g)
    (U : X.Opens) (hm : ⊤ ≤ m ⁻¹ᵁ (f ⁻¹ᵁ U)) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (u : Γ(X, U)) :
    (m.appLE (f ⁻¹ᵁ U) ⊤ hm).hom ((f.app U).hom u) = (g.appLE U ⊤ hg).hom u := by
  subst e
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem appLE_res {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U W : Y.Opens) (h : W ≤ U)
    (hm : ⊤ ≤ m ⁻¹ᵁ W) (hg : ⊤ ≤ m ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    (m.appLE W ⊤ hm).hom (res h u).val = (m.appLE U ⊤ hg).hom u.val :=
  congrArg (fun φ => φ.hom u.val) (Scheme.Hom.map_appLE m hm (homOfLE h).op)

variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G) {Z : Over S}

theorem torus_comp_q (τ : Z ⟶ splitTorus S E.X) : (τ ≫ D.i) ≫ D.q = 1 := by
  rw [Category.assoc, D.isKernel.w, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

theorem translate_comp_q (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) :
    ((τ ≫ D.i) * x).left ≫ D.q.left = x.left ≫ D.q.left := by
  have := D.q_hom
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, torus_comp_q, _root_.one_mul]

theorem translate_le (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (V : E.B.left.Opens)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage] at h ⊢
  rwa [translate_comp_q]

theorem translate_coord (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (k : Module.Free.ChooseBasisIndex ℤ E.X)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (D.u j k).val =
      τ.left.appTop.hom (charUnit S E.X (E.basis k)).val * (x.left.appLE _ ⊤ h).hom (D.u j k).val := by
  let m : Z ⟶ splitTorus S E.X ⊗ G := lift τ x
  have e1 : m.left ≫ (fst (splitTorus S E.X) G).left = τ.left := by
    rw [← Over.comp_left, lift_fst]
  have e2 : m.left ≫ (snd (splitTorus S E.X) G).left = x.left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : m.left ≫ (lift (fst (splitTorus S E.X) G ≫ D.i) (snd (splitTorus S E.X) G) ≫ μ[G]).left
      = ((τ ≫ D.i) * x).left := by
    rw [← Over.comp_left, Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hm : ⊤ ≤ m.left ⁻¹ᵁ ((snd (splitTorus S E.X) G).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j)) := by
    rw [← Scheme.Hom.comp_preimage, e2]; exact h
  have key := congrArg (m.left.appLE _ ⊤ hm).hom (congrArg Units.val (D.equiv j k))
  simp only [Units.val_mul, map_mul] at key
  rw [appLE_res_pullU _ _ _ e3 _ _ _ hm h'] at key
  rw [key]
  congr 1
  · refine (appLE_res_pullU _ _ _ e1 ⊤ _ _ hm le_top _).trans ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  · exact appLE_app _ _ _ e2 _ hm h _

theorem translate_pure (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) (j : E.ChartIdx)
    (V : E.B.left.Opens) (hV : IsAffineOpen V) (hle : V ≤ E.chart j) (α : E.X)
    (s : Γ(G.left, D.q.left ⁻¹ᵁ V)) (hs : ∀ β, β ≠ α → D.weight j V hV hle β s = 0)
    (h : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V))
    (h' : ⊤ ≤ ((τ ≫ D.i) * x).left ⁻¹ᵁ (D.q.left ⁻¹ᵁ V)) :
    (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom s =
      τ.left.appTop.hom (charUnit S E.X α).val * (x.left.appLE _ ⊤ h).hom s := by
  have hsingle : (Equiv.ofBijective _ (D.coord j V hV hle)).symm s =
      AddMonoidAlgebra.single α (D.weight j V hV hle α s) := by
    apply AddMonoidAlgebra.ext
    ext β
    by_cases hβ : β = α
    · subst hβ
      simp [SplitExt.GtDatum.weight]
    · have := hs β hβ
      rw [SplitExt.GtDatum.weight] at this
      rw [this]
      simp [Ne.symm hβ]
  generalize D.weight j V hV hle α s = w at hsingle
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, AddMonoidAlgebra.liftNCRingHom_single] at hsingle
  let c : E.X →ₗ[ℤ] Additive Γ(G.left, D.q.left ⁻¹ᵁ V)ˣ := E.basis.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)))
  have hs' : s = (D.q.left.app V).hom w * (Additive.toMul (c α)).val := hsingle
  let f₁ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₂ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    (Units.map (x.left.appLE _ ⊤ h).hom.toMonoidHom).toAdditive.comp c.toAddMonoidHom
  let f₀ : E.X →+ Additive Γ(Z.left, ⊤)ˣ :=
    MonoidHom.toAdditiveRight (splitTorusPointsEquiv S E.X Z τ)
  have hf : f₁.toIntLinearMap = (f₀ + f₂).toIntLinearMap := by
    refine E.basis.ext fun k => ?_
    apply Additive.toMul.injective
    apply Units.ext
    have hc : c (E.basis k) = Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left hle) (D.u j k)) := E.basis.constr_basis _ _ _
    change (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c (E.basis k))).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd (E.basis k))).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c (E.basis k))).val
    have g : ⊤ ≤ x.left ⁻¹ᵁ (D.q.left ⁻¹ᵁ E.chart j) :=
      h.trans (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hle))
    rw [hc, toMul_ofMul, splitTorusPointsEquiv_val,
      appLE_res _ _ _ _ h' (translate_le D τ x _ g), appLE_res _ _ _ _ h g]
    exact translate_coord D τ x j k g _
  have hα : (((τ ≫ D.i) * x).left.appLE _ ⊤ h').hom (Additive.toMul (c α)).val =
      (splitTorusPointsEquiv S E.X Z τ (Multiplicative.ofAdd α)).val *
        (x.left.appLE _ ⊤ h).hom (Additive.toMul (c α)).val :=
    congrArg (fun z => (Additive.toMul z).val) (LinearMap.congr_fun hf α)
  have g : ⊤ ≤ (x.left ≫ D.q.left) ⁻¹ᵁ V := h
  rw [hs', map_mul, map_mul, hα, splitTorusPointsEquiv_val,
    appLE_app _ _ _ (translate_comp_q D τ x) V h' g, appLE_app _ _ _ rfl V h g]
  ring

end GlobalTheory.TorusTranslate

namespace GlobalTheory.TorusTranslate

theorem exists_point_translate_pure : (∀ (k : Type) [Field k] (Φ : FibPre k) (t : Multiplicative Φ.E.X →* kˣ), ∃ a : Φ.Pt, a ≫ Φ.D.q = 1 ∧ (∀ n : ℕ, t ^ n = 1 → a ^ n = 1) ∧ ∀ (d : ℕ) (α : Φ.E.X) (φ : (Φ.H d).Sec), Φ.Pure α φ → ∀ (x : Φ.Pt) (l : Φ.N₀.ι), ⊤ ≤ x.left ⁻¹ᵁ (Φ.H d).U l → ⊤ ≤ (a * x).left ⁻¹ᵁ (Φ.H d).U l ∧ valF (a * x).left ((Φ.H d).U l) (φ.f l) = (t (Multiplicative.ofAdd α) : k) * valF x.left ((Φ.H d).U l) (φ.f l)) := by
  intro k _ Φ t
  have := Φ.D.i_hom
  let κ : kˣ →* Γ((Out.baseOver (Sp k)).left, ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom
  let e := splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k))
  let τ := e.symm (κ.comp t)
  have hτ : e τ = κ.comp t := e.apply_symm_apply _
  refine ⟨τ ≫ Φ.D.i, torus_comp_q Φ.D τ, fun n hn => ?_, fun d α φ hφ x l hx => ?_⟩
  · have : τ ^ n = 1 := by
      apply e.injective
      rw [map_pow, map_one, hτ]
      refine MonoidHom.ext fun χ => ?_
      have := DFunLike.congr_fun hn χ
      rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, this, map_one, MonoidHom.one_apply]
    rw [← MonObj.pow_comp, this, MonObj.one_comp]
  · have hx' := translate_le Φ.D τ x (Φ.N₀.U l) hx
    refine ⟨hx', ?_⟩
    have key := translate_pure Φ.D τ x (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α (φ.f l)
      (fun β hβ => by
        by_contra hne
        exact hβ (hφ ⟨l, hne⟩)) hx hx'
    rw [← splitTorusPointsEquiv_val] at key
    have hv : (splitTorusPointsEquiv (Sp k) Φ.E.X (Out.baseOver (Sp k)) τ
        (Multiplicative.ofAdd α)).val =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (t (Multiplicative.ofAdd α) : k) := by
      change (e τ _).val = _
      rw [hτ]; rfl
    rw [hv] at key
    have key2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom key
    refine Eq.trans ?_ (Eq.trans key2 (Eq.trans ((map_mul _ _ _)) ?_))
    · exact dif_pos hx'
    · congr 1
      · exact Iso.inv_hom_id_apply _ _
      · symm
        exact dif_pos hx

end GlobalTheory.TorusTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HilbEqFinrankQuotPiece
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

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

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

end GlobalTheory.ZH
end
