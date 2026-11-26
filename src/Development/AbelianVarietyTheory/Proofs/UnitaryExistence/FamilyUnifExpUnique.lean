module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstMinimumLowerBoundNearMax
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsActionOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExpUniqFamily

theorem linear_eq_zero_of_discrete {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ]
    (f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, f z ∈ Λ) (z : Fin g → ℂ) : f z = 0 := by
  have hc : Continuous (fun z => (⟨f z, hf z⟩ : Λ)) :=
    f.continuous_of_finiteDimensional.subtype_mk _
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa using this

theorem eq_iff_sub {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  have h := he (z - w) w
  rw [sub_add_cancel] at h
  rw [h]
  exact mul_eq_right

theorem int_eq_of_exp (n n' : ℤ)
    (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n' : ℂ) / k)) : n = n' := by
  have hk : 0 < (n' - n).natAbs + 1 := Nat.succ_pos _
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  generalize hkk : (n' - n).natAbs + 1 = k at hk hm
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : ((n' - n : ℤ) : ℂ) = ((k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hm ⊢
    linear_combination hm
  have h4 : n' - n = k * m := Int.cast_injective h3
  have h5 : n' - n = 0 := Int.eq_zero_of_abs_lt_dvd (m := k) ⟨m, h4⟩ (by
    rw [← hkk, Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem algebraic {O Q L L' : Type} [CommRing O] [Group Q] [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {g : ℕ} (χ : Fin g → O → ℂ) (P : L →+ (Fin g → ℂ)) (P' : L' →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x i, P (a • x) i = χ i a * P x i) (hP' : ∀ (a : O) x i, P' (a • x) i = χ i a * P' x i)
    (iP : Function.Injective P) (iP' : Function.Injective P')
    (dP : DiscreteTopology P.range) (dP' : DiscreteTopology P'.range)
    (e e' : (Fin g → ℂ) → Q) (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (act : O → Q → Q) (hl : ∀ a z, e (fun k => χ k a * z k) = act a (e z))
    (hl' : ∀ a z, e' (fun k => χ k a * z k) = act a (e' z))
    (f f' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, e' (f z) = e z) (hf' : ∀ z, e (f' z) = e' z) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : L ≃ₗ[O] L'), (∀ z, e' (h z) = e z) ∧
      (∀ a, P' (gam a) = h (P a)) ∧
      ∀ (k : ℕ) a b, 0 < k → e ((k : ℂ)⁻¹ • P a) = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  have h1 : ∀ z, f' (f z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P.range (f' ∘ₗ f - LinearMap.id) (fun z => (hk _).1 <|
      (eq_iff_sub e ha _ _).1 (by simp [hf, hf'])) z
  have h2 : ∀ z, f (f' z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ f' - LinearMap.id) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp [hf, hf'])) z
  let d : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => LinearMap.pi fun k => χ k a • LinearMap.proj k
  have hd : ∀ a z, d a z = fun k => χ k a * z k := fun a z => rfl
  have h3 : ∀ a z, f (d a z) = d a (f z) := fun a z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ d a - d a ∘ₗ f) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp only [LinearMap.comp_apply, hf, hd, hl, hl'])) z
  have m1 : ∀ a, ∃ b, P' b = f (P a) := fun a => (hk' _).1 (by rw [hf]; exact (hk _).2 ⟨a, rfl⟩)
  have m2 : ∀ b, ∃ a, P a = f' (P' b) := fun b => (hk _).1 (by rw [hf']; exact (hk' _).2 ⟨b, rfl⟩)
  choose ga hga using m1
  choose de hde using m2
  let gam : L ≃ₗ[O] L' :=
    { toFun := ga
      invFun := de
      map_add' := fun a b => iP' (by simp [hga])
      map_smul' := fun c a => iP' (by
        have e1 : P (c • a) = d c (P a) := funext fun i => hP c a i
        have e2 : P' (c • ga a) = d c (P' (ga a)) := funext fun i => hP' c _ i
        rw [RingHom.id_apply, hga, e1, e2, hga, h3])
      left_inv := fun a => iP (by rw [hde, hga, h1])
      right_inv := fun b => iP' (by rw [hga, hde, h2]) }
  refine ⟨LinearEquiv.ofLinear f f' (LinearMap.ext h2) (LinearMap.ext h1), gam, hf, hga, ?_⟩
  intro k a b hk0 hab
  have hk1 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  rw [← hf, map_smul, ← hga, eq_iff_sub e' ha', hk'] at hab
  obtain ⟨c, hc⟩ := hab
  refine ⟨c, iP' ?_⟩
  show P' (ga a) = _
  rw [map_add (f := _), map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hk1, one_smul]
  abel

theorem isHolTo_fibre {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} (y : V × W → (Sp ℂ ⟶ X)) (h : IsHolTo (Set.univ ×ˢ Set.univ) y) (b : V) :
    IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hd : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have := h1.preimage hd.continuous
    convert this using 1
    ext z
    simp
  · exact h2.comp hd.differentiableOn (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_ex {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (U.Di i) ty P) : IsHolTo Set.univ (fun z => (U.ex i P z).left) :=
  isHolTo_fibre _ (U.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 0

theorem fibrewise {X : Scheme.{0}} (t : SAB H X) (D₁ D₂ : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (hy : y = y') (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd : (∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
      ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
        ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e' (h z)).left = (e z).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') ∧
      ∀ (k : ℕ) (s : 𝟙_ (Over X) ⟶ t.G) a b, 0 < k → toUnit _ ≫ s = e ((k : ℂ)⁻¹ • P a) →
        toUnit _ ≫ s = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  subst hy
  have dk : DiscreteTopology {z // e z = 1} := by
    have h0 : (fun z => e z = 1) = fun z => z ∈ P.range := funext fun z => propext (hk z)
    show DiscreteTopology (Subtype fun z => e z = 1)
    rw [h0]
    exact hP.2.2.1
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres X X t.G t.G y y g g e e' (𝟙 _) (MonoidHom.id _) t.semi.smooth ha ha' hh hh' hd' dk'
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨f', hf', -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres X X t.G t.G y y g g e' e (𝟙 _) (MonoidHom.id _) t.semi.smooth ha' ha hh' hh hd dk
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨h, gam, h1, h2, h3⟩ := algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1 hP.2.1 hP'.2.1
    hP.2.2.1 hP'.2.2.1 e e' ha ha' hk hk' (fun a x => x ≫ t.act.act a) hl hl' f f' hf hf'
  refine ⟨h, gam, fun z => by rw [h1], h2, fun a a' => ?_, fun k s a b hk0 e1 e2 => h3 k a b hk0 (e1.symm.trans e2)⟩
  refine int_eq_of_exp _ _ fun k hk0 => ?_
  have w1 := hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t.G t.PP.L t.PP.isLB ℂ y k _ _ _ _ w2 w1)

end ExpUniqFamily

theorem familyUnif_exp_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i j P P' hP hP' hu
  obtain ⟨h, gam, h1, h2, h3, h4⟩ := ExpUniqFamily.fibrewise Xo.univ.t (U.Di i) (U.Di j) ty P P' hP hP' _ _ hu
    (U.ex i P) (U.ex j P') (U.ex_add i P hP) (U.ex_add j P' hP') (U.ex_ker i P hP) (U.ex_ker j P' hP')
    (U.ex_lin i P hP) (U.ex_lin j P' hP') (U.ex_weil i P hP) (U.ex_weil j P' hP')
    (ExpUniqFamily.isHolTo_ex U i P hP) (ExpUniqFamily.isHolTo_ex U j P' hP') (U.ex_diff i P hP) (U.ex_diff j P' hP')
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  exact ⟨h, gam, h1, h2, h3,
    fun a ha => h4 l.M _ _ _ hM (U.ex_eta i P hP a ha) (U.ex_eta j P' hP' a ha),
    fun a => h4 l.A _ _ _ l.A_pos (U.ex_etaA i P hP a) (U.ex_etaA j P' hP' a)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUniqueStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.familyUnif_exp_unique_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by
  first | exact @GlobalTheory.familyUnif_exp_unique | exact GlobalTheory.familyUnif_exp_unique | (intros; apply GlobalTheory.familyUnif_exp_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_mem_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    {P : FDSec X} (hP : P ∈ holSub X la) (k : Comp) : P k ∈ (X k).SS (la k) := by
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0
  induction hP using Submodule.span_induction with
  | mem P hP => exact hP k
  | zero => exact h0
  | add P Q _ _ h1 h2 => exact hadd _ h1 _ h2
  | smul a P _ h1 => exact hsmul a _ h1

end GlobalTheory.CuspSecFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
noncomputable section

namespace GlobalTheory.ValuativeExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem valuation_extension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (oV : O →+* V) (fK : c.F →+* K) (y : Sp K ⟶ Xo.XF c), (algebraMap V K).comp oV = fK.comp β → y ≫ pullback.snd _ _ = spMap fK → (∃! yt : Sp V ⟶ Y.X, yt ≫ Y.s = spMap oV ∧ spMap (algebraMap V K) ≫ yt = y ≫ Y.j) ∧ ∀ yt : Sp V ⟶ Y.X, ∃ G : SAB H (Sp V), Nonempty (SABMap G Y.t yt) := by
  intro E _ _ _ H D l Xo c O _ β Y V K _ _ _ _ _ _ oV fK y ho hy
  obtain ⟨h1, h2, -⟩ := GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y
  exact ⟨h1 V K oV fK y ho hy, fun yt => h2 _ yt⟩

end GlobalTheory.ValuativeExtension
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_ev_eq_iff_add (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ c, a = b + n • c := by
  rw [tateIso_ev_eq_iff I hn]
  exact exists_congr fun c => sub_eq_iff_eq_add'

theorem tateIso_exists_lift_of_two_data (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  let R : Submodule (𝓞 E) (D.La × D'.La) :=
    { carrier := {p | I.ev n p.1 = I'.ev n p.2}
      add_mem' := fun {p q} hp hq => by
        change I.ev n (p.1 + q.1) = I'.ev n (p.2 + q.2)
        rw [I.add, I'.add, show I.ev n p.1 = I'.ev n p.2 from hp, show I.ev n q.1 = I'.ev n q.2 from hq]
      zero_mem' := by
        change I.ev n 0 = I'.ev n 0
        rw [(I.ker n hn 0).2 ⟨0, by simp⟩, (I'.ker n hn 0).2 ⟨0, by simp⟩]
      smul_mem' := fun c p hp => by
        change I.ev n (c • p.1) = I'.ev n (c • p.2)
        rw [I.lin, I'.lin, show I.ev n p.1 = I'.ev n p.2 from hp] }
  have hs : Function.Surjective ((LinearMap.fst (𝓞 E) D.La D'.La).comp R.subtype) := fun a => by
    obtain ⟨b, hb⟩ := (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  haveI := D.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  refine ⟨((LinearMap.snd (𝓞 E) D.La D'.La).comp R.subtype).comp s, fun a => ?_⟩
  have h1 : (s a).1.1 = a := LinearMap.congr_fun hs a
  have h2 : I.ev n (s a).1.1 = I'.ev n (s a).1.2 := (s a).2
  rw [h1] at h2
  exact h2

theorem tateIso_similar_of_two_data
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      ∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

noncomputable def expNegUnit (n : ℕ) : ℂˣ :=
  (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n)) (Complex.exp_ne_zero _))⁻¹

theorem expNegUnit_zpow_val (n : ℕ) (j : ℤ) :
    ((expNegUnit n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expNegUnit, Units.val_inv_eq_inv_val, Units.val_mk0, ← Complex.exp_neg,
    ← Complex.exp_int_mul]
  congr 1
  ring

theorem expNegUnit_isPrimitiveRoot {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expNegUnit n) n :=
  (IsPrimitiveRoot.coe_units_iff.1 (Complex.isPrimitiveRoot_exp n hn.ne')).inv

theorem expNegUnit_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expNegUnit (n * m) ^ m = expNegUnit n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [← zpow_natCast, expNegUnit_zpow_val, ← zpow_one (expNegUnit n), expNegUnit_zpow_val]
  congr 1
  push_cast
  field_simp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) {i : Fin U.n}
  {P : (U.Di i).La →+ (Fin g → ℂ)}

theorem familyUnif_ex_nsmul (hP : IsPeriod (U.Di i) ty P) (n : ℕ) (z : Fin g → ℂ) :
    U.ex i P ((n : ℂ) • z) = U.ex i P z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (U.ex_ker i P hP 0).2 (zero_mem _)
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, U.ex_add i P hP, ih, pow_succ]

noncomputable def familyUnifTateIso (hP : IsPeriod (U.Di i) ty P) :
    TateIso (U.Di i) ℂ (Over.mk (U.u i P) ⟶ Xo.univ.t.G) (fun a x => x ≫ Xo.univ.t.act.act a)
      (fun n x x' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c)) where
  ζ := expNegUnit
  ζ_prim _ hn := expNegUnit_isPrimitiveRoot hn
  ζ_pow _ _ hn hm := expNegUnit_mul_pow hn hm
  ev n a := U.ex i P ((n : ℂ)⁻¹ • P a)
  add n a b := by rw [map_add (f := _), smul_add, U.ex_add i P hP]
  lin n c a := by
    rw [← U.ex_lin i P hP]
    congr 1
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, hP.1 c a k]
    exact mul_left_comm _ _ _
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [U.ex_ker i P hP]
    refine exists_congr fun b => ?_
    rw [eq_inv_smul_iff₀ hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.2.1.eq_iff, eq_comm]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := U.ex_onto i P hP x
      rw [← familyUnif_ex_nsmul U hP, U.ex_ker i P hP] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, inv_smul_smul₀ hn']⟩
    · rintro ⟨a, rfl⟩
      rw [← familyUnif_ex_nsmul U hP, smul_inv_smul₀ hn', U.ex_ker i P hP]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← familyUnif_ex_nsmul U hP, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := U.ex_weil i P hP n a b _ hn (expNegUnit_zpow_val n _)

end

theorem familyUnif_lattice_similar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧ ∀ a, ∃ e, f l.A a = U.t i a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨-, I, -, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6⟩ := tateIso_similar_of_two_data
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h3, h4, h5, fun a ha => ?_, fun a => ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsTangentVectorBasisAtPointBaseChange
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open scoped CategoryTheory.Obj

namespace GlobalTheory.Frames

theorem tanBasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), TanBasis x v → TanBasis (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x n v hv
  have := Xo.univ.t.semi.comm
  have := Xo.univ.t.semi.smooth
  have h₁ := isGrpPullback_pullback Xo.univ.t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj Xo.univ.t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj Xo.univ.t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj Xo.univ.t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo S x _ _ h₁
  obtain ⟨-, b₃⟩ := GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo T _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv.1 i)
  have hb : IsLieBasis u := (b₁ n u).2 (by rw [funext hu]; exact hv)
  have hs : Smooth ((Over.pullback x).obj Xo.univ.t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd Xo.univ.t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  convert key using 2 with i
  rw [← Category.assoc, hu', e, Category.assoc, hu]

end GlobalTheory.Frames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem valAt_eq_of_finite_values_anyLevel :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty c j f S hS hval i P P' hP hP' x x' hx1 hx2 hx1' hx2'
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hcont : ContinuousOn (fun b => valAt' (y b) ⊤ f) B :=
    ((hhol ⊤ f).2.mono fun b hb => ⟨hb, le_of_eq rfl⟩).continuousOn
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  rw [← e, ← e']
  exact hBc.isPreconnected.constant_of_mapsTo hS.isDiscrete hcont (fun a ha => hval _ (hy2 a ha)) hb hb'

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularFunction_const_of_finite_values_any_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  first | exact @GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel | exact GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel | (intros; apply GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexLinearOfPureTypes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice {A V W : Type} [AddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (P : A →+ V) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) (Q : A →+ W) :
    ∃ r : V →ₗ[ℝ] W, ∀ a, r (P a) = Q a := by
  set L : Submodule ℤ V := P.range.toIntSubmodule with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by simpa [hL] using hs⟩
  let b := Module.Free.chooseBasis ℤ L
  let e : A ≃+ P.range := AddMonoidHom.ofInjective hi
  let r : V →ₗ[ℝ] W := (b.ofZLatticeBasis ℝ L).constr ℝ (fun i => Q (e.symm (b i)))
  refine ⟨r, fun a => ?_⟩
  let f₁ : L →+ W := r.toAddMonoidHom.comp L.subtype.toAddMonoidHom
  let f₂ : L →+ W := Q.comp e.symm.toAddMonoidHom
  have hf : f₁.toIntLinearMap = f₂.toIntLinearMap := by
    refine b.ext fun i => ?_
    show r (b i : V) = Q (e.symm (b i))
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ L b i]
    exact (b.ofZLatticeBasis ℝ L).constr_basis ℝ (fun i => Q (e.symm (b i))) i
  have h : r (P a) = Q (e.symm ⟨P a, a, rfl⟩) := LinearMap.congr_fun hf ⟨P a, a, rfl⟩
  have he : e.symm ⟨P a, a, rfl⟩ = a := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [h, he]

theorem _root_.GlobalTheory.CompRat.exists_complex_linear_of_pure_types : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) (hP' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La), _root_.GlobalTheory.CompRat.IsSplit hP → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP H.rt0, Φ a ∈ _root_.GlobalTheory.PureType.lat hP' H.rt0) → (∀ a ∈ _root_.GlobalTheory.PureType.lat hP (-H.rt0), Φ a ∈ _root_.GlobalTheory.PureType.lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ hsplit h₁ h₂
  have hP₀ := hP
  have hP'₀ := hP'
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod at hP₀ hP'₀
  obtain ⟨-, hi, hd, hs, -⟩ := hP₀
  obtain ⟨-, hi', hd', hs', -⟩ := hP'₀
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P hi hd hs
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  obtain ⟨r', hr'⟩ := _root_.GlobalTheory.CompRat.exists_real_extension_of_lattice P' hi' hd' hs'
    (P.comp Φ.symm.toLinearMap.toAddMonoidHom)
  have hr₁ : ∀ a, r (P a) = P' (Φ a) := hr
  have hr'₁ : ∀ b, r' (P' b) = P (Φ.symm b) := hr'
  have him : H.rt0.im ≠ 0 := by
    intro h0
    have hsq : (H.rt0 ^ 2).re = H.rt0.re ^ 2 := by simp [pow_two, Complex.mul_re, h0]
    rw [H.sqrt_neg_disc_sq] at hsq
    have h2 : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    simp at hsq
    nlinarith [sq_nonneg H.rt0.re]
  have hsplit' : _root_.GlobalTheory.PureType.lat hP H.rt0 ⊔ _root_.GlobalTheory.PureType.lat hP (-H.rt0) = ⊤ :=
    hsplit
  have hkey : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsplit' ▸ Submodule.mem_top : a ∈ _)
    have ry : r (H.rt0 • P y) = H.rt0 • r (P y) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hy, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₁ y hy)]
    have rz : r (-H.rt0 • P z) = -H.rt0 • r (P z) := by
      rw [← _root_.GlobalTheory.PureType.period_rt_smul hP hz, hr₁, hr₁, map_smul,
        _root_.GlobalTheory.PureType.period_rt_smul hP' (h₂ z hz)]
    have rz' : r (H.rt0 • P z) = H.rt0 • r (P z) := by
      rw [neg_smul, map_neg, neg_smul, neg_inj] at rz
      exact rz
    simp only [map_add (f := _), smul_add, ry, rz']
  have hrot : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    have hext : r.comp (H.rt0 • LinearMap.id) = (H.rt0 • LinearMap.id).comp r :=
      LinearMap.ext_on_range hs fun a => by simpa using hkey a
    intro v
    simpa using LinearMap.congr_fun hext v
  have hlin : ∀ (c : ℂ) v, r (c • v) = c • r v := by
    intro c v
    have hc : c = ((c.re - c.im / H.rt0.im * H.rt0.re : ℝ) : ℂ) +
        ((c.im / H.rt0.im : ℝ) : ℂ) * H.rt0 := by
      apply Complex.ext <;> simp <;> field_simp <;> ring
    rw [hc, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add (f := _), map_smul, map_smul,
      hrot, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hl : ∀ v, r' (r v) = v := by
    have hext : r'.comp r = LinearMap.id :=
      LinearMap.ext_on_range hs fun a => by simp [hr₁, hr'₁]
    exact fun v => LinearMap.congr_fun hext v
  have hrr : ∀ w, r (r' w) = w := by
    have hext : r.comp r' = LinearMap.id :=
      LinearMap.ext_on_range hs' fun b => by simp [hr₁, hr'₁]
    exact fun w => LinearMap.congr_fun hext w
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r, map_add' := r.map_add, map_smul' := hlin }
  exact ⟨LinearEquiv.ofBijective L ⟨Function.LeftInverse.injective (g := r') hl,
    fun w => ⟨r' w, hrr w⟩⟩, fun a => (hr₁ a).symm⟩

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesOnPeriodSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesOnPeriodSpace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem valAt_eq_of_finite_values :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty _ c j f S hS hval i P P' hP hP' x x' hx1 hx2 hx1' hx2'
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hcont : ContinuousOn (fun b => valAt' (y b) ⊤ f) B :=
    ((hhol ⊤ f).2.mono fun b hb => ⟨hb, le_of_eq rfl⟩).continuousOn
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  rw [← e, ← e']
  exact hBc.isPreconnected.constant_of_mapsTo hS.isDiscrete hcont (fun a ha => hval _ (hy2 a ha)) hb hb'

end GlobalTheory.CompRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesOnPeriodSpaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularFunction_const_of_finite_values_on_period_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ (c : Coeff l) (j : c.F →+* ℂ) (f : Γ(Xo.XF c, ⊤)) (S : Set ℂ), S.Finite → (∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f ∈ S) → ∀ i P P', IsPeriod (F.Di i) ty P → IsPeriod (F.Di i) ty P' → ∀ x x' : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i P → x ≫ pullback.snd _ _ = spMap j → x' ≫ pullback.fst _ _ = F.u i P' → x' ≫ pullback.snd _ _ = spMap j → valAt' x ⊤ f = valAt' x' ⊤ f := by
  first | exact @GlobalTheory.CompRat.valAt_eq_of_finite_values | exact GlobalTheory.CompRat.valAt_eq_of_finite_values | (intros; apply GlobalTheory.CompRat.valAt_eq_of_finite_values <;> assumption)
end
end
