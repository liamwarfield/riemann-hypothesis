module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTan

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

@[simp] theorem fst_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).fst = φ a.fst := by
  simp [dualMapR]

@[simp] theorem snd_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).snd = φ a.snd := by
  simp [dualMapR]

theorem dualMapR_inl (φ : R →+* R') (a : R) : dualMapR φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a) := by
  ext <;> simp

theorem dualMapR_eps (φ : R →+* R') : dualMapR φ DualNumber.eps = DualNumber.eps := by
  ext <;> simp

theorem eq_dualMapR (φ : R →+* R') (ρ : DualNumber R →+* DualNumber R')
    (h : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r)) (he : ρ DualNumber.eps = DualNumber.eps) :
    ρ = dualMapR φ := RingHom.ext fun a => by
  have e : a = TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, he, dualMapR_inl, dualMapR_inl, dualMapR_eps]

theorem isLocalRing_dual (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

end Dual

abbrev idealEps : Ideal (DualNumber ℂ⟦X⟧) :=
  (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))

theorem isAdicComplete_idealEps : IsAdicComplete idealEps (DualNumber ℂ⟦X⟧) :=
  have : Module.Finite ℂ⟦X⟧ (DualNumber ℂ⟦X⟧) := inferInstanceAs (Module.Finite ℂ⟦X⟧ (ℂ⟦X⟧ × ℂ⟦X⟧))
  isAdicComplete_map_of_finite _ (DualNumber ℂ⟦X⟧)

abbrev constEps : DualNumber ℂ →+* DualNumber ℂ⟦X⟧ := dualMapR (PowerSeries.C (R := ℂ))

section Jet

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def jet (F : V → ℂ) (z : V) : DualNumber ℂ := TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (fderiv ℂ F 0 z)

@[simp] theorem fst_jet (F : V → ℂ) (z : V) : (jet F z).fst = F 0 := by simp [jet]

@[simp] theorem snd_jet (F : V → ℂ) (z : V) : (jet F z).snd = fderiv ℂ F 0 z := by simp [jet]

theorem jet_mul {F G : V → ℂ} (hF : DifferentiableAt ℂ F 0) (hG : DifferentiableAt ℂ G 0) (z : V) :
    jet (fun v => F v * G v) z = jet F z * jet G z := by
  ext
  · simp
  · rw [snd_jet, fderiv_fun_mul hF hG]
    simp [TrivSqZeroExt.snd_mul, _root_.mul_comm]

theorem jet_pow {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) (n : ℕ) :
    jet (fun v => F v ^ n) z = jet F z ^ n := by
  induction n with
  | zero => ext <;> simp
  | succ n ih => rw [pow_succ, ← ih, ← jet_mul (hF.fun_pow n) hF]; simp only [pow_succ]

theorem jet_congr {F G : V → ℂ} (h : F =ᶠ[nhds 0] G) (z : V) : jet F z = jet G z := by
  rw [jet, jet, h.eq_of_nhds, h.fderiv_eq]

def IsJet (x : V → ℂ⟦X⟧) (z : V) (y : DualNumber ℂ⟦X⟧) : Prop :=
  (∀ n, DifferentiableAt ℂ (fun v => PowerSeries.coeff n (x v)) 0) ∧ y.fst = x 0 ∧
    ∀ n, PowerSeries.coeff n y.snd = fderiv ℂ (fun v => PowerSeries.coeff n (x v)) 0 z

variable {z : V}

theorem isJet_zero (z : V) : IsJet (fun _ => 0) z 0 := ⟨fun n => by simp, rfl, fun n => by simp⟩

theorem IsJet.add {x x' : V → ℂ⟦X⟧} {y y' : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (h' : IsJet x' z y') :
    IsJet (fun v => x v + x' v) z (y + y') := by
  refine ⟨fun n => ?_, by simp [h.2.1, h'.2.1], fun n => ?_⟩
  · simp only [map_add (f := _)]
    exact (h.1 n).fun_add (h'.1 n)
  · simp only [map_add (f := _), TrivSqZeroExt.snd_add]
    rw [fderiv_fun_add (h.1 n) (h'.1 n), h.2.2, h'.2.2, ContinuousLinearMap.add_apply]

theorem IsJet.sum {K : Type} (s : Finset K) {x : K → V → ℂ⟦X⟧} {y : K → DualNumber ℂ⟦X⟧}
    (h : ∀ i ∈ s, IsJet (x i) z (y i)) : IsJet (fun v => ∑ i ∈ s, x i v) z (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isJet_zero z
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsJet.const_mul {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (r : ℂ⟦X⟧) :
    IsJet (fun v => r * x v) z (TrivSqZeroExt.inl r * y) := by
  refine ⟨fun n => ?_, by simp [h.2.1], fun n => ?_⟩
  · simp only [PowerSeries.coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ => (h.1 _).const_mul _
  · have e : (TrivSqZeroExt.inl r * y : DualNumber ℂ⟦X⟧).snd = r * y.snd := by simp [TrivSqZeroExt.snd_mul]
    simp only [e, PowerSeries.coeff_mul]
    rw [fderiv_fun_sum fun p _ => (h.1 _).const_mul _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [fderiv_const_mul (h.1 _), h.2.2]
    rfl

theorem isJet_C {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) :
    IsJet (fun v => PowerSeries.C (F v)) z (constEps (jet F z)) := by
  refine ⟨fun n => ?_, by simp, fun n => ?_⟩
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn, hF]
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem mem_idealEps_pow {a : DualNumber ℂ⟦X⟧} {n : ℕ} (h : a ∈ idealEps ^ n) :
    PowerSeries.X ^ n ∣ a.fst ∧ PowerSeries.X ^ n ∣ a.snd := by
  rw [idealEps, ← Ideal.map_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at h
  obtain ⟨c, rfl⟩ := h
  exact ⟨⟨c.fst, by simp [TrivSqZeroExt.algebraMap_eq_inl]⟩, ⟨c.snd, by
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]; simp⟩⟩

theorem isJet_of_approx {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧}
    (h : ∀ e : ℕ, ∃ x' y', IsJet x' z y' ∧ (∀ v, PowerSeries.X ^ (e + 1) ∣ x v - x' v) ∧ y - y' ∈ idealEps ^ (e + 1)) :
    IsJet x z y := by
  have key : ∀ (n : ℕ) (a b : ℂ⟦X⟧), PowerSeries.X ^ (n + 1) ∣ a - b →
      PowerSeries.coeff n a = PowerSeries.coeff n b := fun n a b hab => by
    have := PowerSeries.X_pow_dvd_iff.1 hab n (Nat.lt_succ_self n)
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨fun n => ?_, PowerSeries.ext fun n => ?_, fun n => ?_⟩
  · obtain ⟨x', y', h₁, h₂, -⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    exact h₁.1 n
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    rw [key n _ _ (h₂ 0), ← h₁.2.1]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).1)
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    rw [← h₁.2.2]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).2)

theorem IsJet.dualMapR_eq {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (m : ℤ) (f : V → ℂ⸨X⸩)
    (hf : ∀ v, algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (x v) = HahnSeries.single m (1 : ℂ) * f v) (F : ℂ⸨X⸩)
    (hF : ∀ n, F.coeff n = fderiv ℂ (fun v => (f v).coeff n) 0 z) :
    dualMapR (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) y = TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) := by
  have c : ∀ (g : ℂ⸨X⸩) (n : ℤ), (HahnSeries.single m (1 : ℂ) * g).coeff (n + m) = g.coeff n := fun g n => by
    rw [HahnSeries.coeff_single_mul_add, _root_.one_mul]
  refine TrivSqZeroExt.ext (by simp [h.2.1, hf]) ?_
  have e : (TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) : DualNumber ℂ⸨X⸩).snd = HahnSeries.single m (1 : ℂ) * F := by
    simp [TrivSqZeroExt.snd_mul]
  rw [e, snd_dualMapR]
  ext k
  obtain ⟨n, rfl⟩ : ∃ n, k = n + m := ⟨k - m, by ring⟩
  rw [c, hF]
  simp only [fun v => (c (f v) n).symm.trans (congrArg (fun q : ℂ⸨X⸩ => q.coeff (n + m)) (hf v).symm)]
  generalize n + m = k
  rw [LaurentSeries.coe_algebraMap]
  simp only [PowerSeries.coeff_coe]
  by_cases hk : k < 0
  · simp [hk]
  · simp only [if_neg hk]
    exact h.2.2 _

end Jet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}

def TanRel (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ)
    (ν : Out.GtPt a.D₀ (epsR ℂ)) (g : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) : Prop :=
  ∀ x, GenRelR (A := DualNumber ℂ⟦X⟧) W.w (g.s (W.e x)) (LB.pullGen _ _ _ (ν.s x) (spMap constEps))

def IsConstMul (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ)
    (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) : Prop :=
  ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z)
    (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ →
    (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e x) i) ⁻¹ᵁ
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
    ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) =
        valR (p ≫ W.P.D.toPre.famφB (W.e x) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧
      (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) *
          valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e x)) jf) (f.f jf) =
        κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB x) j₀) (s₀.f j₀)

def HasConstExp (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) {j : ℕ}
    (σ : Out.H0 W.P.U.LG.L j) : Prop :=
  ∃ f : ∀ y, W.P.D.toPre.SecB j y, (∀ e, W.P.U.toUnifPre.ExpandsAt e j σ f) ∧
    ∀ x : a.D₀.X, ∃ s₀ r, IsConstMul W j x s₀ (f (W.e x)) r

end GlobalTheory.ConstTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTerm

section Values

variable {A : Type} [CommRing A] {B B₀ : Scheme.{0}}

theorem valR_zpow (x : Sp A ⟶ B) (U : B.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (t : Γ(B, U)ˣ) (u : Aˣ)
    (hu : (u : A) = valR x U t.val) (n : ℤ) : valR x U (t ^ n).val = ((u ^ n : Aˣ) : A) := by
  have e : u = Units.map (HolHom.evalHom x U h).toMonoidHom t := Units.ext (hu.trans (HolHom.valR_eq x U h _))
  rw [e, ← map_zpow, HolHom.valR_eq x U h]
  rfl

theorem le_div {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} (x : Sp A ⟶ B) {k : M₀.ι} {m : M.ι}
    (h₀ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ M₀.U k) (h : ⊤ ≤ x ⁻¹ᵁ M.U m) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => k, m) :=
  fun _ hz => ⟨Set.mem_iInter.2 fun _ => h₀ hz, h hz⟩

theorem valR_pullGen {A₀ : Type} [CommRing A₀] (ρ : A₀ →+* A) {M₀ : LB B₀} {K : Type} [Fintype K]
    {ψ : K → (Sp A₀ ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M₀ ψ ε)) (k : K → M₀.ι)
    (h : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ LB.wchart M₀ ψ k) :
    valR (𝟙 (Sp A)) _ ((LB.pullGen M₀ ψ ε t (spMap ρ)).s k).val = ρ (valR (𝟙 (Sp A₀)) _ (t.s k).val) := by
  have h' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M₀ (fun i => spMap ρ ≫ ψ i) k :=
    fun z _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 (h (show spMap ρ z ∈ (⊤ : (Sp A₀).Opens) from trivial)) i
  refine (HolHom.valR_res (𝟙 (Sp A)) _ _ h').trans ((HolHom.valR_comp (𝟙 (Sp A)) (spMap ρ) _ _).symm.trans ?_)
  refine Eq.trans ?_ (HolHom.valR_spMap ρ (𝟙 (Sp A₀)) _ h _)
  rw [Category.id_comp, Category.comp_id]
  rfl

theorem prod_factors {G : Type} [CommGroup G] (u : Fin 4 → G) (j : ℕ) :
    (∏ i, u i ^ Out.DegPre.famε j i) * ∏ i, ![u 1, u 2, u 0, u 3] i ^ Out.DegPre.gtε i = u 0 ^ j := by
  simp only [Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub, zpow_neg, zpow_one,
    zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end Values

section Points

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (α : D.X)

theorem comp_famφB (i : Fin 4) : b.left ≫ D.famφB α i = D.gtφT T b α (![2, 0, 1, 3] i) := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases i
  · exact Category.comp_id _
  · change (b ≫ (𝟙 D.P.A * toUnit _ ≫ D.c α)).left = ((toUnit _ ≫ D.c α) * b).left
    rw [MonObj.comp_mul, h, Category.comp_id, mul_comm]
  · exact congrArg (·.left) (h _)
  · exact congrArg (·.left) (h _)

end Points

section Core

open FrameValue

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {D₀ : Out.DegPre ℂ} {n : ℕ}
  (u : HolUnif D₀.P.A D₀.P.L n) {α₀ : D₀.X} {c : Fin n → ℂ}

theorem toUnit_comp_left {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ p).left) = p.left := by
  have e : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  change (Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ) ≫ p.left = _
  rw [e]
  exact Category.id_comp _

theorem gtφ_eq (hc : u.ex c = D₀.c α₀) {b₀ : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A} {z : Fin n → ℂ}
    (hb : (show Sp ℂ ⟶ _ from b₀.left) = (u.ex z).left) (k : Fin 4) :
    (show Sp ℂ ⟶ _ from Out.DegPre.gtφ D₀ ℂ b₀ α₀ k) = (u.ex (![c + z, c, z, 0] k)).left := by
  have hb' : b₀ = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hb.trans (toUnit_comp_left _).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]
  fin_cases k
  · refine Eq.trans ?_ (toUnit_comp_left _)
    change (toUnit _ ≫ D₀.c α₀ * b₀).left = (toUnit _ ≫ u.ex (c + z)).left
    rw [hb', u.ex_add, MonObj.comp_mul, hc]
  · exact (toUnit_comp_left _).trans (congrArg (·.left) hc.symm)
  · exact hb
  · exact (toUnit_comp_left _).trans (congrArg (·.left) h0.symm)


omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem isLift_famφB (hc : u.ex c = D₀.c α₀) (z : Fin n → ℂ) :
    IsLift u (D₀.famφB α₀) (u.ex z).left ![z, z + c, c, 0] := fun k => by
  have h : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A, u.ex z ≫ toUnit D₀.P.A ≫ p = p := fun p => by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  fin_cases k
  · exact Category.comp_id _
  · change (u.ex z ≫ (𝟙 D₀.P.A * toUnit _ ≫ D₀.c α₀)).left = (u.ex (z + c)).left
    rw [MonObj.comp_mul, h, Category.comp_id, u.ex_add, hc]
  · change (u.ex z ≫ toUnit _ ≫ D₀.c α₀).left = (u.ex c).left
    rw [h, hc]
  · change (u.ex z ≫ toUnit _ ≫ η[D₀.P.A]).left = (u.ex 0).left
    rw [h, (u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    [IsLocalRing S] (κ : R →+* S) (ρ : ℂ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ))) (g₀ : Out.GtPtF D₀ ℂ)
    {α : D.toPre.X} {z : Fin n → ℂ} (hc : u.ex c = D₀.c α₀) (hb : (show Sp ℂ ⟶ _ from g₀.b.left) = (u.ex z).left)
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (j₀ : D₀.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (hj : FormalValue.CohCharts g α jM jf jt)
    (hM : ⊤ ≤ (show Sp S ⟶ _ from g.b.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀, jM)) :
    valR (A := S) g.b.left _ (w.s (fun _ => j₀, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (secVal u D₀.P.isLB s₀ (u.ex z).left ![z, z + c, c, 0] *
        genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] * u.fr j₀ z ^ j) := by
  have hφ : ∀ k, FormalValue.coordφ g α k ≫ φ = spMap ρ ≫ (u.ex (![c + z, c, z, 0] k)).left := fun k =>
    (hg.1 k).trans (congrArg (spMap ρ ≫ ·) (gtφ_eq u hc hb k))
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have h₀ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.U j₀ := by
    intro y _
    obtain rfl : y = spMap ρ (cpt S) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact (congrArg (fun q => q (cpt S) ∈ D₀.P.L.U j₀) (hφ 2)).mp (mem_pull.1 (hM trivial).1)
  obtain ⟨k, hk, ek⟩ : ∃ k : Fin 4 → D₀.P.L.ι,
      (∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ D₀.P.L.U (k i)) ∧ k 2 = j₀ := by
    refine ⟨![chartAt D₀.P.isLB (u.ex (c + z)).left, chartAt D₀.P.isLB (u.ex c).left, j₀,
      chartAt D₀.P.isLB (u.ex 0).left], fun i => ?_, rfl⟩
    fin_cases i
    exacts [le_chartAt D₀.P.isLB _, le_chartAt D₀.P.isLB _, h₀, le_chartAt D₀.P.isLB _]
  subst ek ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have lf := isLift_famφB u hc z
  have lg : IsLift u (Out.DegPre.gtφ D₀ ℂ g₀.b α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] :=
    fun i => (Category.id_comp _).trans (gtφ_eq u hc hb i)
  have cf : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) := by
    refine (lf.le_iff _).2 fun i => ?_
    fin_cases i
    exacts [hk 2, add_comm c z ▸ hk 0, hk 1, hk 3]
  have cg := (lg.le_iff k).2 hk
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      ((HolHom.valR_spMap ρ (u.ex z).left _ cf _).trans (congrArg ρ (valAt'_sec D₀.P.isLB s₀ lf cf)))
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    ((valR_pullGen ρ (g₀.s α₀) k cg).trans (congrArg ρ (valAt'_gen D₀.P.isLB (g₀.isGen α₀) lg cg))))
  have e₄ : FrameValue.frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] (fun i => k (![2, 0, 1, 3] i)) *
      FrameValue.frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
    have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
    have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
    have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
    have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
    simp only [FrameValue.frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
      zpow_neg, zpow_one, zpow_natCast, add_comm z c]
    field_simp
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₄]
  simp only [map_mul] at e₁ ⊢
  rw [← e₅] at e₁
  unfold FormalValue.famVal
  linear_combination (ρ (genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0]) *
    ρ (FrameValue.frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k)) * e₁

end Core

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧), (∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z) (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ → (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) → ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) = valR (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧ (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) * valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e (Λ.ε α))) jf) (f.f jf) = κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) j₀) (s₀.f j₀)) → ∀ v jM j₀ jf jt, FormalValue.CohCharts (Ξ.g v) (W.e (Λ.ε α)) jM jf jt → ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) → valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j * (FormalValue.famVal (Ξ.g v) f jf * FormalValue.coordVal (Ξ.g v) (W.e (Λ.ε α)) jt) = r * PowerSeries.C (Λ.fn j α s₀ v.2 * eTwoPi (v.1 α) * Λ.u.fr j₀ v.2 ^ j) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j α s₀ f r hf v jM j₀ jf jt hj hM
  have h := core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v) (Λ.ct α) (Λ.ex0_b v)
    (Ξ.g_rel v (Λ.ε α)) s₀ f r (fun p => hf _ p _) jM j₀ jf jt hj hM
  rw [Λ.arcDict_expZero_section v α] at h
  exact h

end GlobalTheory.ConstTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibres
noncomputable section

namespace GlobalTheory.RigIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem gm_eq_of_eq_along_section {Y Z T : Scheme.{0}} {N : LB Y} (hN : ∀ y : Y, ∃ i, y ∈ N.U i)
    (q : Z ⟶ Y) (p : Z ⟶ T) (e : T ⟶ Z) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    {t₁ t₂ : LB.Gen N} (h₁ : t₁.IsGen) (h₂ : t₂.IsGen)
    (h : ∀ (s : T) (i : N.ι), (e ≫ q) s ∈ N.U i → gm (e ≫ q) s (N.U i) (t₁.s i) = gm (e ≫ q) s (N.U i) (t₂.s i))
    {W : Scheme.{0}} (r : W ⟶ Z) (z : W) (i : N.ι) (hi : (r ≫ q) z ∈ N.U i) :
    gm (r ≫ q) z (N.U i) (t₁.s i) = gm (r ≫ q) z (N.U i) (t₂.s i) := by
  have tr : ∀ {t : LB.Gen N}, t.IsGen → ∀ (i j : N.ι) (x : Y), x ∈ N.U i ⊓ N.U j →
      gm (𝟙 Y) x (N.U i) (t.s i) = gm (𝟙 Y) x (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) x (N.U j) (t.s j) := by
    intro t ht i j x hx
    have := congrArg (gm (𝟙 Y) x (N.U i ⊓ N.U j)) (ht i j)
    rwa [map_mul, gm_res _ x _ hx, gm_res _ x _ hx] at this
  obtain ⟨u, hu⟩ := glue_unit ⊤ N.U (fun _ => le_top) (fun y _ => Opens.mem_iSup.2 (hN y))
    (fun i => t₁.s i * (t₂.s i)⁻¹) (fun i j x hx => by
      rw [map_mul, map_mul, map_inv, map_inv, tr h₁ i j x hx, tr h₂ i j x hx, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  obtain ⟨a, ha⟩ := hp (q.appTop.hom u.val)
  have key : ∀ (W : Scheme.{0}) (r : W ⟶ Z) (z : W) (i : N.ι), (r ≫ q) z ∈ N.U i →
      (gm (r ≫ q) z (N.U i) (t₁.s i) * (gm (r ≫ q) z (N.U i) (t₂.s i))⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro W r z i hi
    rw [← map_inv, ← map_mul, ← hu i, gm_res (r ≫ q) z _ hi]
    exact (gs_unit (r ≫ q) z ⊤ trivial _).symm.trans ((gs_pull r q z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    obtain ⟨i, hi⟩ := hN ((e ≫ q) y)
    have := key _ e y i hi
    rw [h y i hi, mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key _ r z i hi
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

theorem valR_eq_of_gs {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) (h : ∀ z, gs x z U a = gs x z U b) : valR x U a = valR x U b := by
  rw [valR, valR, dite_eq_left hU, dite_eq_left hU]
  congr 1
  have : (x.app U).hom a = (x.app U).hom b := fn_ext fun z hz => by
    rw [gs_pull (𝟙 _) x z U hz, gs_pull (𝟙 _) x z U hz, Category.id_comp]
    exact h z
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, this]

theorem isAbelianScheme_fibre {S T : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (y : T ⟶ S)
    (hp : IsProper (pullback.snd G.hom y)) : IsAbelianScheme ((Over.pullback y).obj G) := by
  haveI := hG.comm
  haveI := hG.smooth
  haveI := hG.geomConnected
  exact ⟨inferInstance, (inferInstance : Smooth (pullback.snd G.hom y)), hp,
    (inferInstance : GeometricallyConnected (pullback.snd G.hom y))⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), (∃ w, IsRigIso m.cm t'.PP t.PP w) ∧ ∀ (w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)), IsRigIso m.cm t'.PP t.PP w → IsRigIso m.cm t'.PP t.PP w' → ∀ (F : Type) [Field F] (y : Sp F ⟶ S') (x : Over.mk y ⟶ t'.G), IsProper (pullback.snd t'.G.hom y) → ∀ j j', ⊤ ≤ x.left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') → valR x.left _ (w.s (fun _ => j, j')).val = valR x.left _ (w'.s (fun _ => j, j')).val := by
  intro hL _ E _ _ _ H _ S S' t t' f m
  refine ⟨m.lin.imp fun w hw => ⟨hw.1, hw.2.1⟩, ?_⟩
  intro w w' hw hw' F _ y x hp j j' hU
  have hs : Function.Surjective (pullback.snd t'.G.hom y).appTop.hom :=
    (hL.globalFns _ _ (isAbelianScheme_fibre t'.G t'.semi y hp)).2
  have he : eSec t'.G ≫ t'.G.hom = 𝟙 S' := Over.w η[t'.G]
  have hx : x.left ≫ t'.G.hom = 𝟙 _ ≫ y := (Over.w x).trans (Category.id_comp y).symm
  have he' : (y ≫ eSec t'.G) ≫ t'.G.hom = 𝟙 _ ≫ y := by
    rw [Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) he).trans (Category.comp_id y))
  refine valR_eq_of_gs _ _ hU _ _ fun z => ?_
  have hz : x.left z ∈ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') :=
    hU (show z ∈ (⊤ : (Sp F).Opens) from trivial)
  rw [gs_unit _ _ _ hz, gs_unit _ _ _ hz]
  congr 1
  have hcov : ∀ a : t'.G.left, ∃ i, a ∈ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart t'.PP.isLB a
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (m.φ a)
    exact ⟨(fun _ => k, i), mem_pull.2 hk, hi⟩
  have gm_pullU_eq_gm_comp {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (r : Z ⟶ Y) (z : Z) {U : X.Opens}
      (h : φ (r z) ∈ U) (x : Γ(X, U)ˣ) :
      gm r z (φ ⁻¹ᵁ U) (pullU φ U x) = gm (r ≫ φ) z U x := by
    have h₁ : r z ∈ φ ⁻¹ᵁ U := h
    have h₂ : (r ≫ φ) z ∈ U := h
    simp only [gm, dif_pos h₁, dif_pos h₂, MonoidHom.comp_apply]
    ext
    simp only [Units.coe_map, pullU, MonoidHom.coe_coe]
    first
      | rfl
      | (rw [Scheme.comp_app]; rfl)

  have gm_maps_pt {X : Scheme.{0}} {L' L : LB X} {w : LB.Iso L' L} {Y : Scheme.{0}} {φ : Y ⟶ X} {a : LB.Gen (L'.pull φ)}
      {b : LB.Gen (L.pull φ)} (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => φ) (fun _ => 1)) a b)
      {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (p : L.ι) (q : L'.ι) (hp : φ (r z) ∈ L.U p) (hq : φ (r z) ∈ L'.U q) :
      gm r z _ (b.s (fun _ => p)) = gm (r ≫ φ) z _ (w.s (p, q)) * gm r z _ (a.s (fun _ => q)) := by
    have hV : r z ∈ LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q) :=
      ⟨mem_pull.2 hp, mem_pull.2 hq⟩
    have h' : res (U := LB.wchart L (fun _ => φ) (fun _ => p))
          (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_left
          (b.s (fun _ => p)) =
        (∏ _k : PUnit, (res (U := φ ⁻¹ᵁ (L.U p ⊓ L'.U q))
            (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))
            (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ => φ) (fun _ => p) PUnit.unit))
              (inf_le_right.trans (LB.wchart_le L' (fun _ => φ) (fun _ => q) PUnit.unit)))
            (pullU φ (L.U p ⊓ L'.U q) (w.s (p, q)))) ^ (1 : ℤ)) *
        res (U := LB.wchart L' (fun _ => φ) (fun _ => q))
          (V := LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q)) inf_le_right
          (a.s (fun _ => q)) :=
      h (fun _ => p, fun _ => q)
    rw [Fintype.prod_unique, zpow_one] at h'
    have key := congrArg (gm r z (LB.wchart L (fun _ => φ) (fun _ => p) ⊓ LB.wchart L' (fun _ => φ) (fun _ => q))) h'
    rw [map_mul, gm_res r z (U := LB.wchart L (fun _ => φ) (fun _ => p)) _ hV (b.s (fun _ => p))] at key
    refine key.trans (congrArg₂ (· * ·) ((gm_res r z _ hV _).trans
      (gm_pullU_eq_gm_comp φ r z (U := L.U p ⊓ L'.U q) ⟨hp, hq⟩ (w.s (p, q)))) (gm_res r z _ hV _))
  have key := gm_eq_of_eq_along_section hcov (pullback.fst t'.G.hom y) (pullback.snd t'.G.hom y)
    (pullback.lift (y ≫ eSec t'.G) (𝟙 _) he') (pullback.lift_snd _ _ _) hs hw.1 hw'.1 (by
      rw [pullback.lift_fst]
      rintro s ⟨k, i⟩ ⟨hk, hi⟩
      have k₁ := gm_maps_pt hw.2 y s k i hk hi
      have k₂ := gm_maps_pt hw'.2 y s k i hk hi
      exact mul_right_cancel (k₁.symm.trans k₂))
    (pullback.lift x.left (𝟙 _) hx) z (fun _ => j, j')
  rw [pullback.lift_fst] at key
  exact key hz

end GlobalTheory.RigIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f), (∃ w, IsRigIso m.cm t'.PP t.PP w) ∧ ∀ (w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)), IsRigIso m.cm t'.PP t.PP w → IsRigIso m.cm t'.PP t.PP w' → ∀ (F : Type) [Field F] (y : Sp F ⟶ S') (x : Over.mk y ⟶ t'.G), IsProper (pullback.snd t'.G.hom y) → ∀ j j', ⊤ ≤ x.left ⁻¹ᵁ (LB.div (t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') → valR x.left _ (w.s (fun _ => j, j')).val = valR x.left _ (w'.s (fun _ => j, j')).val := by
  first | exact @GlobalTheory.RigIso.main | exact GlobalTheory.RigIso.main | (intros; apply GlobalTheory.RigIso.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkings
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkings
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem exp_eq_of_matching_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P P' : (Fu.Di i).La →+ (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (inferInstance : StarRing (𝓞 E)) = H.starRing → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i) ty P' → (∀ u v, (Fu.Di i).EF (gam u) (gam v) = (Fu.Di i).EF u v) → (∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = Fu.t i v + l.M • e) → (∀ v, ∃ e, gam (Fu.t i v) = Fu.t i v + l.A • e) → (∀ u, P' (gam u) = h (P u)) → Fu.u i P = Fu.u i P' ∧ ∀ z, (Fu.ex i P' (h z)).left = (Fu.ex i P z).left := by
  intro E _ _ _ H _ D l Xo σ g ty Fu i P P' gam h _ hP hP' hiso hM hA hh
  have hM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Fu.Di i).La),
      ∃ e, gam a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := Fu.t_surj i b
      obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have hA' : ∀ a, ∃ e, gam a = a + l.A • e := by
    intro b
    obtain ⟨c, e, rfl⟩ := Fu.t_surj i b
    obtain ⟨e₁, he₁⟩ := hA c
    obtain ⟨r, hr⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
    refine ⟨e₁ + r • (gam e - e), ?_⟩
    rw [map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul, smul_sub]
    abel
  have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
    LinearMap.toMatrix'_mulVec _ z
  obtain ⟨-, h1, h2⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H D l Xo σ g ty Fu i P P' gam
    (LinearMap.toMatrix' h.toLinearMap) hP hP' hiso hM' hA' (fun a => by rw [hm, hh])
  exact ⟨h1, fun z => by rw [← hm]; exact h2 z⟩

end GlobalTheory.ArcPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpEqOfIsometryMatchingMarkingsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_eq_of_isometry_matching_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P P' : (Fu.Di i).La →+ (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (inferInstance : StarRing (𝓞 E)) = H.starRing → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i) ty P' → (∀ u v, (Fu.Di i).EF (gam u) (gam v) = (Fu.Di i).EF u v) → (∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = Fu.t i v + l.M • e) → (∀ v, ∃ e, gam (Fu.t i v) = Fu.t i v + l.A • e) → (∀ u, P' (gam u) = h (P u)) → Fu.u i P = Fu.u i P' ∧ ∀ z, (Fu.ex i P' (h z)).left = (Fu.ex i P z).left := by
  first | exact @GlobalTheory.ArcPts.exp_eq_of_matching_markings | exact GlobalTheory.ArcPts.exp_eq_of_matching_markings | (intros; apply GlobalTheory.ArcPts.exp_eq_of_matching_markings <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShift
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.GtRep

open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem exists_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  intro h1 h2 E _ _ _ H _ D l c O _ β _ _ b a Λ k hk
  obtain ⟨hadd, hsurj, -⟩ := GlobalTheory.T.analyticDictionaryExp_additive_surjective_linear h1 h2 E H D l c O β b a Λ
  obtain ⟨hker, hio, -⟩ := GlobalTheory.T.analyticDictionaryExp_kernel_iota_torusPoints E H D l c O β b a Λ
  have hB := a.bimult
  let ex : Λ.A.V →+ Out.GtPtF a.D₀ ℂ :=
    AddMonoidHom.mk' Λ.ex0 fun z z' => (isAdd_iff_eq _ _ _).1 (hadd z z')
  have hex : ∀ z, Λ.ex0 z = ex z := fun _ => rfl
  have hio' : ∀ la : Λ.A.La, ex (Λ.A.P0 la) = iota hB ℂ (Λ.ε la.y) := fun la => (isIota_iff_eq hB _ _).1 (hio la)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hf : (algebraMap (FractionRing ℂ) ℂ).comp (algebraMap (FractionRing ℂ) (FractionRing ℂ)) =
      algebraMap (FractionRing ℂ) ℂ := RingHom.ext fun _ => rfl
  have hkk : ∀ v : Λ.A.V, (k : ℂ)⁻¹ • k • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hkk' : ∀ v : Λ.A.V, k • (k : ℂ)⁻¹ • v = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  refine ⟨fun p => ?_, fun p la e hrep => ?_⟩
  · obtain ⟨q, -, huniq⟩ := existsUnique_qkExt hB _ hf p
    obtain ⟨z, hz⟩ := hsurj q.g
    let l0 : Λ.A.La := AnArc.La.mk (Λ.ε.symm q.y) 0 0
    have hl0 : Λ.ε l0.y = q.y := Λ.ε.apply_symm_apply _
    have hzero : (Λ.ex0 (k • z - Λ.A.P0 l0)).IsZero := by
      rw [isZero_iff_eq, hex, map_sub, map_nsmul, ← hex z, hz, qk_nsmul hB, hio', hl0, sub_self]
    obtain ⟨l1, hl1, hl1'⟩ := (hker _).1 hzero
    refine ⟨l1 + l0, fun q' hq' => ?_⟩
    obtain rfl := huniq q' hq'
    refine ⟨by rw [AnArc.La.add_y, hl1, zero_add, hl0], ?_⟩
    rw [map_add (f := _), ← hl1', sub_add_cancel, hkk, hz]
  · refine ⟨qkMk hB (Λ.ε (la + k • e).y) (Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)))
      (by rw [hex, ← map_nsmul, hkk', hio']), rfl, rfl, fun q' hq' => ?_⟩
    obtain ⟨hy, hg⟩ := hrep q' hq'
    refine equiv_symm hB ((equiv_iff hB _ _).2 ⟨Λ.ε e.y, ?_, ?_⟩)
    · rw [qkMk_y, hy, AnArc.La.add_y, AnArc.La.nsmul_y, map_add (f := _), map_nsmul]
    · rw [qkMk_g, hg, hex, hex, map_add (f := _), map_nsmul, smul_add, hkk, map_add (f := _), hio']

end GlobalTheory.GtRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLatticeVectorRepAndShiftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeVector_rep_and_shift : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ), 1 ≤ k → (∀ p, ∃ la, Λ.Rep k p la) ∧ ∀ p la e, Λ.Rep k p la → ∃ q : Out.QkPt a.D₀ ℂ k, q.y = Λ.ε (la + k • e).y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 (la + k • e)) ∧ ∀ q', QkExt (algebraMap _ ℂ) p q' → Out.QkPt.Equiv a.D₀ ℂ q q' := by
  first | exact @GlobalTheory.GtRep.exists_rep_and_shift | exact GlobalTheory.GtRep.exists_rep_and_shift | (intros; apply GlobalTheory.GtRep.exists_rep_and_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqSpMapOfInjective
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPoint

theorem eq_spMap_of_injective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) (x : Sp A ⟶ Sp K) (ρ : K →+* A) (h : spMap i ≫ x = spMap (i.comp ρ)) :
    x = spMap ρ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  have h' : Spec.map (φ ≫ CommRingCat.ofHom i) = Spec.map (CommRingCat.ofHom (i.comp ρ)) := by
    rw [Spec.map_comp]; exact h
  have h2 := Spec.map_injective h'
  congr 1
  ext k
  exact hi (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h2) k)

theorem sumsAt_of_halfRing {K F : Type} [CommRing K] [CommRing F] {X Y : Scheme.{0}} (s : X ⟶ Sp K) (κ : K →+* F)
    (bF : F →+* ℂ) (j : pullback s (spMap κ) ⟶ Y) (χ : Sp ℂ⟦X⟧ ⟶ Y) (y : Sp ℂ⸨X⸩ ⟶ pullback s (spMap κ))
    (hj : y ≫ j = spMap (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) ≫ χ)
    (hs : y ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF))
    {T : ℝ} (yT : Sp (Conv.halfRing T) ⟶ X)
    (hT : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y ≫ pullback.fst _ _)
    (U : Y.Opens) (f : Γ(Y, U)) (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ (w : ℂ) (hw : T < w.im), T' < w.im → ∀ z : Sp ℂ ⟶ pullback s (spMap κ),
      z ≫ pullback.fst _ _ = spMap (Conv.ev T w hw).toRingHom ≫ yT → z ≫ pullback.snd _ _ = spMap bF →
      ⊤ ≤ (z ≫ j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (z ≫ j) U f) := by
  have hval : (Conv.halfRing T).val.toRingHom.comp ((algebraMap ℂ (Conv.halfRing T)).comp bF) =
      (algebraMap ℂ ℂ⸨X⸩).comp bF := RingHom.ext fun _ => rfl
  have hover : yT ≫ s = spMap ((algebraMap ℂ (Conv.halfRing T)).comp bF) ≫ spMap κ := by
    rw [← spMap_comp]
    refine eq_spMap_of_injective (Conv.halfRing T).val.toRingHom Subtype.val_injective _ _ ?_
    rw [← Category.assoc, hT, Category.assoc, pullback.condition, ← Category.assoc, hs, ← spMap_comp,
      ← RingHom.comp_assoc, hval]
  let yF : Sp (Conv.halfRing T) ⟶ pullback s (spMap κ) := pullback.lift yT _ hover
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yF = y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hT]
    · rw [Category.assoc, pullback.lift_snd, hs, ← spMap_comp, hval]
  obtain ⟨T', hle, hw'⟩ := Conv.exists_sumsAt_halfCurve (yT := yF ≫ j) (χ := χ) rfl (RingHom.id _) (by
    rw [RingHom.id_comp, RingHom.id_comp, ← hj, ← hgen, Category.assoc, ← Category.assoc (spMap _) (spMap _),
      ← spMap_comp]
    rfl) hU
  refine ⟨T', hle, fun w hw hw2 z hz1 hz2 => ?_⟩
  have hz : z = spMap (Conv.ev T w hw).toRingHom ≫ yF := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hz1]
    · rw [Category.assoc, pullback.lift_snd, hz2, ← spMap_comp]
      congr 2
      ext x
      exact ((Conv.ev T w hw).commutes (bF x)).symm
  have hzj : z ≫ j = Conv.halfCurve (yF ≫ j) w := by
    rw [hz, Conv.halfCurve_eq _ hw, Category.assoc]
    rfl
  rw [hzj]
  exact ⟨(hw' w hw2).1, (hw' w hw2).2 f⟩

theorem point_sumsAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), ∀ (U : Y.X.Opens) (f : Γ(Y.X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u K.i (K.Pw w) → yF ≫ pullback.snd _ _ = spMap bF → ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (yF ≫ Y.j) U f) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K U f hU
  obtain ⟨T', hle, h⟩ := sumsAt_of_halfRing Xo.s _ bF Y.j χ C.yF C.yF_j C.yF_over Ψ.yT Ψ.yT_gen U f hU
  refine ⟨max T' K.T, fun w hw z hz1 hz2 => ?_⟩
  have h1 : T' < w.im := (le_max_left _ _).trans_lt hw
  have h2 : Ψ.T < w.im := hle.trans_lt h1
  exact h w h2 h1 z (hz1.trans ((K.u_eq w ((le_max_right _ _).trans_lt hw)).trans (Ψ.yw_eq w h2))) hz2

end GlobalTheory.ArcPoint
end
end
