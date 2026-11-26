module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.FibreCmp

theorem isDerivAt0_comp_linear {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem valAt'_comp_app {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [Scheme.Hom.app_eq_appLE]
    exact valAt'_appLE _ _ _ _ _ _ h
  · have h' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := h
    unfold valAt'
    rw [dite_eq_right h, dite_eq_right h']

theorem isDerivAt0_of_isDiff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {Y : Scheme.{0}}
    (φ : A.left ⟶ Y) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    (he : ∀ z, (u.ex z).left ≫ φ = e z) (hv : IsTangent v) (hd : u.IsDiff w v) :
    IsDerivAt0 e w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := by
  obtain rfl : (fun z => (show Sp ℂ ⟶ _ from (u.ex z).left) ≫ φ) = e := funext he
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [← Category.assoc]
    refine congrArg (· ≫ φ) (hv.trans ?_)
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp
  · have := hd (φ ⁻¹ᵁ U) hU ((φ.app U).hom f)
    simp only [valAt'_comp_app] at this
    rw [← this, Scheme.Hom.comp_appLE]
    rfl


open FibreUnif in
theorem exists_equiv_of_polAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty)
    (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (FU.Di i) ty Pe) (P : Out.PolAV (Sp ℂ))
    (φ : P.A.left ⟶ Xo.univ.t.G.left) (hp : IsGrpPullback P.A Xo.univ.t.G (FU.u i Pe) φ)
    (hL : LBIso P.L (Xo.univ.t.PP.L.pull φ)) {g : ℕ} (u : HolUnif P.A P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hAH : u.IsAH Hm κ) :
    ∃ F : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left) ∧
      (∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) ∧
      (∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = (FU.Di i).EF a b) ∧
      ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → (u.IsDiff (F w) v ↔
        IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)) := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨Ef, hEf, -, -, ht₁, ht₂, hweil⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all P g u Hm κ hAH
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = y.left ≫ φ → x = y := fun x y h =>
    Over.OverMorphism.ext (hp.1.hom_ext h (by rw [Over.w x, Over.w y]))
  have lift : ∀ x₀ : Over.mk (FU.u i Pe) ⟶ Xo.univ.t.G, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x.left ≫ φ = x₀.left := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left (𝟙 _) ((Over.w x₀).trans (Category.id_comp _).symm)) (hp.1.lift_snd _ _ _),
      hp.1.lift_fst _ _ _⟩
  choose Φ hΦ using lift
  have Φmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => inj _ _ (by
    rw [hΦ, ← hp.2 _ (Φ x) (Φ y) (pushPt hp.1.w (Φ x)) (pushPt hp.1.w (Φ y)) rfl rfl]
    exact mul_left_congr (Category.id_comp _).symm _ _ _ _ (hΦ x).symm (hΦ y).symm)
  have Φinj : Function.Injective Φ := fun x y h => Over.OverMorphism.ext (by rw [← hΦ, ← hΦ, h])
  have Φsurj : Function.Surjective Φ := fun x =>
    ⟨Over.homMk (x.left ≫ φ) ((Over.w (pushPt hp.1.w x)).trans (Category.id_comp _)), inj _ _ (hΦ _)⟩
  have Φone : Φ 1 = 1 := by
    have := Φmul 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have holG : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (FU.ex i Pe z).left) := by
    have h := (FU.hol i 0 Set.univ (fun _ => Pe) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
    exact isHolTo_slice h 0
  have hol : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (Φ (FU.ex i Pe z)).left) :=
    isHolTo_of_isPullback hp.1 (e := fun z => (Φ (FU.ex i Pe z)).left) (fun z => Over.w (Φ (FU.ex i Pe z)))
      (by simpa only [hΦ] using holG)
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo P.A P.isAb P.L g g₀ u ht₁ ht₂ (fun z => Φ (FU.ex i Pe z))
    (fun z z' => by rw [FU.ex_add i Pe hP, Φmul]) hol
  have hΛ : ∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range := fun z => by
    rw [← u.ker, hF, ← FU.ex_ker i Pe hP, ← Φone, Φinj.eq_iff]
  have cΛ : (u.Λ : Set (Fin g → ℂ)).Countable := by
    have := u.discrete
    exact (countable_of_Lindelof_of_discrete : Countable u.Λ)
  have cP : (Pe.range : Set (Fin g₀ → ℂ)).Countable := by
    have := hP.2.2.1
    exact (countable_of_Lindelof_of_discrete : Countable Pe.range)
  have Finj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun z hz =>
    eq_zero_of_smul_mem_countable cP fun t => (hΛ _).1 (by rw [map_smul, hz, smul_zero]; exact u.Λ.zero_mem)
  have Fsurj : Function.Surjective F := surjective_of_countable F cΛ fun v => by
    obtain ⟨x₀, hx₀⟩ := Φsurj (u.ex v)
    obtain ⟨z, rfl⟩ := FU.ex_onto i Pe hP x₀
    refine ⟨z, (u.ker _).1 ?_⟩
    have := u.ex_add (v - F z) (F z)
    rw [sub_add_cancel, hF, hx₀] at this
    exact right_eq_mul.1 this
  have hex : ∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left := fun z => by rw [hF, hΦ]
  let F' := LinearEquiv.ofBijective F ⟨Finj, Fsurj⟩
  have fwd : ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ P.A), IsTangent v → u.IsDiff (F' w) v →
      IsDerivAt0 (fun z => (FU.ex i Pe z).left) w ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ) := fun w v hv hd => by
    have h1 := isDerivAt0_of_isDiff u φ (e := fun z => (FU.ex i Pe (F'.symm.toLinearMap z)).left)
      (fun z => by rw [← hex]; exact congrArg (fun t => (u.ex t).left ≫ φ) (F'.apply_symm_apply z).symm) hv hd
    have h2 := (isDerivAt0_comp_linear _ holG F'.symm.toLinearMap _ _).1 h1
    rwa [LinearEquiv.coe_coe, F'.symm_apply_apply] at h2
  refine ⟨F', hex, hΛ, fun a b => ?_, fun w v hv => ⟨fwd w v hv, fun hd => ?_⟩⟩
  · let a' : u.Λ := ⟨F (Pe a), (hΛ _).2 ⟨a, rfl⟩⟩
    let b' : u.Λ := ⟨F (Pe b), (hΛ _).2 ⟨b, rfl⟩⟩
    refine (hEf a' b').symm.trans (congrArg _ (int_eq_of_exp_eq fun k hk => ?_))
    have h₁ := hweil k a' b' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have h₂ := FU.ex_weil i Pe hP k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
    have h₃ := weil_eq_of_grpPullback hp Xo.univ.t.PP.isLB P.isLB w hw (Z := Sp ℂ) (t := FU.u i Pe) (t' := 𝟙 _)
      (Category.id_comp _).symm k (u.ex ((k : ℂ)⁻¹ • F (Pe a))) (u.ex ((k : ℂ)⁻¹ • F (Pe b))) _ _
      (by rw [← hex, map_smul]) (by rw [← hex, map_smul]) _ _ h₁ h₂
    exact congrArg Units.val (unitOn_injective h₃)
  · obtain ⟨w', hw', -⟩ := ht₁ v hv
    obtain ⟨w₁, rfl⟩ := F'.surjective w'
    have h1 := fwd w₁ v hv hw'
    let a : epsPt (FU.u i Pe) ⟶ Xo.univ.t.G := Over.homMk ((show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ φ)
      (by rw [Category.assoc, hp.1.w, ← Category.assoc]; exact congrArg (· ≫ FU.u i Pe) (Over.w v))
    have e : w = w₁ := ((FU.ex_diff i Pe hP).2 a hd.1).unique hd h1
    rwa [e]

theorem exists_equiv_of_isAH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ' : KA l →+* ℂ) (g₀ : ℕ) (ty : Fin g₀ → (E →+* ℂ)) (Fu : FamilyUnif Xo σ' ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g₀ → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (s' : Sp ℂ ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s') (m : ObjMap o Xo.univ y₀) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ), IsPeriod (Fu.Di i) ty P → y₀ = Fu.u i P → u.IsAH Hm κ → ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) ∧ (∀ z, h z ∈ u.Λ ↔ z ∈ P.range) ∧ (∀ a b, (herm Hm (h (P a)) (h (P b))).im = (Fu.Di i).EF a b) ∧ ∀ (w : Fin g₀ → ℂ) (v : epsR ℂ ⟶ o.t.G), IsTangent v → (u.IsDiff (h w) v ↔ IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v.left ≫ m.toSABMap.φ)) := by
  intro E _ _ _ H D l Xo σ' g₀ ty Fu i P y₀ s' o m g u Hm κ hP hy hAH
  subst hy
  obtain ⟨w, hw, -⟩ := m.lin
  exact exists_equiv_of_polAV Fu i hP (GlobalTheory.Obj.toPolAV o) m.toSABMap.φ m.cart ⟨w, hw⟩ u hAH

end GlobalTheory.DetLine.FibreCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasDim

theorem two_mul_card_pairs_le (p : ℕ) :
    2 * ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card ≤ p ^ 2 := by
  have e : ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card = ∑ i ∈ Finset.range p, i := by
    rw [← Finset.sum_range_reflect]
    rw [Fin.sum_univ_eq_sum_range (fun i => p - 1 - i) p |>.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [e, mul_comm, Finset.sum_range_id_mul_two]
  rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem abs_factor_le (d : ℤ) (i j : ℕ) (hij : i < j) :
    |((((d : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) : ℚ) : ℝ)| ≤ 1 + |(d : ℝ)| := by
  have hs : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hs0 : (0 : ℝ) < (j : ℝ) - (i : ℝ) := by linarith
  push_cast
  rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
  have h1 : |(d : ℝ) + (j : ℝ) - (i : ℝ)| ≤ |(d : ℝ)| + ((j : ℝ) - (i : ℝ)) := by
    have := abs_add_le (d : ℝ) ((j : ℝ) - (i : ℝ))
    rw [abs_of_pos hs0] at this
    rw [show (d : ℝ) + (j : ℝ) - (i : ℝ) = (d : ℝ) + ((j : ℝ) - (i : ℝ)) by ring]
    exact this
  nlinarith [abs_nonneg (d : ℝ)]

theorem abs_weylDimU_le {p : ℕ} (lam : Fin p → ℤ) (B : ℝ) (hB : ∀ a b, |((lam a - lam b : ℤ) : ℝ)| ≤ B) :
    |((Formalism.IndefR.Mult.weylDimU lam : ℚ) : ℝ)| ≤
      (1 + B) ^ (∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card) := by
  unfold Formalism.IndefR.Mult.weylDimU
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j hj => ?_
  have hij : (i : ℕ) < (j : ℕ) := (Finset.mem_filter.1 hj).2
  have := abs_factor_le (lam i - lam j) i j hij
  exact this.trans (by linarith [hB i j])

end GlobalTheory.OneMeasDim

namespace GlobalTheory.OneMeasDim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem abs_wt_sub_le (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (a b : Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) :
    |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
  have hw : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hab : a = b
  · subst hab; simpa using hw
  set c : ℝ := (((D.hc τ).e i : ℚ) : ℝ)
  set g : (Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) → ℝ :=
    fun x => |((Formalism.L2.NTheta.wtOf D (Wc D i) τ x : ℤ) : ℝ) + c| with hg
  have h1 : |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ g a + g b := by
    rw [hg]; push_cast
    have := abs_sub (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c)
    rw [show (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) - (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c) =
      ((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) - ((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) by ring] at this
    exact this
  have h2 : g a + g b ≤ ∑ x, g x := by
    rw [← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
  have h3 : ∑ x, g x ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
    exact Finset.single_le_sum (f := fun τ' => ∑ x, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ' x : ℤ) : ℝ) + (((D.hc τ').e i : ℚ) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  linarith

theorem log_dimAt_le : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau),
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  intro D i L hL τ
  obtain ⟨hf, hs, -, -⟩ := hL

  have hb2 : (2 : ℝ) ≤ Real.exp L := by
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
    have hfn : 2 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
    have hn : 1 ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    have : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by
      have : 2 ≤ D.R.f * D.R.r * D.R.nV := by
        calc 2 ≤ D.R.f := hfn
          _ = D.R.f * 1 * 1 := by ring
          _ ≤ D.R.f * D.R.r * D.R.nV := by gcongr
      exact_mod_cast this
    linarith
  have hL0 : 0 ≤ L := by
    by_contra h; push_neg at h
    have := Real.exp_lt_exp.2 h; rw [Real.exp_zero] at this; linarith
  set b := Real.exp L with hbdef
  set B := b ^ 2
  have h1B : 1 + B ≤ Real.exp (3 * L) := by
    rw [show 3 * L = L + L + L by ring, Real.exp_add, Real.exp_add, ← hbdef]
    nlinarith
  have hlog1B : Real.log (1 + B) ≤ 3 * L := by
    have := Real.log_le_log (by positivity) h1B
    rwa [Real.log_exp] at this

  set p := ((Wc D i).sig (tauE D τ)).1
  set q := ((Wc D i).sig (tauE D τ)).2
  have hpq : p + q = D.R.r := by
    have hr := D.sp.W_rank ((i:ℕ)+1) (by omega) (by have := i.2; omega)
    rw [← hr]; obtain ⟨e, -⟩ := (D.sp.W_sig ((i:ℕ)+1)) (tauE D τ); simpa using (Fintype.card_congr e).symm
  set κ := Formalism.L2.NTheta.wtOf D (Wc D i) τ
  have hent : ∀ a b, |((κ a - κ b : ℤ) : ℝ)| ≤ B := fun a b => (abs_wt_sub_le D i τ a b).trans (hs i)
  set N1 := ∑ a : Fin p, (Finset.univ.filter (fun j : Fin p => a < j)).card
  set N2 := ∑ a : Fin q, (Finset.univ.filter (fun j : Fin q => a < j)).card
  have w1 := abs_weylDimU_le (fun a => κ (Sum.inl a)) B (fun a b => hent _ _)
  have w2 := abs_weylDimU_le (fun a => κ (Sum.inr a)) B (fun a b => hent _ _)
  have hdim : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ =
      ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inl a)) : ℚ) : ℝ) *
        ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inr a)) : ℚ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt Formalism.IndefR.Mult.dimK; push_cast; rfl
  have habs : |GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| ≤ (1 + B) ^ (N1 + N2) := by
    rw [hdim, abs_mul, pow_add]
    exact mul_le_mul w1 w2 (abs_nonneg _) (by positivity)
  have hlog : Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := by
    rw [← Real.log_abs]
    rcases eq_or_ne (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) 0 with h0 | h0
    · rw [h0, abs_zero, Real.log_zero]
      have hB0 : (0 : ℝ) ≤ B := sq_nonneg b
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    · have := Real.log_le_log (abs_pos.2 h0) habs
      rwa [Real.log_pow] at this
  have hN : 2 * (N1 + N2) ≤ D.R.r ^ 2 := by
    have a1 : 2 * N1 ≤ p ^ 2 := two_mul_card_pairs_le p
    have a2 : 2 * N2 ≤ q ^ 2 := two_mul_card_pairs_le q
    have a3 : p ^ 2 + q ^ 2 ≤ (p + q) ^ 2 := by ring_nf; omega
    rw [← hpq]; omega
  have hN' : 2 * ((N1 + N2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ ((N1 + N2 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := hlog
    _ ≤ ((N1 + N2 : ℕ) : ℝ) * (3 * L) := mul_le_mul_of_nonneg_left hlog1B hN0
    _ = 3 / 2 * (2 * ((N1 + N2 : ℕ) : ℝ)) * L := by ring
    _ ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by gcongr

end GlobalTheory.OneMeasDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  first | exact @GlobalTheory.OneMeasDim.log_dimAt_le | exact GlobalTheory.OneMeasDim.log_dimAt_le | (intros; apply GlobalTheory.OneMeasDim.log_dimAt_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitBasisWittModelLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAdeleSplitPlaceMatrixCoordinateEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAdeleSplitPlaceMatrixCoordinateEq
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.VacLift

theorem exists_lift_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : Fv F v) :
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ piW t z = a := by
  have hp : ∀ (s : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s z = splitProj s (compFin F E v z) := fun s z => rfl
  have hs : ∀ (s : E →ₐ[F] Fv F v) (u : AF F) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piW s (u • z) = evFin F v u * piW s z := by
    intro s u z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hp]
    change splitProj s (TensorProduct.tmul F (evFin F v u) (1 : E)) = _
    rw [splitProj_tmul, map_one, mul_one]
  refine ⟨GlobalTheory.LatVac.liftV v a • Supp.splitIdemAd h t, ?_, ?_, ?_⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self]
    simp [splitIdem]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self, GlobalTheory.LatVac.evFin_liftV]
    simp [splitIdem]

theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  intro F E _ _ _ _ _ σ n d h v t b c Y
  choose f hf using exists_lift_scalar h v t
  refine ⟨(b.1 * Y * c.1ᵀ).map f, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (hf _).1 u hu
  · exact Matrix.ext fun i j => (hf _).2.1
  · have e : ((b.1 * Y * c.1ᵀ).map f).map (piW t) = b.1 * Y * c.1ᵀ :=
      Matrix.ext fun i j => (hf _).2.2
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]

end GlobalTheory.VacLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAdeleSplitPlaceMatrixCoordinateEqStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  first | exact @GlobalTheory.VacLift.exists_lift | exact GlobalTheory.VacLift.exists_lift | (intros; apply GlobalTheory.VacLift.exists_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTensorLatticeComponentIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTensorLatticeComponentIntegral
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem piW_smul_incl (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (e : E) :
    piW t (a • inclR (F := F) (AF F) e) = evFin F v a * t e := by
  simp [piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]

theorem comp_mem_splitLat (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ L) : (fun i => t (x i)) ∈ splitLat t L := by
  refine ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩
  simp [splitVec, splitProj_tmul]

end GlobalTheory.LatInt

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem map_piW_gen (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    (a • incM F (Matrix.vecMulVec x y)).map (piW t) =
      evFin F v a • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [piW_smul_incl, map_mul]

theorem latAtV_comp_integral {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) :
    ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, x, hx, y, hy, rfl⟩ := hz
    have hx' := (hb.mem_iff).1 (comp_mem_splitLat v t hx)
    have hy' := (hc.mem_iff).1 (comp_mem_splitLat v t hy)
    intro i j
    rw [map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem ha (mul_mem (hx' i) (hy' j))
  | zero => intro i j; simp
  | add γ δ _ _ hγ hδ =>
    intro i j
    rw [Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem (hγ i j) (hδ i j)
  | neg γ _ hγ =>
    intro i j
    rw [Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem (hγ i j)

end GlobalTheory.LatInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTensorLatticeComponentIntegralStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_tensorLattice_component_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)),
    IsSplitBasis t X.L b → IsSplitBasis t W.L c → ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.LatInt.latAtV_comp_integral | exact GlobalTheory.LatInt.latAtV_comp_integral | (intros; apply GlobalTheory.LatInt.latAtV_comp_integral <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.VacLinW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem symp_eq_zero_of_comp (hcm : IsCMExt F E σ) {v : Pl (F := F)} (s : E →ₐ[F] Fv F v)
    {x y : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hx : At (evFin F v) x) (hx0 : x.map (piW (s.comp σ)) = 0)
    (hy0 : y.map (piW (s.comp σ)) = 0) (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (JA : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : symp (cA σ) ξ JA JB x y = 0 := by
  set z := hTens (cA σ) JA JB x y with hz
  have hat : At (evFin F v) z := by
    intro c hc
    have hij : ∀ i j, c • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx c hc) i) j
      simpa using this
    simp only [hz, hTens, Finset.smul_sum, ← smul_mul_assoc, hij, zero_mul, Finset.sum_const_zero]
  have hx' : ∀ i j, piW (s.comp σ) (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx0 i) j
  have hy' : ∀ i j, piW (s.comp σ) (y i j) = 0 := fun i j => by simpa using congrFun (congrFun hy0 i) j
  have h1 : piW s z = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, hTens, map_sum, map_mul, GlobalTheory.VacIso.piW_cA, hy', mul_zero, Finset.sum_const_zero]
  have h2 : piW (s.comp σ) z = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, hTens, map_sum, map_mul, hx', zero_mul, Finset.sum_const_zero]
  have : z = 0 := GlobalTheory.VacIso.eq_zero_of_at_split hcm s hat h1 h2
  simp only [symp, ← hz, this, mul_zero, map_zero]

theorem symp_add_right (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (JA : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (x y y' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    symp (cA σ) ξ JA JB x (y + y') = symp (cA σ) ξ JA JB x y + symp (cA σ) ξ JA JB x y' := by
  simp only [symp, hTens, Matrix.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem isLin_smul {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl (F := F)}
    {π₁ π₀ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v} {co : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (Fv F v)}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} (h : M.IsLin ψ π₁ π₀ co ι)
    {z : ℂ} (hz : z ≠ 0) : M.IsLin ψ π₁ π₀ co (z • ι) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' e => ?_, fun g hg => ?_⟩
    · simp only [LinearMap.smul_apply]; exact Submodule.smul_mem _ z (h.bij.mapsTo hφ)
    · simp only [LinearMap.smul_apply] at e
      exact h.bij.injOn hφ hφ' (smul_right_injective _ hz e)
    · obtain ⟨φ, hφ, e⟩ := h.bij.surjOn (Submodule.smul_mem _ z⁻¹ hg)
      refine ⟨φ, hφ, ?_⟩
      simp only [LinearMap.smul_apply, e, smul_smul, mul_inv_cancel₀ hz, one_smul]
  · intro u hu h0 φ hφ φ₁ hφ₁ hA Y
    simp only [LinearMap.smul_apply, Pi.smul_apply, h.trans u hu h0 φ hφ φ₁ hφ₁ hA Y]
  · intro u hu h1 φ hφ φ₁ hφ₁ hA x hx hx0
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h.mult u hu h1 φ hφ φ₁ hφ₁ hA x hx hx0]
    ring

end GlobalTheory.VacLinW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.ProjSpace

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem regAt_fnMap_of (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {y : Y} {t : X.functionField}
    (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [fnMap_fnOf j hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

theorem fnOf_appLE (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} {V : Y.Opens}
    (e : V ≤ j ⁻¹ᵁ U) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V h' ((j.appLE U V e).hom a) = fnMap j hη (fnOf U h a) := by
  rw [fnMap_fnOf j hη h (e h')]
  exact fnOf_resG e h' (j.app U a)

theorem comp_genericPoint_specializes {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X) :
    (a ≫ b) (genericPoint Z) ⤳ genericPoint X := by
  rw [Scheme.Hom.comp_apply]
  exact (ha.map b.continuous).trans hb

theorem fnMap_comp {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X)
    (hab : (a ≫ b) (genericPoint Z) ⤳ genericPoint X) (t : X.functionField) :
    fnMap (a ≫ b) hab t = fnMap a ha (fnMap b hb t) := by
  obtain ⟨U, hx, s, rfl⟩ := (regAt_genericPoint t).exists_fnOf
  have h1 : genericPoint Y ∈ b ⁻¹ᵁ U := hb.mem_open U.isOpen hx
  have h2 : genericPoint Z ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U) := ha.mem_open (b ⁻¹ᵁ U).isOpen h1
  rw [fnMap_fnOf b hb _ h1, fnMap_fnOf a ha _ h2, fnMap_fnOf (a ≫ b) hab _ h2, Scheme.Hom.comp_app]
  rfl

theorem fnMap_congr {a b : Y ⟶ X} (e : a = b) (ha : a (genericPoint Y) ⤳ genericPoint X)
    (hb : b (genericPoint Y) ⤳ genericPoint X) (t : X.functionField) : fnMap a ha t = fnMap b hb t := by
  subst e; rfl
end

theorem exists_ratCoords : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    (φ : U.toScheme ⟶ PSpace F N),
    haveI : Nonempty U := hU.to_subtype
    haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      ∀ (u : U.toScheme) (k : Fin (N + 1)) (hk : u ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k), w k ≠ 0 ∧ ∀ j,
        GlobalTheory.TrueGeo.SmallSec.fnMap U.ι (specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)) (w j / w k) =
          GlobalTheory.Cartier.fnOf (φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k) (GlobalTheory.Cartier.gen_mem hk)
            (GlobalTheory.ProjSpace.pullRatio φ _ k le_rfl j) := by
  intro F _ Y _ N U hU φ
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨i₀, hi₀⟩ := exists_mem_chart F N (φ (genericPoint U.toScheme))
  have hg₀ : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ := hi₀
  choose w hw using fun j => fnMap_surjective U.ι hηU (fnOf _ hg₀ (pullRatio φ _ i₀ le_rfl j))
  refine ⟨w, i₀, ?_, fun u k hk => ?_⟩
  · apply (fnMap U.ι hηU).injective
    rw [hw, pullRatio_self, map_one, map_one]
  have hV : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ ⊓ φ ⁻¹ᵁ chart F N k := ⟨hg₀, gen_mem hk⟩
  have hmul : ∀ j, fnMap U.ι hηU (w j) =
      fnMap U.ι hηU (w k) * fnOf _ (gen_mem hk) (pullRatio φ _ k le_rfl j) := by
    intro j
    rw [hw, hw, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_right hV, ← map_mul,
      resG_pullRatio, resG_pullRatio, resG_pullRatio, pullRatio_mul_pullRatio]
  have hk0 : fnMap U.ι hηU (w k) ≠ 0 := by
    rw [hw, ← fnOf_resG inf_le_left hV, resG_pullRatio]
    refine ((unitAt_fnOf_iff hV hV _).2 ?_).ne_zero
    rw [basicOpen_pullRatio]
    exact ⟨hV, hV.2⟩
  refine ⟨fun h => hk0 (by rw [h, map_zero]), fun j => ?_⟩
  rw [map_div₀, hmul j, mul_div_cancel_left₀ _ hk0]

theorem exists_hom_of_ratCoords : ∀ (F : Type) [Field F] (N : ℕ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp F)
    (w : Fin (N + 1) → Y.functionField),
    (∀ y : Y, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ g : Y ⟶ PSpace F N, g ≫ PSpace.str F N = q ∧ ∀ (y : Y) (k : Fin (N + 1)), w k ≠ 0 →
      (∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
      ∃ (W : Y.Opens) (hy : y ∈ W) (hW : W ≤ g ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k),
        ∀ j, GlobalTheory.Cartier.fnOf W (GlobalTheory.Cartier.gen_mem hy) (GlobalTheory.ProjSpace.pullRatio g W k hW j) = w j / w k := by
  intro F _ N Y _ q w hw
  classical
  have hopen : ∀ k, IsOpen {y : Y | w k ≠ 0 ∧ ∀ j, RegAt y (w j / w k)} := fun k => by
    refine isOpen_iff_forall_mem_open.2 fun y ⟨h0, hy⟩ => ?_
    obtain ⟨W, hyW, hW⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
    refine ⟨W, fun y' hy' => ⟨h0, fun j => ?_⟩, W.isOpen, hyW⟩
    obtain ⟨a, ha⟩ := hW j
    exact ha ▸ regAt_fnOf hy' _ a
  let U' : Fin (N + 1) → Y.Opens := fun k => ⟨_, hopen k⟩
  have hr : ∀ k j, ∃ a : Γ(Y, U' k), ∀ h, fnOf (U' k) h a = w j / w k := fun k j => by
    by_cases h : genericPoint Y ∈ U' k
    · obtain ⟨a, ha⟩ := exists_fnOf_eq h fun y hy => hy.2 j
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose r hr using hr
  have H : IsCoordFamily U' r :=
    { cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hw y)
      self := fun k => fn_ext fun h => by rw [hr, map_one, div_self h.1]
      mul := fun i j k => fn_ext fun h => by
        rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hr, hr, hr]
        have hi : w i ≠ 0 := h.1.1
        have hj : w j ≠ 0 := h.2.1
        field_simp
      basicOpen_le := fun i j y hy => by
        have hyi : y ∈ U' i := Y.basicOpen_le _ hy
        have hu := (unitAt_fnOf_iff hyi (gen_mem hyi) (r i j)).2 hy
        rw [hr] at hu
        have hi0 : w i ≠ 0 := hyi.1
        have hj0 : w j ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_div])
        refine ⟨hj0, fun l => ?_⟩
        have := (hyi.2 l).mul hu.inv.regAt
        rwa [show w l / w i * (w j / w i)⁻¹ = w l / w j by field_simp] at this }
  refine ⟨H.toHom q, H.toHom_str q, fun y k hk0 hreg => ⟨U' k, ⟨hk0, hreg⟩, H.le_toHom_preimage q k, fun j => ?_⟩⟩
  rw [H.pullRatio_toHom q k j]
  exact hr k j _

theorem exists_ratCoords_extend : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  intro F _ Y _ p N U φ hφ hU
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨w, i₀, hw₀, hw⟩ := exists_ratCoords F Y N U hU φ
  have loc : ∀ (u : U.toScheme) k, u ∈ φ ⁻¹ᵁ chart F N k → w k ≠ 0 ∧ ∀ j, RegAt (U.ι u) (w j / w k) := by
    intro u k hk
    refine ⟨(hw u k hk).1, fun j => ?_⟩
    rw [← regAt_fnMap_iff U.ι hηU, (hw u k hk).2 j]
    exact regAt_fnOf hk _ _
  refine ⟨w, i₀, hw₀, fun y hy => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ⟨y, hy⟩)
    exact ⟨k, loc ⟨y, hy⟩ k hk⟩
  intro Y' _ s hη hY'
  obtain ⟨g, hg, hgW⟩ := exists_hom_of_ratCoords F N Y' (s ≫ p) (fun j => fnMap s (specializes_of_eq hη) (w j)) hY'
  refine ⟨g, hg, hom_ext ?_ fun z => ?_⟩
  · rw [Category.assoc, hg, Category.assoc, hφ, ← Category.assoc (s ∣_ U), morphismRestrict_ι, Category.assoc]
  haveI : Nonempty (s ⁻¹ᵁ U).toScheme := ⟨z⟩
  haveI : IsIntegral (s ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have hu : U.ι ((s ∣_ U) z) = s ((s ⁻¹ᵁ U).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hηι : (s ⁻¹ᵁ U).ι (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint Y' :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have hηr : (s ∣_ U) (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint U.toScheme := by
    refine specializes_of_eq (U.ι.isOpenEmbedding.injective ?_)
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion, hη, genericPoint_eq_of_isOpenImmersion]
  obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ((s ∣_ U) z))
  obtain ⟨hk0, hreg⟩ := loc _ k hk
  have hreg' : ∀ j, RegAt ((s ⁻¹ᵁ U).ι z)
      (fnMap s (specializes_of_eq hη) (w j) / fnMap s (specializes_of_eq hη) (w k)) := fun j => by
    rw [← map_div₀]
    exact regAt_fnMap_of s _ (hu ▸ hreg j)
  obtain ⟨W, hzW, hW, hWj⟩ := hgW _ k ((map_ne_zero _).2 hk0) hreg'
  have hz : z ∈ (s ⁻¹ᵁ U).ι ⁻¹ᵁ W ⊓ (s ∣_ U) ⁻¹ᵁ (φ ⁻¹ᵁ chart F N k) := ⟨hzW, hk⟩
  refine ⟨_, hz, k, inf_le_left.trans ((s ⁻¹ᵁ U).ι.preimage_mono hW), inf_le_right, fun j => ?_⟩
  refine fnOf_injective _ (gen_mem hz) ?_
  rw [← appLE_pullRatio (φ := g) (hi := hW) (s ⁻¹ᵁ U).ι inf_le_left,
    ← appLE_pullRatio (φ := φ) (hi := le_rfl) (s ∣_ U) inf_le_right,
    fnOf_appLE _ hηι _ (gen_mem hzW), fnOf_appLE _ hηr _ (gen_mem hk), hWj, ← (hw _ k hk).2 j, ← map_div₀,
    ← fnMap_comp _ _ hηι (specializes_of_eq hη) (comp_genericPoint_specializes _ _ hηι (specializes_of_eq hη)),
    ← fnMap_comp _ _ hηr hηU (comp_genericPoint_specializes _ _ hηr hηU)]
  exact fnMap_congr (morphismRestrict_ι s U).symm _ _ _

end GlobalTheory.ProjSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpaceStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  first | exact @GlobalTheory.ProjSpace.exists_ratCoords_extend | exact GlobalTheory.ProjSpace.exists_ratCoords_extend | (intros; apply GlobalTheory.ProjSpace.exists_ratCoords_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupport
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem appLE_comp_cst {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (U : W.Opens) (A : W'.Opens) (h : A ≤ π ⁻¹ᵁ U) :
    (π.appLE U A h).hom.comp (cst f U) = cst (π ≫ f) A := by
  have e : f.appTop ≫ W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ π.appLE U A h =
      (π ≫ f).appTop ≫ W'.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop]
    simp [Scheme.Hom.appLE]
  ext r
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem cst_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (U : W.Opens) :
    cst (p ≫ Spec.map (CommRingCat.ofHom φ)) U = (cst p U).comp φ := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem comap_baseIdeal {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (J : Ideal R) : (baseIdeal f J).comap π = baseIdeal (π ≫ f) J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {p : W.affineOpens × W'.affineOpens // p.2.1 ≤ π ⁻¹ᵁ p.1.1}) (fun i => i.1.2) ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ (π x)))
    obtain ⟨A, hA, hxA, hAU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 W'.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U.1 from hxU)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(U, ⟨A, hA⟩), hAU⟩, hxA⟩
  · intro i
    rw [GlobalTheory.Principalise.comapIdealAffine _ π i.1.1 i.1.2 i.2, baseIdeal_ideal, baseIdeal_ideal, Ideal.map_map,
      appLE_comp_cst]

theorem baseIdeal_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R) :
    baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ) := by
  rw [baseIdeal, baseIdeal, Ideal.map_map, cst_comp_specMap]

theorem mem_support_baseIdeal {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (J : Ideal R) (x : W) : x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal := by
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
    ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
  have key : ∀ r, x ∈ W.basicOpen (cst f U.1 r) ↔ r ∉ (f x).asIdeal := by
    intro r
    simp only [cst, rs, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    simp only [hxU, TopologicalSpace.Opens.mem_inf, true_and]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, baseIdeal_ideal]
  unfold Ideal.map
  rw [Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h r hr
    by_contra hn
    exact h _ ⟨r, hr, rfl⟩ ((key r).2 hn)
  · rintro h _ ⟨r, hr, rfl⟩ hx
    exact (key r).1 hx (h hr)

theorem baseIdeal_calculus :
    (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) :=
  ⟨fun _ _ _ _ f π J => comap_baseIdeal f π J,
    fun _ _ _ _ φ _ p J => baseIdeal_comp_specMap φ p J,
    fun _ _ _ f J x => mem_support_baseIdeal f J x⟩

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support : (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) := by
  first | exact @GlobalTheory.FormalAlg.baseIdeal_calculus | exact GlobalTheory.FormalAlg.baseIdeal_calculus | (intros; apply GlobalTheory.FormalAlg.baseIdeal_calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem thetaChar_entire_ne_zero_automorphy : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → Differentiable ℂ (thetaChar τ a b) ∧ (∃ z, thetaChar τ a b z ≠ 0) ∧ ∀ M N z, thetaChar τ a b (z + perV τ M N) = autV τ a b M N z * thetaChar τ a b z := by
  intro g τ a b hs hp ha hb
  obtain ⟨h1, -⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g a b ha hb
  obtain ⟨hd, hne⟩ := h1 τ hs hp
  refine ⟨hd, hne, fun M N z => ?_⟩
  rw [perV, autV]
  unfold cv
  rw [GlobalTheory.ThetaAH.thetaChar_add_period hs a b z M N]
  congr 1
  rw [dotProduct_comm b]
  ring_nf

end GlobalTheory.MBLow.Cl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → Differentiable ℂ (thetaChar τ a b) ∧ (∃ z, thetaChar τ a b z ≠ 0) ∧ ∀ M N z, thetaChar τ a b (z + perV τ M N) = autV τ a b M N z * thetaChar τ a b z := by
  first | exact @GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy | exact GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy | (intros; apply GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkCompactFlagSpaceOverComponentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charZero_stalk_compactFlagSpaceOverComponent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z), CharZero ((Y₀ TF.X Z).presheaf.stalk y) := by
  intro E _ _ _ H Dw l Xo c TF Z y
  let f : c.F →+* (Y₀ TF.X Z).presheaf.stalk y :=
    ((Y₀ TF.X Z).presheaf.germ ⊤ y trivial).hom.comp
      ((str₀ TF.X Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
  exact charZero_of_injective_ringHom f.injective
end
