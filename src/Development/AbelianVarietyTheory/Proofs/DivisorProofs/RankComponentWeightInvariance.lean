module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfGermEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.Vanishing.ProdNe

theorem eq_zero_of_germ_eq_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    {p : Y ⟶ Sp k} {B : LB Y} (hc : ∀ z : Y, ∃ j, z ∈ B.U j) (f : H0 p B ⊤) (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) (h0 : H0.germ i y (show y ∈ (⊤ : Y.Opens) from trivial) hi f = 0) : f = 0 := by
  have hi0 : f.loc i = 0 := by
    apply germ_injective_of_isIntegral Y y (memInf (U := ⊤) trivial hi)
    rw [map_zero]
    exact h0
  refine H0.ext_germ fun z hz => ?_
  obtain ⟨j, hj⟩ := hc z
  refine ⟨j, hj, ?_⟩
  have hj0 : f.loc j = 0 := by
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (B.U i).isOpen (B.U j).isOpen ⟨y, hi⟩ ⟨z, hj⟩
    apply germ_injective_of_isIntegral Y w (memInf (U := ⊤) trivial hwj)
    rw [map_zero]
    have e := H0.germ_change (O := ⊤) i j w (show w ∈ (⊤ : Y.Opens) from trivial) hwi hwj f
    have e2 : H0.germ (O := ⊤) i w (show w ∈ (⊤ : Y.Opens) from trivial) hwi f = 0 := by
      rw [H0.germ_apply, hi0, map_zero]
    rw [e2] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h
  rw [H0.germ_apply, hj0, map_zero, map_zero]

theorem mul_ne_zero : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {P B N : LB Y} (C : ProdChart P B N) (σ : H0 p P ⊤) (f : H0 p B ⊤), σ ≠ 0 → f ≠ 0 → C.mul σ f ≠ 0 := by
  intro k _ Y _ p P B N C σ f hσ hf hmul
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨t, ha, hb, hc⟩ := C.cover y
  have e := C.germ_mul σ f t y trivial ha hb hc
  rw [hmul, map_zero] at e
  rcases mul_eq_zero.mp e.symm with h | h
  · exact hσ (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.a t, h.1⟩) σ y _ ha h)
  · exact hf (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.b t, h.2.1⟩) f y _ hb h)

end GlobalTheory.Vanishing.ProdNe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowth
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open Filter
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefCuspGrowth

theorem ofReal_le_growth (D : ℕ) (h : ℕ → ℕ) (r : ℕ → ℕ∞) {c : ℝ} (hc : 0 ≤ c)
    (ht : Tendsto (fun m : ℕ => (h m : ℝ) / (m : ℝ) ^ D) atTop (nhds (c / D.factorial)))
    (hle : ∀ m, (h m : ℕ∞) ≤ r (m + 1)) : ENNReal.ofReal c ≤ CompHt.growth D r := by
  have hf : (0 : ℝ) < D.factorial := by positivity
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (nhds 1) := tendsto_natCast_div_add_atTop 1
  have h2 : Tendsto (fun m : ℕ => (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D))
      atTop (nhds c) := by
    have := (ht.mul (h1.pow D)).const_mul (D.factorial : ℝ)
    rwa [one_pow, mul_one, mul_div_cancel₀ _ hf.ne'] at this
  have h3 := (ENNReal.tendsto_ofReal h2).limsup_eq
  rw [CompHt.growth, ← Filter.limsup_nat_add _ 1, ← h3]
  refine limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have e : (D.factorial : ℝ) * ((h m : ℝ) / (m : ℝ) ^ D * ((m : ℝ) / ((m : ℝ) + 1)) ^ D) =
      (D.factorial : ℝ) * (h m : ℝ) / ((m + 1 : ℕ) : ℝ) ^ D := by
    push_cast
    rw [div_pow]
    field_simp
  rw [e, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
  exact ENNReal.div_le_div_right (mul_le_mul_right (by exact_mod_cast ENat.toENNReal_le.2 (hle m)) _) _

section Comp

private def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')

private theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }

private theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }

private theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }

private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem cls_L₀_nsmul (u : AllWt.Weight Dw) (k : ℕ) :
    cls (L₀ X Z (k • u)) (isLB_L₀ X Z (k • u)) = k • cls (L₀ X Z u) (isLB_L₀ X Z u) := by
  induction k with
  | zero =>
    have e := cls_common_add (common₀ X Z) (0 : AllWt.Weight Dw) 0
    simp only [add_zero] at e
    rw [zero_smul]
    exact (left_eq_add.1 e).symm ▸ rfl
  | succ k ih =>
    have e := cls_common_add (common₀ X Z) (k • u) u
    rw [succ_nsmul, succ_nsmul, ← ih]
    exact e

end Comp

section Inj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem mul_mem_vanBd (u : AllWt.Weight Dw) (k : ℕ) (h : u + k • u = (k + 1) • u)
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (g : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) :
    ((common₀ X Z).addChart h).mul θ g ∈ vanBd X Z ((k + 1) • u) := by
  intro y hy i hi
  obtain ⟨t, ha, hb, hc⟩ := ((common₀ X Z).addChart h).cover y
  rw [H0.germ_change i (((common₀ X Z).addChart h).c t) y (memTop y) hi hc,
    ((common₀ X Z).addChart h).germ_mul θ g t y (memTop y) ha hb hc]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hθ y hy _ ha))

set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_le_rank [IsIntegral (Y₀ X Z)] (u : AllWt.Weight Dw) (k : ℕ) (hC : CuspIso X Z U ((k + 1) • u))
    {θ : H0 (str₀ X Z) (L₀ X Z u) ⊤} (hθ : θ ∈ vanBd X Z u) (hθ0 : θ ≠ 0) :
    (Module.finrank c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤) : ℕ∞) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((k + 1) • wtOf Dw u 0))) := by
  have h : u + k • u = (k + 1) • u := by rw [succ_nsmul, add_comm]
  let C := (common₀ X Z).addChart h
  let φ : H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤ →ₗ[c.F] Cusp Z U ((k + 1) • u) :=
    ofSpace X Z U ((k + 1) • u) ∘ₗ Submodule.inclusion hC.2 ∘ₗ
      LinearMap.codRestrict _ (C.mul θ) (mul_mem_vanBd X Z u k h hθ)
  have hφ : Function.Injective φ := by
    refine (ofSpace_injective X Z U _).comp ((Submodule.inclusion_injective hC.2).comp fun g g' e => ?_)
    have e' : C.mul θ g = C.mul θ g' := congrArg Subtype.val e
    by_contra hne
    refine GlobalTheory.Vanishing.ProdNe.mul_ne_zero C θ (g - g') hθ0 (sub_ne_zero.2 hne) ?_
    rw [map_sub, e', sub_self]
  have e : cuspOn U Z ((k + 1) • wtOf Dw u 0) = Cusp Z U ((k + 1) • u) := by
    rw [CompHt.nsmul_wtOf, smul_zero]
  rw [e]
  have hr := LinearMap.rank_le_of_injective φ hφ
  by_cases hfin : FiniteDimensional c.F (H0 (str₀ X Z) (L₀ X Z (k • u)) ⊤)
  · rw [← Module.finrank_eq_rank] at hr
    exact (Cardinal.toENat_nat _).symm.le.trans (OrderHomClass.mono Cardinal.toENat hr)
  · rw [Module.finrank_of_not_finite hfin]
    exact bot_le

end Inj

theorem topSelf_le_growthOn : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) →
    letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) →
    ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  intro hN E _ _ _ H Dw l Xo c Y X Z r U u hV hD hC hf
  obtain ⟨f, hf⟩ := hf
  letI := algebraΓOfHom (str₀ X Z)
  intro hnef
  let S : LinSys c.F := ⟨Y₀ X Z, str₀ X Z, dimFlag Dw, L₀ X Z u, isLB_L₀ X Z u, 0, Fin.elim0⟩
  have hS : S.IsVariety := ⟨hV.1, hV.2.1, hV.2.2, hD⟩
  haveI : IsIntegral (Y₀ X Z) := hS.isIntegral
  have hp : IsProjOver (strHom c.F (X := (Y₀ X Z))) := by
    rw [strHom_eq (f := str₀ X Z) fun _ => rfl]
    exact hV.2.1
  have hdim : topologicalKrullDim (Y₀ X Z) = dimFlag Dw := ImageDegree.topologicalKrullDim_eq S hS
  have ht := hN.2.2.tendsto hp hdim hnef
  have h0 := hN.2.2.topSelf_nonneg hp hdim hnef
  let θ := ((hC u).1.equiv f).1
  have hθ : θ ∈ vanBd X Z u := (hC u).1.space_le ((hC u).1.equiv f).2
  have hθ0 : θ ≠ 0 := fun e => hf ((hC u).1.equiv.map_eq_zero_iff.1 (Subtype.ext e))
  rw [CompHt.growthOn, dimFlag_eq]
  refine ofReal_le_growth (dimFlag Dw) (fun m => lbH0 c.F (lbPow (L₀ X Z u) m)) _ (Int.cast_nonneg h0) ht fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow (isLB_L₀ X Z u) m) (isLB_L₀ X Z (m • u))
    (by rw [cls_lbPow (isLB_L₀ X Z u), cls_L₀_nsmul]), ← H0.finrank_top]
  exact finrank_le_rank X Z U u m (hC _) hθ hθ0

end GlobalTheory.NefCuspGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowthStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_nef_le_cuspFormGrowth : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) → letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) → ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  first | exact @GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | exact GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | (intros; apply GlobalTheory.NefCuspGrowth.topSelf_le_growthOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteV
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteV
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PureTransc

theorem isDomain_tensor (k : Type) [Field k] (σ : Type) (A : Type) [CommRing A] [IsDomain A]
    [Algebra k A] : IsDomain (FractionRing (MvPolynomial σ k) ⊗[k] A) := by
  let P := MvPolynomial σ k
  let K := FractionRing P
  letI : Algebra (P ⊗[k] A) (K ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P K) (AlgHom.id k A)).toAlgebra
  haveI : IsScalarTower P (P ⊗[k] A) (K ⊗[k] A) :=
    .of_algebraMap_eq fun x => by simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct k A (nonZeroDivisors P) K
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  let e : P ⊗[k] A ≃+* MvPolynomial σ A :=
    ((Algebra.TensorProduct.comm k P A).toRingEquiv.trans
      (MvPolynomial.scalarRTensorAlgEquiv).toRingEquiv)
  haveI : IsDomain (P ⊗[k] A) := e.toMulEquiv.isDomain
  have hinj : Function.Injective (algebraMap P (P ⊗[k] A)) :=
    Algebra.TensorProduct.includeLeft_injective (S := P) (algebraMap k A).injective
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[k] A)
    (M := Algebra.algebraMapSubmonoid (P ⊗[k] A) (nonZeroDivisors P)) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero hp (hinj (h.trans (map_zero _).symm))

theorem isIntegral_of_isPullback : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X),
    IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) →
    IsIntegral X' := by
  intro k _ N X X' _ f f' π H

  have chart (x : X) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : IsDomain A)
      (j : Sp A ⟶ X) (_ : IsOpenImmersion j) (q : PrimeSpectrum A),
      j q = x ∧ j ≫ f = spMap (algebraMap k A) := by
    obtain ⟨A, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f x
    have : Nonempty (Spec (.of A)) := ⟨q⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion j
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    exact ⟨A, _, _, this, j, inferInstance, q, hq, hj⟩
  have lift {A : Type} [CommRing A] [Algebra k A] [IsDomain A] (j : Sp A ⟶ X) [IsOpenImmersion j]
      (hj : j ≫ f = spMap (algebraMap k A)) (x' : X') (hx : π x' ∈ Set.range j) :
      ∃ (j₀ : Sp (FractionRing (MvPolynomial (Fin N) k) ⊗[k] A) ⟶ X') (_ : IsOpenImmersion j₀),
        x' ∈ Set.range j₀ := by
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    refine ⟨j₀, hj₀, ?_⟩
    have hr : x' ∈ Set.range (Limits.pullback.fst π j) := by
      rw [Scheme.Pullback.range_fst]; exact hx
    obtain ⟨z, rfl⟩ := hr
    exact ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst]⟩
  have hflat : Flat π := by
    refine MorphismProperty.of_isPullback H.flip ?_
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    exact GlobalTheory.GeomIrr.flat_of_field _
  have : IsReduced X' := by
    have (x' : X') : _root_.IsReduced (X'.presheaf.stalk x') := by
      obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (π x')
      obtain ⟨j₀, _, z, rfl⟩ := lift j hj x' ⟨q, hq⟩
      have := isDomain_tensor k (Fin N) A
      exact isReduced_of_injective
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.toRingHom
        (asIso (j₀.stalkMap z)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk X'
  have : IrreducibleSpace X' := by
    obtain ⟨A, _, _, _, j, _, q, hq, hj⟩ := chart (genericPoint X)
    obtain ⟨j₀, hj₀, H'⟩ := exists_affine_chart_of_isPullback H j hj
    have := isDomain_tensor k (Fin N) A
    have hirr : IsIrreducible (Set.range j₀) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ j₀.continuous.continuousOn
    have hdense : closure (Set.range j₀) = Set.univ := by
      refine Set.eq_univ_of_forall fun x' => ?_
      obtain ⟨y, hy, e⟩ := Flat.generalizingMap π (genericPoint_specializes (π x'))
      have hr : y ∈ Set.range (Limits.pullback.fst π j) := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, e]; exact ⟨q, hq⟩
      obtain ⟨z, hz⟩ := hr
      have hy' : y ∈ Set.range j₀ :=
        ⟨H'.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, H'.isoPullback_inv_fst, hz]⟩
      exact closure_mono (Set.singleton_subset_iff.2 hy') (specializes_iff_mem_closure.1 hy)
    refine (irreducibleSpace_def X').2 ?_
    rw [Set.top_eq_univ, ← hdense]
    exact hirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X'

end GlobalTheory.PureTransc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteVStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_baseChange_rationalFunctionField_finiteVars : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → IsIntegral X' := by
  first | exact @GlobalTheory.PureTransc.isIntegral_of_isPullback | exact GlobalTheory.PureTransc.isIntegral_of_isPullback | (intros; apply GlobalTheory.PureTransc.isIntegral_of_isPullback <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open Limits

namespace GlobalTheory.JetRank

theorem isProjOver_along {k : Type} [Field k] {X Z : Scheme.{0}} [Algebra k Γ(X, ⊤)] (hp : IsProjOver (strHom k (X := X)))
    (i : Z ⟶ X) [IsClosedImmersion i] : letI := algebraΓAlong k i; IsProjOver (strHom k (X := Z)) := by
  letI := algebraΓAlong k i
  obtain ⟨n, e, he, hs⟩ := hp
  exact ⟨n, i ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom (appTop_algebraMap_along k i)]⟩

section Nef

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

theorem dim_zeroScheme_le [IsIntegral X] [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) {t : L.Sec} (ht : t ≠ 0) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) : topologicalKrullDim (secIdeal hL t).subscheme ≤ d := by
  have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
  refine le_of_eq_of_le ?_ (suppDim_cut_le (structureModule _) hL t (d := d) (by rwa [QCoh.suppDim_structureModule]))
  rw [QCoh.suppDim, support_cut_eq_inter, QCoh.support_structureModule, Set.univ_inter]
  exact (topologicalKrullDim_eq_of_isEmbedding (secIdeal hL t).subschemeι.isClosedEmbedding.isEmbedding
    (secIdeal hL t).range_subschemeι).symm

theorem globalSections_dim_le_div_add_restriction [IsIntegral X] (hp : IsProjOver (strHom k (X := X))) {L B : LB X} (hL : L.IsLB) (hB : B.IsLB) {t : L.Sec}
    (ht : t ≠ 0) : letI := algebraΓAlong k (secIdeal hL t).subschemeι
    lbH0 k B ≤ lbH0 k (LB.div B L) + lbH0 k (B.pull (secIdeal hL t).subschemeι) := by
  set_option maxHeartbeats 16000000 in
    letI := algebraΓAlong k (secIdeal hL t).subschemeι
    have := isNoetherian_of_isProjOver hp
    have := (mono_cutHom_structureModule_iff hL t).2 ((sec_ne_zero_iff t).1 ht)
    have hF := finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp
    have h := hdim₂_le k (Twist.shortExact_map hB (shortExact_cutComplex (structureModule X) hL t)) 0
      ((hF.twist (Twist.isLB_lbZPow hL (-1)) _ hB).finite 0) ((hF.cut hL t _ hB).finite 0)
    obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule X) (Twist.isLB_lbZPow hL (-1)) hB
      (LB.isLB_div hB hL) (by rw [cls_div hB hL, cls_lbZPow hL]; abel)
    obtain ⟨e₂, -⟩ := exists_cut_structureModule_iso hL t
    have := Twist.isQuasicoherent_twist (F := structureModule _) (LB.isLB_pull hB (secIdeal hL t).subschemeι)
    refine h.trans_eq (congrArg₂ (· + ·) (hdim_congr k 0 e₁) ((hdim_congr k 0 ((twistFunctor B).mapIso e₂)).trans
      ((hdim_congr k 0 (Twist.projIso B _ _)).symm.trans ?_)))
    exact hdim_pushforward k (appTop_algebraMap_along k _) _ 0

theorem interNum_nonneg (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k (X := X))) {d : ℕ}
    (hd : topologicalKrullDim X ≤ d) {P : Fin d → LB X} (hP : ∀ i, IsNef k (P i)) :
    0 ≤ interNum k (structureModule X) P := by
  rcases hd.eq_or_lt with h | h
  · exact hN.1.interNum_nonneg hp h hP
  · exact (interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom k X) _ hp
      (by rwa [QCoh.suppDim_structureModule, Fintype.card_fin]) fun i => (hP i).isLB).ge

theorem interNum_cons_nonneg [IsIntegral X] (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k (X := X))) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {B : LB X} {P : Fin d → LB X} (hB : B.IsLB) (hs : HasNonzeroSec B)
    (hP : ∀ i, IsNef k (P i)) : 0 ≤ interNum k (structureModule X) (Fin.cons B P : Fin (d + 1) → LB X) := by
  obtain ⟨t, ht⟩ := hs
  have := isNoetherian_of_isProjOver hp
  have := (mono_cutHom_structureModule_iff hB t).2 ((sec_ne_zero_iff t).1 ht)
  letI := algebraΓAlong k (secIdeal hB t).subschemeι
  have hi := appTop_algebraMap_along k (secIdeal hB t).subschemeι
  rw [interNum_cons_eq_interNumSub hB t (fun i => (hP i).isLB)
    (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X) _ hp), interNumSub_def,
    interNumOn_eq_interNum_pull hi fun i => (hP i).isLB]
  exact interNum_nonneg hN (isProjOver_along hp _) (dim_zeroScheme_le hB ht hd)
    fun i => (hP i).pull_of_isClosedImmersion _ hi

theorem interNum_mono [IsIntegral X] (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k (X := X))) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {P Q R : Fin (d + 1) → LB X} (hP : ∀ i, IsNef k (P i))
    (hQ : ∀ i, IsNef k (Q i)) (hR : ∀ i, (R i).IsLB) (hR' : ∀ i, IsNef k (R i) ∨ HasNonzeroSec (R i))
    (e : ∀ i, cls (Q i) (hQ i).isLB = cls (P i) (hP i).isLB + cls (R i) (hR i)) :
    interNum k (structureModule X) P ≤ interNum k (structureModule X) Q := by
  have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp (d := d + 1)
    (by rwa [QCoh.suppDim_structureModule])
  have key : ∀ s : Finset (Fin (d + 1)),
      interNum k (structureModule X) P ≤ interNum k (structureModule X) (s.piecewise Q P) := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.piecewise_empty]
    | insert i s hi ih =>
      have hn : ∀ j, IsNef k (s.piecewise Q P j) := fun j => by
        by_cases h : j ∈ s
        · rw [Finset.piecewise_eq_of_mem _ _ _ h]; exact hQ j
        · rw [Finset.piecewise_eq_of_notMem _ _ _ h]; exact hP j
      rw [Finset.piecewise_insert, hV.interNum_update_of_cls_eq_add (by simp) (fun j => (hn j).isLB) i (hQ i).isLB
        (hP i).isLB (hR i) (e i), ← Finset.piecewise_eq_of_notMem s Q P hi, Function.update_eq_self]
      refine ih.trans (le_add_of_nonneg_right ?_)
      rcases hR' i with h | h
      · refine interNum_nonneg hN hp hd fun j => ?_
        by_cases hj : j = i
        · subst hj; rwa [Function.update_self]
        · rw [Function.update_of_ne hj]; exact hn j
      · rw [← interNum_comp_perm k _ (isLB_update (fun j => (hn j).isLB) i (hR i)) i.cycleRange.symm]
        refine (interNum_cons_nonneg hN hp hd (hR i) h fun j => hn (i.succAbove j)).trans_eq
          (congrArg _ (funext fun j => Fin.cases ?_ (fun j => ?_) j))
        · simp
        · simp
  simpa using key Finset.univ

theorem cons_const {α : Type*} (a : α) (d : ℕ) : (Fin.cons a (fun _ : Fin d => a) : Fin (d + 1) → α) = fun _ => a :=
  funext fun i => Fin.cases rfl (fun _ => rfl) i

theorem interNum_cons_le [IsIntegral X] (hN : GlobalTheory.Published.NefNumerics) (hp : IsProjOver (strHom k (X := X))) {d : ℕ}
    (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {B L L' P Q : LB X} (hB : IsNef k B) (hL : IsNef k L) (hL' : IsNef k L')
    (hP : P.IsLB) (hQ : IsNef k Q) (n : ℕ) (hs : HasNonzeroSec P) (e₁ : cls L' hL'.isLB = cls L hL.isLB + cls P hP)
    (e₂ : n • cls L' hL'.isLB = cls B hB.isLB + cls Q hQ.isLB) :
    interNum k (structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) ≤ n * topSelfIntersection k L' (d + 1) := by
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp (d := d + 1)
    (by rwa [QCoh.suppDim_structureModule])
  refine (interNum_mono hN hp hd (Q := Fin.cons (lbPow L' n) fun _ => L') (R := Fin.cons Q fun _ => P)
    (Fin.cases hB fun _ => hL) (Fin.cases (hL'.pow hA n) fun _ => hL') (Fin.cases hQ.isLB fun _ => hP)
    (Fin.cases (Or.inl hQ) fun _ => Or.inr hs) (Fin.cases ((cls_lbPow hL'.isLB _ _).trans e₂) fun _ => e₁)).trans_eq ?_
  have h := hV.interNum_update_of_cls_eq_zsmul (L := fun _ : Fin (d + 1) => L') (by simp) (fun _ => hL'.isLB) 0
    (isLB_lbPow hL'.isLB n) hL'.isLB n (by rw [cls_lbPow hL'.isLB, natCast_zsmul])
  rw [Function.update_eq_self 0 fun _ : Fin (d + 1) => L'] at h
  exact (congrArg _ (funext fun i => Fin.cases (by simp) (fun _ => by simp) i)).trans h

end Nef

theorem exists_step {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [a : Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) {d : ℕ} (hd : topologicalKrullDim X ≤ (d + 1 : ℕ)) {L : LB X} (hL : IsGenerated L) :
    ∃ (K : Type) (_ : Field K) (H : Scheme.{0}) (_ : Algebra K Γ(H, ⊤)) (ρ : H ⟶ X),
      IsProjOver (strHom K (X := H)) ∧ topologicalKrullDim H ≤ d ∧ (IsIntegral H ∨ IsEmpty H) ∧
      (∀ B : LB X, B.IsLB → lbH0 k B ≤ lbH0 k (LB.div B L) + lbH0 K (B.pull ρ)) ∧
      ∀ (e : ℕ) (P : Fin e → LB X), (∀ i, (P i).IsLB) →
        interNum K (structureModule H) (fun i => (P i).pull ρ) =
          interNum k (structureModule X) (Fin.cons L P : Fin (e + 1) → LB X) := by
  obtain ⟨f, rfl⟩ : ∃ f : X ⟶ Sp k, a = algebraΓOfHom f :=
    ⟨strHom k X, Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)⟩
  letI := algebraΓOfHom f
  rw [strHom_eq (f := f) fun _ => rfl] at hp
  have hLB := hL.isLB
  obtain ⟨N, b, hb⟩ := hL
  let K := FractionRing (MvPolynomial (Fin N) k)
  have H := IsPullback.of_hasPullback f (spMap (algebraMap k K))
  set π := pullback.fst f (spMap (algebraMap k K))
  set f' := pullback.snd f (spMap (algebraMap k K))
  letI := algebraΓOfHom f'
  obtain ⟨hpr, -⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hp
  have := GlobalTheory.T.isIntegral_baseChange_rationalFunctionField_finiteVars k N X _ f f' π H
  obtain ⟨t, ht, hH⟩ := GlobalTheory.T.isIntegral_or_isEmpty_generic_member_linearSystem k N X _ f f' π H L hLB b hb
  have hp' : IsProjOver (strHom K (X := (pullback f (spMap (algebraMap k K))))) := by
    rw [strHom_eq (f := f') fun _ => rfl]
    exact PosBaseChange.isProjOver_of_isPullback H hp
  have hL' := LB.isLB_pull hLB π
  have := isNoetherian_of_isProjOver hp'
  have := (mono_cutHom_structureModule_iff hL' t).2 ((sec_ne_zero_iff t).1 ht)
  set ι := (secIdeal hL' t).subschemeι
  letI := algebraΓAlong K ι
  refine ⟨K, inferInstance, _, algebraΓAlong K ι, ι ≫ π, isProjOver_along hp' ι, ?_, hH, fun B hB => ?_, fun e P hP => ?_⟩
  · exact dim_zeroScheme_le hL' ht ((GlobalTheory.T.topologicalKrullDim_fieldBaseChange_le k K X _ f f' π H).trans hd)
  · have h1 := globalSections_dim_le_div_add_restriction hp' hL' (LB.isLB_pull hB π) ht
    have e1 : lbH0 K (B.pull π) = lbH0 k B := FieldChangeInter.hdim_pull H hB 0
    have e2 : lbH0 K ((LB.div B L).pull π) = lbH0 k (LB.div B L) := FieldChangeInter.hdim_pull H (LB.isLB_div hB hLB) 0
    rw [e1, lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_div (LB.isLB_pull hB π) hL') (LB.isLB_pull (LB.isLB_div hB hLB) π) (by
      rw [cls_div (LB.isLB_pull hB π) hL', cls_pull (LB.isLB_div hB hLB), cls_div hB hLB, map_sub, cls_pull hB, cls_pull hLB]), e2,
      lineBundleGlobalSectionsDim_congr_picardClass (LB.isLB_pull (LB.isLB_pull hB π) ι) (LB.isLB_pull hB (ι ≫ π)) (by
        rw [cls_pull (LB.isLB_pull hB π), cls_pull hB, cls_pull hB, pull_comp])] at h1
    exact h1
  · rw [← FieldChangeInter.interNum_pull H (isLB_cons hLB hP)]
    have h1 := interNum_cons_eq_interNumSub (k := K) hL' t (P := fun i => (P i).pull π) (fun i => LB.isLB_pull (hP i) π)
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom K _) _ hp')
    rw [interNumSub_def, interNumOn_eq_interNum_pull (appTop_algebraMap_along K ι) (fun i => LB.isLB_pull (hP i) π)] at h1
    refine Eq.trans (interNum_congr_cls K _ (fun i => LB.isLB_pull (hP i) _)
      (fun i => LB.isLB_pull (LB.isLB_pull (hP i) π) ι) fun i => ?_) (h1.symm.trans (congrArg _ (funext fun i => ?_)))
    · rw [cls_pull (LB.isLB_pull (hP i) π), cls_pull (hP i), cls_pull (hP i), pull_comp]
    · exact Fin.cases rfl (fun _ => rfl) i

theorem globalSections_dim_le_of_intersection_bound (hN : GlobalTheory.Published.NefNumerics) (d : ℕ) : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → topologicalKrullDim X ≤ d → ∀ {L : LB X}, IsGenerated L →
    ∀ (a : ℕ) {B : LB X}, B.IsLB → (∀ e, d = e + 1 →
      interNum k (structureModule X) (Fin.cons B (fun _ : Fin e => L) : Fin (e + 1) → LB X) < (a + 1) * topSelfIntersection k L d) →
    (lbH0 k B : ℤ) ≤ (a + d).choose d * topSelfIntersection k L d := by
  induction d with
  | zero =>
    intro k _ X _ _ hp hd L hL a B hB _
    have := isNoetherian_of_isProjOver hp
    have h0 : QCoh.suppDim (structureModule X) ≤ 0 := by rw [QCoh.suppDim_structureModule]; exact hd
    rw [topSelf_def, interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k h0, lineBundleGlobalSectionsDim_def,
      hdim_twist_of_suppDim_le_zero k h0 hB]
    simp
  | succ d ih =>
    intro k _ X _ _ hp hd L hL
    have := isNoetherian_of_isProjOver hp
    have hf := algebraMap_eq_strHom k X
    have hnef : IsNef k L := hL.isNef_of_isProjOver hp
    obtain ⟨K, _, H, _, ρ, hp', hd', hH, h₁, h₂⟩ := exists_step hp hd hL
    have hδ : topSelfIntersection K (L.pull ρ) d = topSelfIntersection k L (d + 1) := by
      rw [topSelf_def, topSelf_def, ← cons_const]; exact h₂ d (fun _ => L) fun _ => hL.isLB
    have hδ₀ : 0 ≤ topSelfIntersection k L (d + 1) := by
      rw [topSelf_def, ← cons_const]
      exact interNum_cons_nonneg hN hp hd hL.isLB hL.hasNonzeroSec fun _ => hnef
    have key : ∀ (a : ℕ) {B : LB X}, B.IsLB →
        interNum k (structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < a * topSelfIntersection k L (d + 1) →
        (lbH0 k B : ℤ) ≤ (a + d).choose (d + 1) * topSelfIntersection k L (d + 1) := by
      intro a
      induction a with
      | zero =>
        intro B hB h
        have : lbH0 k B = 0 := by
          by_contra h0
          have := interNum_cons_nonneg (P := fun _ => L) hN hp hd hB (lineBundleHasNonzeroSection_of_globalSectionsDim_pos (Nat.pos_of_ne_zero h0)) fun _ => hnef
          simp only [Nat.cast_zero, zero_mul] at h
          omega
        rw [this]; positivity
      | succ a iha =>
        intro B hB h
        have hD := LB.isLB_div hB hL.isLB
        have e := (diffVanish_chiPic_of_isProjOver hf (structureModule X) hp (d := d + 1)
          (by rw [QCoh.suppDim_structureModule]; exact hd)).interNum_cons_of_cls_eq_add le_rfl (P := fun _ : Fin d => L)
          (fun _ => hL.isLB) hB hD hL.isLB (by rw [cls_div hB hL.isLB, sub_add_cancel])
        rw [cons_const, ← topSelf_def] at e
        have i₁ := iha hD (by push_cast at h; linarith)
        have i₂ : (lbH0 K (B.pull ρ) : ℤ) ≤ (a + d).choose d * topSelfIntersection k L (d + 1) := by
          rcases hH with hH | hH
          · rw [← hδ]
            refine ih K H hp' hd' (hL.pull ρ) a (LB.isLB_pull hB ρ) fun m he => ?_
            subst he
            have h₃ := h₂ (m + 1) (Fin.cons B fun _ => L) (isLB_cons hB fun _ => hL.isLB)
            rw [hδ]
            refine lt_of_eq_of_lt (Eq.trans (congrArg _ (funext fun i => Fin.cases rfl (fun _ => rfl) i)) (h₃.trans ?_))
              (by exact_mod_cast h)
            rw [← interNum_comp_perm k _ (isLB_cons hB fun _ => hL.isLB) (Equiv.swap 0 1)]
            refine congrArg _ (funext fun i => ?_)
            refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => ?_) i) i
            rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
            rfl
          · have : lbH0 K (B.pull ρ) = 0 := by
              by_contra h0
              obtain ⟨s, hs⟩ := lineBundleHasNonzeroSection_of_globalSectionsDim_pos (Nat.pos_of_ne_zero h0)
              exact hs ((Vanishing.H0.bijective_ofSec_top (p := strHom K H)).1
                (Vanishing.H0.ext_germ fun y _ => hH.elim y))
            rw [this]; positivity
        have i₃ : (lbH0 k B : ℤ) ≤ lbH0 k (LB.div B L) + lbH0 K (B.pull ρ) := by exact_mod_cast h₁ B hB
        rw [show a + 1 + d = (a + d) + 1 by ring, Nat.choose_succ_succ']
        push_cast
        linarith
    intro a B hB h
    rw [show a + (d + 1) = a + 1 + d by ring]
    exact key (a + 1) hB (by exact_mod_cast h d rfl)

section

open NumberField _root_.Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

theorem imageDeg_eq_del (hQ : GlobalTheory.HSCore.Quoted) {F : Type} [Field F] [NumberField F] (S : LinSys F) {V Ω : Type}
    [AddCommGroup V] [Module F V] [Field Ω] [Algebra F Ω] (ev : V →ₗ[F] Ω) (b : Module.Basis (Fin S.N) F V) (x : S.Pt Ω)
    {a : Ω} (hV : S.IsVariety) (hb : S.BasePointFree) (hx : IsGenericPoint (ptOf x.1) Set.univ) (ha : a ≠ 0)
    (hc : S.coords x.1 = a • fun j => ev (b j)) (hG : GlobalTheory.DegVal.GenRatios ev) :
    (GlobalTheory.CompHt.imageDeg ev S.D : ℤ) = S.del := by
  have : IsIntegral S.Y := hV.isIntegral
  have hB : S.Birational := by
    refine ⟨_, hx, ?_⟩
    obtain ⟨τ, hτ⟩ : ∃ τ : S.Y.residueField (ptOf x.1) →+* Ω, spMap τ ≫ resPt (ptOf x.1) = x.1 :=
      ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω S.Y x.1⟩
    have h₁ : S.ratioField x.1 ≤ (S.ratioField (resPt (ptOf x.1))).map τ := by
      have e₁ := S.coords_spMap_comp (resPt (ptOf x.1)) τ
      have e₂ : S.baseHom x.1 = τ.comp (S.baseHom (resPt (ptOf x.1))) :=
        LinSys.baseHom_ptOver (S := S) ⟨x.1, by
          rw [← congrArg (· ≫ S.str) hτ, Category.assoc, S.comp_str]; exact (Spec.map_comp _ _).symm⟩
      rw [hτ] at e₁
      refine Subfield.closure_le.2 ?_
      rintro _ (⟨r, rfl⟩ | ⟨i, j, rfl⟩)
      · exact ⟨_, Subfield.subset_closure (Or.inl ⟨r, rfl⟩), by rw [e₂]; rfl⟩
      · exact ⟨_, Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩), by rw [e₁, map_div₀]⟩
    have h₂ : S.ratioField x.1 = ⊤ := by
      obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
      have hF : ∀ r, algebraMap F Ω r ∈ S.ratioField x.1 := fun r =>
        Subfield.subset_closure (Or.inl ⟨r, by rw [LinSys.baseHom_ptOver]⟩)
      have h₃ : ∀ v, a * ev v / S.coords x.1 j ∈ S.ratioField x.1 := fun v => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← b.sum_repr v, map_sum, Finset.mul_sum, Finset.sum_div]
        refine sum_mem fun i _ => ?_
        rw [map_smul, Algebra.smul_def, mul_left_comm, mul_div_assoc]
        exact mul_mem (hF _) (Subfield.subset_closure (Or.inr ⟨i, j, by rw [congrFun hc i]; rfl⟩))
      have h₄ : GlobalTheory.DegVal.ratioField ev ≤ (S.ratioField x.1).toIntermediateField hF := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        rintro _ ⟨v, w, rfl⟩
        have := div_mem (h₃ v) (h₃ w)
        rwa [div_div_div_cancel_right₀ hj, mul_div_mul_left _ _ ha] at this
      exact top_le_iff.1 fun y _ => h₄ (hG.2.ge trivial)
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨z, hz, e⟩ := h₂.ge.trans h₁ (trivial : τ y ∈ ⊤)
    exact τ.injective e ▸ hz
  obtain ⟨-, hdeg, hdim⟩ := ImageDegree.degree_image_eq_topSelf hQ F S hV hb hB
  obtain ⟨f, hf, -⟩ := hQ.chowInt F S.N S.D S.imageIdeal S.isHomogeneous_imageIdeal
    (GlobalTheory.Adelic.HeightExists.isPrime_imageIdeal hV) hdim
  rw [GlobalTheory.CompHt.imageIdeal_eq_coneIdeal_of_generic F Ω S x hx a _ ha hc] at hf hdeg
  rw [GlobalTheory.CompHt.IsImageDeg.imageDeg_eq ⟨S.N, b, f, hf⟩]
  exact hdeg

theorem exists_basis_fin (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Module.Finite F V] :
    ∃ N, Nonempty (Module.Basis (Fin N) F V) := ⟨_, ⟨Module.finBasis F V⟩⟩

section Moving

open GlobalTheory.Vanishing.H0 GlobalTheory.LB GlobalTheory.TangentOrigin
open GlobalTheory.AllWt (secZ exOf)
open GlobalTheory.CompHt (genVal)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem exists_chart_val (h : GenFrEx Xo c) {u : AllWt.Weight Dw} (R : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
    (Δ : Cartier ((baseId X Z U u).comap R.σ)) (hfree : FreeOnOpen X Z U u)
    {z : Sp (Om Z) ⟶ R.X} (hz : z ≫ toFlag R = X.ptY (genFr h Z)) (hO : ⊤ ≤ z ⁻¹ᵁ R.off) :
    ∃ (i : Δ.moving.ι) (a : Om Z), ptOf z ∈ Δ.moving.U i ∧ a ≠ 0 ∧ ∀ (g : Cusp Z U u) (w : space X Z U u),
      restr le_top w.1 = cuspSec X Z U u g →
      valR z (Δ.moving.U i) ((toSec (Δ.lift w)).f i) = a * genVal Z g.1 := by
  classical
  have e₁ : (z ≫ R.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (ptOf ((z ≫ R.σ) ≫ inc₀ X Z))))
  have hk₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := (le_iff_ptOf_mem _ _).2 hk
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) k hk₁
  have hQ₂ : X.F.ChartFr k ((z ≫ R.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  have hU : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [R.off_eq] at this
    exact this
  have hO₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  obtain ⟨n, hn⟩ := exists_chart Δ.isLB (ptOf z)
  have hz' : ptOf z ∈ R.off := (le_iff_ptOf_mem _ _).1 hO
  have hm : ptOf z ∈ ((L₀ X Z u).pull R.σ).U (flagIdx R u k) := (((common₀ X Z).pull R.σ).mem _ _ _).2 hk
  have hi : ptOf z ∈ Δ.moving.U (flagIdx R u k, n) := ⟨hm, hn⟩
  have hτ : valR z _ (Δ.t.f n) ≠ 0 := (valR_ne_zero_iff z hn _).2
    ((mem_nonzeroLocus_iff_basicOpen Δ.t hn).1 ((Δ.mem_nonzeroLocus _).2 (R.notMem_support hfree _ hz')))
  obtain ⟨T, hT0, hT⟩ : ∃ T : Om Z, T ≠ 0 ∧ ∀ f : secZ Xo c (exOf Dw u 0),
      evR Xo c f.1 (genFr h Z) = T * H0.val (B := X.LL (exOf Dw u 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) :=
    ⟨_, Units.ne_zero _, fun f => evR_eq_val_secOf f hO₂ hQ₂ ht⟩
  refine ⟨(flagIdx R u k, n), (valR z _ (Δ.t.f n) * T)⁻¹, hi, inv_ne_zero (mul_ne_zero hτ hT0),
    fun g w hw => ?_⟩
  have hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : R.X.Opens) := fun _ _ => trivial
  have hTop' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens) := fun _ _ => trivial
  have hi' := (le_iff_ptOf_mem z _).2 hi
  have hm' := (le_iff_ptOf_mem z _).2 hm
  have hn' := (le_iff_ptOf_mem z _).2 hn
  have hm'' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (L₀ X Z u).U (flagIdx R u k PUnit.unit) := by
    have hm₀ : R.σ (ptOf z) ∈ (L₀ X Z u).U (flagIdx R u k PUnit.unit) := mem_pull.1 hm
    exact (le_iff_ptOf_mem _ _).2 hm₀
  have v₁ : valR z (Δ.moving.U (flagIdx R u k, n)) ((toSec (Δ.lift w)).f (flagIdx R u k, n)) =
      H0.val z _ hTop hi' (Δ.lift w) := by
    have := H0.val_ofSec (p := R.str) z (flagIdx R u k, n) hTop hi' (toSec (Δ.lift w))
    rw [ofSec_toSec] at this
    rw [this, valR_eq_evalPt z _ hi']
  have v₂ := (divChart (LB.isLB_pull (isLB_L₀ X Z u) R.σ) Δ.isLB).val_mul (ofSec R.str ⊤ Δ.t) (Δ.lift w)
    (flagIdx R u k, n) z hTop hn' hi' hm'
  have v₃ : H0.val z _ hTop hm' (H0.pull R.σ le_top w.1) = H0.val (z ≫ R.σ) _ hTop' hm'' w.1 :=
    H0.val_pull R.σ le_top z _ hTop hm' hTop' hm'' w.1
  have v₄ := val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) (z ≫ R.σ) _ hTop' hU hm'' w.1
  have v₅ : H0.val (z ≫ R.σ) _ hU hm'' (cuspSec X Z U u g) = H0.val (B := X.LL (exOf Dw u 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂
      (secOf X _ ⟨g.1, cusp_le_secZ Z U _ g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl (z ≫ R.σ) _ hU hm'' hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  have v₇ : H0.val z _ hTop hn' (ofSec R.str ⊤ Δ.t) = valR z _ (Δ.t.f n) := by
    rw [H0.val_ofSec, valR_eq_evalPt z _ hn']
  have v₈ := hT ⟨g.1, cusp_le_secZ Z U _ g.2⟩
  rw [v₁, v₆, v₈, ← v₅, ← hw, v₄, ← v₃, ← Δ.incl_lift w]
  have v₉ : H0.val z _ hTop hm' (Δ.incl ⊤ (Δ.lift w)) = valR z _ (Δ.t.f n) * H0.val z _ hTop hi' (Δ.lift w) :=
    v₂.trans (congrArg (· * _) v₇)
  rw [v₉]
  field_simp

theorem topSelf_moving (hQ : GlobalTheory.HSCore.Quoted) {u : AllWt.Weight Dw} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))
    (Δ : Cartier ((baseId X Z U u).comap M.σ)) (hV : IsVariety₀ X Z) (hD : 1 ≤ dimFlag Dw) (hE : Extends X Z U u)
    (hF : FreeOnOpen X Z U u) (hB : GlobalTheory.DegVal.BirOn U Z (wtOf Dw u 0)) :
    letI := algebraΓOfHom M.str
    IsGenerated Δ.moving ∧ topSelfIntersection c.F Δ.moving (dimFlag Dw) = GlobalTheory.CompHt.compDeg U Z (wtOf Dw u 0) := by
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have := finite_top hV.2.1 (isLB_L₀ X Z u)
  have : Module.Finite c.F (Cusp Z U u) := .equiv hE.equiv.symm
  obtain ⟨N, ⟨b⟩⟩ := exists_basis_fin c.F (Cusp Z U u)
  let S : LinSys c.F := ⟨M.X, M.str, dimFlag Dw, Δ.moving, Δ.isLB_moving, _, fun j => toSec (Δ.lift (hE.equiv (b j)))⟩
  have hS : S.IsVariety := ⟨M.smooth, M.proj,
    GlobalTheory.CompHS.Modif.geometricallyConnected_str _ _ _ _ _ M hV.1 hV.2.2 (dense_U₀ _ _), hD⟩
  have hb : S.BasePointFree := Δ.iSup_nonzeroLocus (b.map hE.equiv).span_eq
  refine ⟨⟨_, S.b, hb⟩, ?_⟩
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M hG
  have hstr : z ≫ S.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag M ≫ flagStr X) = _
    rw [← Category.assoc, hz, ptY_str]
  obtain ⟨i, a, hi, ha, hv⟩ := exists_chart_val hG M Δ hF hz hO
  obtain ⟨a', ha', h', -⟩ := S.exists_frame_change z i hi
  have key := imageDeg_eq_del hQ S (GlobalTheory.CompHt.genPoint Z (Cusp Z U u)) b ⟨z, hstr⟩ (a := a'⁻¹ * a) hS hb
    (isGenericPoint_of_lift M hG hz hO) (mul_ne_zero (inv_ne_zero ha') ha) (funext fun j => by
      have e := (h' (S.b j)).symm.trans (hv (b j) (hE.equiv (b j)) (hE.restr_equiv _))
      show S.val z _ = (a'⁻¹ * a) * genVal Z (b j).1
      rw [mul_assoc, ← e, inv_mul_cancel_left₀ ha']) hB
  rw [GlobalTheory.CompHt.compDeg, dimFlag_eq]
  exact key.symm

end Moving

theorem topSelf_pull (hN : GlobalTheory.Published.NefNumerics) {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hc : GeometricallyConnected p) (hD : 1 ≤ D)
    (M : Modif p U D) (hc' : GeometricallyConnected M.str) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom M.str
    IsIntegral M.X ∧ IsProjOver (strHom k (X := M.X)) ∧ topologicalKrullDim M.X = D ∧
      (∀ B : LB Y, B.IsLB → lbH0 k (B.pull M.σ) = lbH0 k B) ∧
      ∀ B : LB Y, IsNef k B → IsNef k (B.pull M.σ) ∧ topSelfIntersection k (B.pull M.σ) D = topSelfIntersection k B D := by
  letI := algebraΓOfHom p
  letI := algebraΓOfHom M.str
  have hV : LinSys.IsVariety ⟨Y, p, D, LB.triv Y, LB.isLB_triv Y, 0, Fin.elim0⟩ := ⟨hs, hp, hc, hD⟩
  have hV' : LinSys.IsVariety ⟨M.X, M.str, D, LB.triv _, LB.isLB_triv _, 0, Fin.elim0⟩ := ⟨M.smooth, M.proj, hc', hD⟩
  have : IsIntegral Y := hV.isIntegral
  have : IsIntegral M.X := hV'.isIntegral
  have hd : topologicalKrullDim Y = D := ImageDegree.topologicalKrullDim_eq _ hV
  have hd' : topologicalKrullDim M.X = D := ImageDegree.topologicalKrullDim_eq _ hV'
  have e : strHom k Y = p := strHom_eq fun _ => rfl
  have e' : strHom k M.X = M.str := strHom_eq fun _ => rfl
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨hpr', A', hA'⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB M.str).1 M.proj
  have : IsProper M.σ := IsProper.of_comp M.σ p
  have : IsProper (strHom k (X := Y)) := e ▸ hpr
  have h0 := GlobalTheory.T.modification_globalSectionsDim_pull_eq k Y p U D hs hp M
  have hp₁ : IsProjOver (strHom k (X := Y)) := by rw [e]; exact hp
  have hp₂ : IsProjOver (strHom k (X := M.X)) := by rw [e']; exact M.proj
  refine ⟨inferInstance, hp₂, hd', h0, fun B hB => ?_⟩
  have hB' : IsNef k (B.pull M.σ) := PosBaseChange.isNef_pull hB hA hA' M.σ M.σ.isClosedMap
  refine ⟨hB', ?_⟩
  have t := hN.2.2.tendsto hp₁ hd hB
  have t' := hN.2.2.tendsto hp₂ hd' hB'
  have e₁ : ∀ m, lbH0 k (lbPow (B.pull M.σ) m) = lbH0 k (lbPow B m) := fun m => by
    rw [← h0 _ (isLB_lbPow hB.isLB m)]
    exact lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hB'.isLB m) (LB.isLB_pull (isLB_lbPow hB.isLB m) _)
      (by rw [cls_lbPow hB'.isLB, cls_pull hB.1, cls_pull (isLB_lbPow hB.1 m), cls_lbPow hB.1, map_nsmul])
  simp only [e₁] at t'
  have := tendsto_nhds_unique t' t
  have hf : (D.factorial : ℝ) ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' hf).1 this

private def commonRestr' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')

private theorem isLB_commonRestr' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr' C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }

private theorem commonRestr_iso' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr' C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }

private theorem commonRestr_iso_tens' {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr' C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }

private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr' C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso' C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr' C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens' C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]

private theorem nonempty_cartier_of_locally_principal_local (Y : Scheme.{0}) (I : Y.IdealSheafData)
    (h : ∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧
      I.ideal W = Ideal.span {a}) : Nonempty (Cartier I) := by
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq (I := I) h
  have hLB : D.lb.IsLB := by
    refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (one_mul _).symm).symm
    · intro i j k
      have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
      have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
      have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
      refine Units.ext (D.eq_trans_on i k hi hk ?_)
      rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← mul_assoc]
      rfl
  refine ⟨{ P := D.lb, isLB := hLB, t := D.canonical, reg := fun i y hi => ?_, cut := ?_ }⟩
  · exact GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) y hi
  · refine ideal_ext_stalk fun y => ?_
    obtain ⟨i, hi⟩ := D.exists_mem y
    rw [stalkId_cutIdeal hLB _ i y hi, ← hD, D.stalkId_idealSheaf i y hi, Set.range_const]
    rfl

private def pullOfInt_local {Y T : Scheme.{0}} [IsIntegral T] {I : Y.IdealSheafData} (Δ : Cartier I) (r : T ⟶ Y) {z₀ : T}
    (hz : r z₀ ∉ I.support) : Cartier (I.comap r) :=
  { Cartier.ofSec (LB.isLB_pull Δ.isLB r) (secPull Δ.t r) (y₀ := z₀)
      (by rw [nonzeroLocus_secPull]; exact (Δ.mem_nonzeroLocus _).2 hz) with
    cut := (GlobalTheory.Vanishing.eq_comap_of_stalk
      (fun z => GlobalTheory.Vanishing.stalkId_cutIdeal_secPull Δ.isLB (fun _ : Unit => Δ.t) z)).trans (by rw [Δ.cut]) }

private theorem ne_bot_of_notMem_local {Y : Scheme.{0}} {I : Y.IdealSheafData} {y : Y} (h : y ∉ I.support) : I ≠ ⊥ := fun e => by
  rw [e, Scheme.IdealSheafData.support_bot] at h
  exact h trivial

private theorem nonempty_resol (hPr : GlobalTheory.Published.Principalisation) {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}}
    {p : Y ⟶ Sp F} {D : ℕ} (hs : SmoothOfRelativeDimension D p) (hp : IsProjOver p) (hc : GeometricallyConnected p)
    {U : Y.Opens} (hU : (U : Set Y).Nonempty) {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) {a₁ a₂ : Λ}
    {W₁ : Submodule F (H0 p (B a₁) ⊤)} {W₂ : Submodule F (H0 p (B a₂) ⊤)}
    (h₁ : NoBase (C.isLB a₁) W₁ U) (h₂ : NoBase (C.isLB a₂) W₂ U) : Nonempty (Resol C U D W₁ W₂) := by
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres p
  have hY : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral (f := p) (K := F) (𝟙 _) (𝟙 Y) p IsPullback.of_id_fst
  obtain ⟨u, hu⟩ := hU
  obtain ⟨Y₁, s₁, hi₁, hs₁, hp₁, hb₁, -, hc₁, -⟩ :=
    hPr F D Y p hY hs hp (baseIdeal (C.isLB a₁) W₁) (ne_bot_of_notMem_local (h₁ u hu))
  have iso₁ : IsIso (s₁ ∣_ U) := hb₁.isIso_restrict U h₁
  obtain ⟨z₁, hz₁⟩ : ∃ z : Y₁, z ∈ s₁ ⁻¹ᵁ U :=
    let z := inv (s₁ ∣_ U) ⟨u, hu⟩
    ⟨z.1, z.2⟩
  let M₁ : Modif p U D := ⟨Y₁, s₁, hs₁, hp₁, iso₁, (s₁ ⁻¹ᵁ U).isOpen.dense ⟨z₁, hz₁⟩⟩
  have off₂ : ∀ y ∈ s₁ ⁻¹ᵁ U, y ∉ ((baseIdeal (C.isLB a₂) W₂).comap s₁).support := fun y hy h => by
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h₂ _ hy h
  obtain ⟨Y₂, s₂, hi₂, hs₂, hp₂, hb₂, -, hc₂, -⟩ :=
    hPr F D Y₁ (s₁ ≫ p) hi₁ hs₁ hp₁ _ (ne_bot_of_notMem_local (off₂ z₁ hz₁))
  have iso₂ : IsIso (s₂ ∣_ (s₁ ⁻¹ᵁ U)) := hb₂.isIso_restrict _ off₂
  obtain ⟨z₂, hz₂⟩ : ∃ z : Y₂, z ∈ s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U) :=
    let z := inv (s₂ ∣_ (s₁ ⁻¹ᵁ U)) ⟨z₁, hz₁⟩
    ⟨z.1, z.2⟩
  let M₂ : Modif M₁.str M₁.opn D := ⟨Y₂, s₂, hs₂, hp₂, iso₂, (s₂ ⁻¹ᵁ (s₁ ⁻¹ᵁ U)).isOpen.dense ⟨z₂, hz₂⟩⟩
  have Δ₂ : Cartier ((baseIdeal (C.isLB a₂) W₂).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]; exact (nonempty_cartier_of_locally_principal_local _ _ hc₂).some
  have Δ₁ : Cartier ((baseIdeal (C.isLB a₁) W₁).comap (s₂ ≫ s₁)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact pullOfInt_local (nonempty_cartier_of_locally_principal_local _ _ hc₁).some s₂ (z₀ := z₂) (by
      rw [Scheme.IdealSheafData.support_comap]; exact h₁ _ hz₂)
  exact ⟨{ toModif := M₁.trans M₂, Δ₁ := Δ₁, Δ₂ := Δ₂ }⟩

theorem cls_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a : Λ) (n : ℕ) :
    cls (B (n • a)) (C.isLB _) = n • cls (B a) (C.isLB _) :=
  (AddMonoidHom.mk' (fun a => cls (B a) (C.isLB a)) (cls_common_add C)).map_nsmul n a

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem finrank_cusp_le (hQ : GlobalTheory.HSCore.Quoted) (hPr : GlobalTheory.Published.Principalisation) (hV : IsVariety₀ X Z) (hD : 1 ≤ dimFlag Dw)
    (hC : ∀ la, CuspIso X Z U la) {u la : AllWt.Weight Dw} (hF : FreeOnOpen X Z U u)
    (hB : GlobalTheory.DegVal.BirOn U Z (wtOf Dw u 0)) {n a : ℕ} {v : ℝ} (hv : 0 ≤ v)
    (hG : GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) = ENNReal.ofReal v)
    (hn : letI := algebraΓOfHom (str₀ X Z)
      IsNef c.F (L₀ X Z u) ∧ IsNef c.F (L₀ X Z la) ∧ IsNef c.F (L₀ X Z (n • u - la)))
    (h : n * v < (a + 1) * (GlobalTheory.CompHt.compDeg U Z (wtOf Dw u 0) : ℝ)) :
    Module.finrank c.F (Cusp Z U la) ≤ (a + dimFlag Dw).choose (dimFlag Dw) * GlobalTheory.CompHt.compDeg U Z (wtOf Dw u 0) := by
  letI := algebraΓOfHom (str₀ X Z)
  obtain ⟨hs, hp, hc⟩ := id hV
  have : ConnectedSpace (Y₀ X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ X Z)
  obtain ⟨R⟩ := nonempty_resol hPr hs hp hc (dense_U₀ X Z).nonempty (common₀ X Z) hF hF
  letI := algebraΓOfHom R.str
  have hc' := GlobalTheory.CompHS.Modif.geometricallyConnected_str _ _ _ _ _ R.toModif hs hc (dense_U₀ _ _)
  obtain ⟨_, hp', hd', h0, hpull⟩ := topSelf_pull hQ.nef hs hp hc hD R.toModif hc'
  obtain ⟨hgen, hdeg⟩ := topSelf_moving hQ R.toModif R.Δ₁ hV hD (hC u).1 hF hB
  have hne : ∃ f : Cusp Z U u, f ≠ 0 := by
    by_contra! h0
    exact hB.1 (LinearMap.ext fun f => by rw [h0 f, map_zero]; rfl)
  have htop := GlobalTheory.T.topSelfIntersection_nef_le_cuspFormGrowth hQ.nef E H Dw l Xo c Y X Z r U u hV hD hC hne hn.1
  rw [hG, ENNReal.ofReal_le_ofReal_iff hv, ← (hpull _ hn.1).2] at htop
  obtain ⟨d, hd⟩ : ∃ d, dimFlag Dw = d + 1 := ⟨dimFlag Dw - 1, by omega⟩
  have hP : HasNonzeroSec R.Δ₁.P := by
    obtain ⟨z, hz⟩ := R.dense.nonempty
    exact ⟨_, sec_ne_zero_of_mem ((R.Δ₁.mem_nonzeroLocus z).2 (R.notMem_support hF z (R.off_eq.ge hz)))⟩
  have hch := interNum_cons_le hQ.nef hp' (d := d) (hd ▸ hd'.le) (hpull _ hn.2.1).1 (hgen.isNef_of_isProjOver hp')
    (hpull _ hn.1).1 R.Δ₁.isLB (hpull _ hn.2.2).1 n hP
    (by rw [cls_div (hpull _ hn.1).1.isLB R.Δ₁.isLB, sub_add_cancel])
    ((cls_nsmul R.com u n).symm.trans ((congrArg (fun a => cls (R.pb a) (R.com.isLB a)) (add_sub_cancel la (n • u)).symm).trans
      (cls_common_add R.com _ _)))
  have key := globalSections_dim_le_of_intersection_bound hQ.nef (dimFlag Dw) c.F R.X hp' hd'.le hgen a (hpull _ hn.2.1).1.isLB fun e he => by
    obtain rfl : d = e := by omega
    rw [hdeg]
    rw [congrArg (topSelfIntersection c.F _) hd.symm] at hch
    have h₁ : ((interNum c.F (structureModule R.X) (Fin.cons (R.pb la) (fun _ : Fin d => R.Δ₁.moving) : Fin (d + 1) → LB R.X) : ℤ) : ℝ) ≤
      n * (topSelfIntersection c.F (R.pb u) (dimFlag Dw) : ℝ) := by exact_mod_cast hch
    have h₂ := h₁.trans_lt ((mul_le_mul_of_nonneg_left htop n.cast_nonneg).trans_lt h)
    exact_mod_cast h₂
  rw [hdeg, h0 _ (isLB_L₀ X Z la), ← H0.finrank_top] at key
  have := finite_top hp (isLB_L₀ X Z la)
  have h₃ := (hC la).1.equiv.finrank_eq.trans_le (space X Z U la).finrank_le
  exact h₃.trans (by exact_mod_cast key)

end Comp

theorem gapGe_zero_of_antitone {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {la : AllWt.Weight Dw} (h : ∀ τ, Antitone (la τ)) : GapGe 0 la := fun τ k hk => by
  rw [gap, dite_eq_left hk, sub_nonneg]
  exact h τ (Fin.mk_le_mk.2 k.le_succ)

end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

end

end GlobalTheory.JetRank

end
