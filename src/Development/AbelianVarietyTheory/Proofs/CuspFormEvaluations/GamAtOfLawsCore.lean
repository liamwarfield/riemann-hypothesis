module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGroupShiftHalfTorsionRoot
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExistsBorelOrthonormalMove
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore : ∀ (D : D7) (T : Core D), LawsCore T → GamAt T := by
  intro D T h j hj σ hσ k γ h1 h2
  exact GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T h j hj σ hσ k γ h1 h2

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_iff_modN (k : ℕ) (x : Dw.La) :
    x ∈ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) ↔ Dw.ModN k x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨b, _, hb⟩ => ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩,
    fun ⟨b, hb⟩ => ⟨b, trivial, by rw [hb, Nat.cast_smul_eq_nsmul]⟩⟩

theorem mk_eq_iff (k : ℕ) (a b : Dw.La) :
    (Submodule.Quotient.mk a : LatMod Dw k) = Submodule.Quotient.mk b ↔ Dw.ModN k (a - b) := by
  rw [Submodule.Quotient.eq, mem_iff_modN]

theorem finite_latMod (k : ℕ) (hk : 0 < k) : Finite (LatMod Dw k) := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw k hk
  refine Finite.of_surjective (fun j => (Submodule.Quotient.mk (r j) : LatMod Dw k)) fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨π a, (mk_eq_iff k _ _).2 ((hπ _ _).1 (hr _))⟩

theorem nsmul_latMod (k : ℕ) (q : LatMod Dw k) : k • q = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_iff_modN]
  exact ⟨a, Nat.cast_smul_eq_nsmul _ _ _⟩

variable (Xo : Moduli Dw l)

theorem exists_descend (k : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (ev : Dw.La → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hadd : ∀ a b, ev (a + b) = ev a * ev b)
    (hlin : ∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) (hker : ∀ a, ev (k • a) = 1)
    (hinj : ∀ (K : Type) [Field K] (χ : S →+* K) (a b : Dw.La),
      spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → Dw.ModN k (a - b)) :
    ∃ ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G), IsFullLev Xo k x0 ev' ∧
      ∀ a, ev' (Submodule.Quotient.mk a) = ev a := by
  choose r hr using Submodule.Quotient.mk_surjective (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La)
  have h : ∀ a, ev (r (Submodule.Quotient.mk a)) = ev a := fun a => by
    obtain ⟨b, hb⟩ := (mk_eq_iff k _ _).1 (hr (Submodule.Quotient.mk a))
    rw [sub_eq_iff_eq_add.1 hb, hadd, hker, _root_.one_mul]
  refine ⟨fun q => ev (r q), ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => ?_⟩, h⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    beta_reduce
    rw [← Submodule.Quotient.mk_add, h, h, h, hadd]
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    beta_reduce
    rw [← Submodule.Quotient.mk_smul, h, h, hlin]
  · rw [← hr a, ← hr b]
    exact (mk_eq_iff k _ _).2 (hinj K χ _ _ hab)

theorem pow_eq_one {k : ℕ} {S : Type} [CommRing S] {x0 : Sp S ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (h : IsFullLev Xo k x0 ev) (q : LatMod Dw k) : ev q ^ k = 1 := by
  let f : LatMod Dw k →+ Additive (ptO Xo x0 ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (h.1 a b)
  have := map_nsmul f k q
  rw [nsmul_latMod, map_zero] at this
  exact (congrArg Additive.toMul this).symm

theorem baseChange {k : ℕ} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x0 : Sp S ⟶ Xo.X}
    {x1 : Sp T ⟶ Xo.X} (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ)
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) :
    IsFullLev Xo k x1 (fun q => h ≫ ev q) := by
  refine ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => hev.2.2 K (χ.comp ψ) a b ?_⟩
  · beta_reduce
    rw [hev.1, MonObj.comp_mul]
  · beta_reduce
    rw [hev.2.1, Category.assoc]
  · have : spMap χ ≫ h.left ≫ (ev a).left = spMap χ ≫ h.left ≫ (ev b).left := hab
    rw [hh] at this
    rw [spMap_comp, Category.assoc, Category.assoc]
    exact this

theorem eq_of_agree (hL : Laws) {k : ℕ} (hk : 0 < k) {S T : Type} [CommRing S] [CommRing T] (χ : S →+* T)
    (hχ : ∀ e, χ e = 1 → IsUnit e) {x0 : Sp S ⟶ Xo.X} {a b : ptO Xo x0 ⟶ Xo.univ.t.G} (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hab : spMap χ ≫ a.left = spMap χ ≫ b.left) : a = b := by
  obtain ⟨e, he, He⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo S x0 k hk a b ha hb
  have h1 : e = 1 := (hχ e ((He T χ).2 hab)).mul_left_cancel (he.eq.trans (_root_.mul_one _).symm)
  have h2 := (He S (RingHom.id S)).1 h1
  have h3 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id (CommRingCat.of S)
  rw [h3] at h2
  exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans (h2.trans (Category.id_comp _)))

theorem exists_geometric (hL : Laws) {k : ℕ} (hk : 0 < k) (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X) :
    ∃ ev, IsFullLev Xo k x0 ev ∧ ∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x0 ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x0 β.hom hβ.symm
  obtain ⟨ev, hev, h⟩ := exists_descend Xo k x0 (I.ev k) (I.add k) (I.lin k) (fun a => (I.ker k hk _).2 ⟨a, rfl⟩)
    fun K' _ χ a b hab => by
      have h1 : I.ev k a = I.ev k b :=
        eq_of_agree Xo hL hk χ (fun e he => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at he)
          ((I.onto k hk _).2 ⟨_, rfl⟩) ((I.onto k hk _).2 ⟨_, rfl⟩) hab
      have h2 : I.ev k a = I.ev k (a - b) * I.ev k b := by rw [← I.add, sub_add_cancel]
      rw [h2, mul_eq_right, I.ker k hk] at h1
      exact h1
  refine ⟨ev, hev, fun p hp => ?_⟩
  obtain ⟨a, ha⟩ := (I.onto k hk p).1 hp
  exact ⟨_, (h a).trans ha⟩

theorem onto_of_local (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (p : ptO Xo x0 ⟶ Xo.univ.t.G)
    (hp : p ^ k = 1) : ∃ q, ev q = p := by
  haveI := finite_latMod (Dw := Dw) k hk
  let K := AlgebraicClosure (IsLocalRing.ResidueField T)
  let χ : T →+* K := (algebraMap (IsLocalRing.ResidueField T) K).comp (IsLocalRing.residue T)
  have hχ : ∀ e, χ e = 1 → IsUnit e := fun e he => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    simp [χ, h0] at he
  let h : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  obtain ⟨ev₀, -, h₀⟩ := exists_geometric Xo hL hk K (spMap χ ≫ x0)
  have hpow : ∀ a : ptO Xo x0 ⟶ Xo.univ.t.G, a ^ k = 1 → (h ≫ a) ^ k = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  choose f hf using fun q => h₀ (h ≫ ev q) (hpow _ (pow_eq_one Xo hev q))
  have hinj : Function.Injective f := fun a b hab => hev.2.2 K χ a b
    (congrArg CommaMorphism.left ((hf a).symm.trans ((congrArg ev₀ hab).trans (hf b))))
  obtain ⟨r, hr⟩ := h₀ (h ≫ p) (hpow p hp)
  obtain ⟨q, rfl⟩ := Finite.surjective_of_injective hinj r
  exact ⟨q, eq_of_agree Xo hL hk χ hχ (pow_eq_one Xo hev q) hp
    (congrArg CommaMorphism.left ((hf q).symm.trans hr))⟩

theorem injective_of_local {k : ℕ} {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) : Function.Injective ev :=
  fun a b hab => hev.2.2 _ (IsLocalRing.residue T) a b (by rw [hab])

theorem exists_levGrp (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (hev' : IsFullLev Xo k x0 ev') :
    ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q) := by
  haveI := finite_latMod (Dw := Dw) k hk
  choose f hf using fun q => onto_of_local Xo hL hk hev (ev' q) (pow_eq_one Xo hev' q)
  have hi := injective_of_local Xo hev
  let g : LatMod Dw k →ₗ[𝓞 E] LatMod Dw k :=
    { toFun := f
      map_add' := fun a b => hi (by rw [hev.1, hf, hf, hf, hev'.1])
      map_smul' := fun o a => hi (by rw [RingHom.id_apply, hev.2.1, hf, hf, hev'.2.1]) }
  have hg : Function.Injective g := fun a b hab => injective_of_local Xo hev'
    ((hf a).symm.trans ((congrArg ev hab).trans (hf b)))
  exact ⟨LinearEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, fun q => (hf q).symm⟩

end FullLevel


open FullLevel in
theorem fullLevel_cover_baseChange_torsor :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : ℕ), 0 < k → (∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X), ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : LatMod Dw k → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ IsFullLev Xo k (spMap φ ≫ x0) ev) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ ev, IsFullLev Xo k x0 ev → IsFullLev Xo k x1 (fun q => h ≫ ev q) ∧ ∀ q, ev q ^ k = 1) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)), IsFullLev Xo k x0 ev → (∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p) ∧ ∀ ev', IsFullLev Xo k x0 ev' → ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X), ∃ ev, IsFullLev Xo k x0 ev := by
  intro hL E _ _ _ H Dw l Xo k hk
  refine ⟨fun S _ x0 => ?_, fun S T _ _ ψ x0 x1 h hh ev hev => ⟨FullLevel.baseChange Xo ψ h hh hev, FullLevel.pow_eq_one Xo hev⟩,
    fun T _ _ x0 ev hev => ⟨FullLevel.onto_of_local Xo hL hk hev, fun ev' hev' => FullLevel.exists_levGrp Xo hL hk hev hev'⟩,
    fun K _ _ x0 => (FullLevel.exists_geometric Xo hL hk K x0).imp fun _ h => h.1⟩
  obtain ⟨B, _, φ, ev, hφ, h1, h2, h3, h4⟩ := exists_faithfullyFlat_linear_level hL E H Dw l Xo S x0 k hk
  obtain ⟨ev', hev', -⟩ := FullLevel.exists_descend Xo k (spMap φ ≫ x0) ev h1 h2 h3 h4
  exact ⟨B, inferInstance, φ, ev', hφ, hev'⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLinearLevel_cover_baseChange_torsor : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : ℕ), 0 < k → (∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X), ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : LatMod Dw k → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ IsFullLev Xo k (spMap φ ≫ x0) ev) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ ev, IsFullLev Xo k x0 ev → IsFullLev Xo k x1 (fun q => h ≫ ev q) ∧ ∀ q, ev q ^ k = 1) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)), IsFullLev Xo k x0 ev → (∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p) ∧ ∀ ev', IsFullLev Xo k x0 ev' → ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X), ∃ ev, IsFullLev Xo k x0 ev := by
  first | exact @GlobalTheory.fullLevel_cover_baseChange_torsor | exact GlobalTheory.fullLevel_cover_baseChange_torsor | (intros; apply GlobalTheory.fullLevel_cover_baseChange_torsor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
section -- merged from Development.AbelianVarietyTheory.Definitions.ThetaValues.PowEqOneOfIsFullLev
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem exists_isNullVal (hL : Laws) {N : ℕ} (hN : Odd N) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (hp : p ^ (N ^ 2) = 1) : ∃ w, IsNullVal Xo c N y p w := by
  obtain ⟨F, hF⟩ := (GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver hL E H Dw l Xo N hN _ y.s).1
    (fun t => t = p) (p ^ N) p rfl hp rfl
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_value _ _ Xo.univ.t.PP.isLB ((N : ℤ) ^ 2) F 1
    (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (ptO Xo y.x) ((N : ℤ) ^ 2)) (GlobalTheory.ThetaReal.NormMul.rigT_isGen Xo.univ.t.PP.rigGen _)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom v, F, hF, ?_⟩
  have : toΓ S ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom v) = v := by
    unfold toΓ
    exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply v
  rw [this]
  exact hv

open GlobalTheory.TranslExist in
theorem isNullVal_unique (hL : Laws) {N : ℕ} (hN : Odd N) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (hp : p ^ (N ^ 2) = 1) {w w' : S} (h : IsNullVal Xo c N y p w)
    (h' : IsNullVal Xo c N y p w') : w = w' := by
  have hB := Xo.univ.t.PP.isLB
  obtain ⟨F, ⟨_, α₀, α, s₁, U, -, rfl, g₀, n₀, cα, tw, hU, a₁⟩, hv⟩ := h
  obtain ⟨F', ⟨_, β₀, β, r₁, V, -, rfl, gβ, nβ, cβ, tw', hV, b₁⟩, hv'⟩ := h'
  obtain ⟨g₁, -, -, u₀, -⟩ := GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hL E H Dw l Xo N
  obtain rfl : r₁ = s₁ := twist_congr hB (fun z J hJ =>
    (val_corr hJ cβ _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (u₀ β₀ gβ nβ) _).trans
      ((val_corr hJ cα _).trans ((val_pull hJ _ _ _).trans (val_corr hJ (u₀ α₀ g₀ n₀) _))).symm))) tw' tw
  obtain rfl : F = F' := act_congr hB (hU.pt_eq.trans hV.pt_eq.symm)
    ((GlobalTheory.T.universal_symLift_exists_unique_global hL E H Dw l Xo N hN _ _ hp).2 _ _ hU hV) a₁ b₁
  exact Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.toΓ_injective _ (Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.value_unique _ _ hB _ _ _ _ _ _ hv hv')

end GlobalTheory.EtaForm.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NullValue

section Val

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem isValueAt_congr {T : Over X} {s : LB.Sec (LPow A L a T)} {z z' : T ⟶ A} (e : z = z')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))}
    {τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z'.left) (fun _ => a))}
    (hτ : ∀ (j : Fin 1 → L.ι) (y : T.left), y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      y ∈ LB.wchart L (fun _ : Fin 1 => z'.left) j → gm (𝟙 _) y _ (τ.s j) = gm (𝟙 _) y _ (τ'.s j))
    {v : Γ(T.left, ⊤)} (h : IsValueAt A L a s z τ v) : IsValueAt A L a s z' τ' v := by
  subst e
  have hU : ∀ j, (τ.s j).val = (τ'.s j).val := by
    intro j
    apply TopCat.Presheaf.section_ext T.left.sheaf
    intro y hy
    have hyU : (𝟙 T.left : T.left ⟶ T.left) y ∈ (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := hy
    have key := hτ j y hy hy
    clear hτ h
    unfold gm at key
    rw [dite_eq_left hyU] at key
    have key2 := congrArg Units.val key
    simp only [MonoidHom.comp_apply] at key2
    unfold pullU at key2
    simp only [Units.coe_map, MonoidHom.coe_coe] at key2
    exact key2
  unfold IsValueAt at h ⊢
  intro j
  rw [← hU j]
  exact h j

private lemma gm_id_eq_germ_map {Y : Scheme.{0}} {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V)
    (x : Γ(Y, U)ˣ) :
    ((gm (𝟙 Y) y U x : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) =
      Y.presheaf.germ V y hy ((Y.presheaf.map (homOfLE hVU).op).hom (x : Γ(Y, U))) := by
  unfold gm
  rw [dite_eq_left (show (𝟙 Y : Y ⟶ Y) y ∈ U from hVU hy)]
  simp only [MonoidHom.comp_apply]
  unfold pullU
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [Y.presheaf.germ_res_apply]
  rfl

private lemma gm_id_eq_of_units_map_eq {Y : Scheme.{0}} {U₁ U₂ V : Y.Opens} (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (x₁ : Γ(Y, U₁)ˣ)
    (x₂ : Γ(Y, U₂)ˣ) (y : Y) (hy : y ∈ V)
    (e : Units.map ((Y.presheaf.map (homOfLE h₁).op).hom : Γ(Y, U₁) →* Γ(Y, V)) x₁ =
      Units.map ((Y.presheaf.map (homOfLE h₂).op).hom : Γ(Y, U₂) →* Γ(Y, V)) x₂) :
    gm (𝟙 Y) y U₁ x₁ = gm (𝟙 Y) y U₂ x₂ := by
  apply Units.ext
  rw [gm_id_eq_germ_map h₁ y hy, gm_id_eq_germ_map h₂ y hy]
  have e2 := congrArg Units.val e
  simp only [Units.coe_map, MonoidHom.coe_coe] at e2
  rw [e2]

theorem isValueAt_one_pull (ρ : LB.Gen (L.pull (eSec A))) {T T' : Over X} (g : T' ⟶ T)
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s') {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s 1 (rigT A L ρ T a) v) :
    IsValueAt A L a s' 1 (rigT A L ρ T' a) (g.left.appTop.hom v) := by
  have h1 := Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isValueAt_pull A L a g 1 hs hv
  have hc := Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.corr_rigT_pull A L ρ g a
  have e : g ≫ (1 : T ⟶ A) = 1 := by simp
  refine isValueAt_congr A L a e ?_ h1
  intro j y hy hy'
  unfold LB.Gen.Corr at hc
  have key := hc j j (fun k₁ k₂ _ => by rw [Subsingleton.elim k₁ k₂])
    (fun k₁ k₂ _ => by rw [Subsingleton.elim k₁ k₂]) (fun k k' _ => by rw [Subsingleton.elim k k'])
  unfold res at key
  refine gm_id_eq_of_units_map_eq _ _ _ _ y ?_ key
  exact ⟨hy, hy'⟩

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem baseChange {N : ℕ} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G) (hp : p'.left = spMap ψ.toRingHom ≫ p.left)
    {w : S} (hw : IsNullVal Xo c N y p w) : IsNullVal Xo c N z p' (ψ w) := by
  obtain ⟨F, hVt, hV⟩ := hw
  have hx : spMap ψ.toRingHom ≫ y.x = z.x := by
    unfold FrMap at hm
    exact hm.1.symm
  let g : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx
  have hg : g.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm g hg
  have hF := GlobalTheory.VVRank.isPullSec_pullS (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) ((N : ℤ) ^ 2) g F
  have hpg : p' = g ≫ p := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hg]
    exact hp
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  unfold IsNullVal
  refine ⟨GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) g F, ?_, ?_⟩
  · unfold IsVtOver at hVt ⊢
    obtain ⟨t', α₀, α, s₁, U, ht', hok, g₀, hnm, cα, tw, hsym, hact⟩ := hVt
    have hok' : t' = p := hok
    obtain ⟨α', cα', tw'⟩ := GlobalTheory.VtBaseChange.exists_mulTwist Xo.univ.t.G hL N g hs g₀ cα tw
    obtain ⟨θ', -, -, hsymP, hactP⟩ :=
      GlobalTheory.ThetaPullback.exists_thetaGrp_pullback _ Xo.univ.t.G Xo.univ.t.PP.L hL ((N : ℤ) ^ 2) _ _ g U
    refine ⟨g ≫ t', α₀, α', _, θ', ?_, ?_, g₀, hnm, cα', tw', hsymP _ _ hsym,
      hactP _ _ _ _ hact (GlobalTheory.VVRank.isPullSec_pullS (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) _ g s₁) hF⟩
    · rw [hpg, hok']
    · show g ≫ t' = p'
      rw [hpg, hok']
  · have h1 := isValueAt_one_pull Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Xo.univ.t.PP.rig g hF hV
    have e2 : g.left.appTop.hom (toΓ S w) = toΓ T (ψ w) := GlobalTheory.NabLinear.appTop_toΓ ψ.toRingHom w
    rw [e2] at h1
    exact h1


open GlobalTheory.ThetaValueWeight in
theorem triangular {N : ℕ} {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} {t : Ix Dw → Sˣ}
    (hb : FrBor t y y') (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G) (hp : p'.left = p.left)
    {w : S} (hw : IsNullVal Xo c N y p w) : IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  have hxx : y'.x = y.x := by
    unfold FrBor at hb
    exact hb.1
  obtain ⟨d, rfl⟩ := GlobalTheory.ThetaValueWeight.exists_reframe y y' hxx
  have hpp : p' = p := Over.OverMorphism.ext hp
  subst hpp
  obtain ⟨F, hVt, hV⟩ := hw
  have hgen := fun i => GlobalTheory.ThetaValueWeight.gen_eq d hb i
  unfold IsNullVal
  refine ⟨scaleSec Xo.univ.t.G (toΓ S (t none : S)) F, ?_, ?_⟩
  · exact isVtOver_scale Xo.univ.t.G Xo.univ.t.PP (T := ptO Xo y.x) (s := y.s) (s₀ := d.s)
      (toΓ S (t none : S)) (fun j => hgen j) hVt
  · have h1 := GlobalTheory.NabLinear.isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (𝟙 (ptO Xo y.x))
      (F := F) (F' := scaleSec Xo.univ.t.G (toΓ S (t none : S)) F) (r := toΓ S (t none : S)) (fun _ => rfl)
      (isPullSec_id Xo.univ.t.G F) (isPullSec_id Xo.univ.t.G _) hV
    convert h1 using 1
    rw [map_mul]
    rfl

end GlobalTheory.NullValue

namespace GlobalTheory

theorem nullValue_existsUnique_natural_linear : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (N : ℕ), Odd N → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (p : ptO Xo y.x ⟶ Xo.univ.t.G), p ^ (N ^ 2) = 1 → ∃! w, IsNullVal Xo c N y p w) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap ψ y z → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G), p'.left = spMap ψ.toRingHom ≫ p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N z p' (ψ w)) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G), p'.left = p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  intro hL E _ _ _ H Dw l Xo c N hN
  refine ⟨?_, ?_, ?_⟩
  · intro S _ _ y p hp
    obtain ⟨w, hw⟩ := GlobalTheory.EtaForm.Model.exists_isNullVal Xo c hL hN y p hp
    exact ⟨w, hw, fun w' hw' => GlobalTheory.EtaForm.Model.isNullVal_unique Xo c hL hN y p hp hw' hw⟩
  · intro S T _ _ _ _ ψ y z hm p p' hp w hw
    exact NullValue.baseChange ψ hm p p' hp hw
  · intro S _ _ y y' t hb p p' hp w hw
    exact NullValue.triangular hb p p' hp hw

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinearStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNullValue_existsUnique_natural_linear : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (N : ℕ), Odd N → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (p : ptO Xo y.x ⟶ Xo.univ.t.G), p ^ (N ^ 2) = 1 → ∃! w, IsNullVal Xo c N y p w) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap ψ y z → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G), p'.left = spMap ψ.toRingHom ≫ p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N z p' (ψ w)) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G), p'.left = p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  first | exact @GlobalTheory.nullValue_existsUnique_natural_linear | exact GlobalTheory.nullValue_existsUnique_natural_linear | (intros; apply GlobalTheory.nullValue_existsUnique_natural_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PrincipalDatumFgPerfectTracePairing
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PrincipalDatumFgPerfectTracePairing
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem cc_eq_host_conj (D : D7) (x : D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

theorem principalDatum_trace_perfect : ∀ D : D7, ∃ AA : Submodule (𝓞 D.host.E) D.host.E,
    AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * ReciprocityTheory.ChartRestriction.G.FD.cc b) = z) ↔
        IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hA := AA_ne_zero hP D
  have hone : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  refine ⟨(D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ?_, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  · intro h0
    exact hA (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  · have h1 : ∀ w ∈ D.host.AA * D.host.AAbar, ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z := by
      intro w hw
      refine FractionalIdeal.mul_induction_on (C := fun w => ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z) hw
        (fun a ha b hb c => ?_) (fun u v hu hv c => ?_)
      · obtain ⟨z, hz⟩ := h (c • a) (Submodule.smul_mem _ c ha) (D.host.conj b) (conj_mem_AA D hb)
        refine ⟨z, ?_⟩
        rw [cc_eq_host_conj, conj_conj] at hz
        rw [← hz, ← smul_mul_assoc, mul_assoc (D.host.xi0 * x)]
      · obtain ⟨z, hz⟩ := hu c
        obtain ⟨z', hz'⟩ := hv c
        refine ⟨z + z', ?_⟩
        rw [smul_add, mul_add, map_add (f := _), hz, hz', Int.cast_add]
    have h2 : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.dual ℤ ℚ
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) := by
      rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ hone)]
      intro a ha
      rw [← dual_eq hP D, mul_assoc, FractionalIdeal.mem_singleton_mul] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨z, hz⟩ := h1 w hw 1
      rw [one_smul] at hz
      refine ⟨z, ?_⟩
      rw [Algebra.traceForm_apply, ← mul_assoc, mul_comm x, hz]
      exact eq_intCast _ _
    rw [FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff] at h2
    obtain ⟨c, rfl⟩ := h2
    exact c.isIntegral_coe
  · intro a ha b hb
    have hm : (⟨x, h⟩ : 𝓞 D.host.E) • (a * D.host.conj b) ∈ NAA D :=
      Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
    obtain ⟨z, hz⟩ := trace_int_of_mem hP D hm
    refine ⟨z, ?_⟩
    rw [← hz, cc_eq_host_conj, Algebra.smul_def]
    congr 1
    change _ = D.host.xi0 * (x * (a * D.host.conj b))
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PrincipalDatumFgPerfectTracePairingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalDatum_fg_perfect_tracePairing : ∀ D : D7, ∃ AA : Submodule (𝓞 D.host.E) D.host.E, AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * ReciprocityTheory.ChartRestriction.G.FD.cc b) = z) ↔ IsIntegral ℤ x := by
  first | exact @GlobalTheory.principalDatum_trace_perfect | exact GlobalTheory.principalDatum_trace_perfect | (intros; apply GlobalTheory.principalDatum_trace_perfect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatSplitIsotropicGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatSplitIsotropicGroup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem map_sum_eq_prod_ofFn_of_add_eq_mul {A G : Type} [AddCommGroup A] [Group G] (ev : A → G)
    (h : ∀ a b, ev (a + b) = ev a * ev b) :
    ∀ (n : ℕ) (f : Fin n → A), ev (∑ j, f j) = (List.ofFn fun j => ev (f j)).prod := by
  have h0 : ev 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.mp this
  intro n
  induction n with
  | zero => intro f; simp [h0]
  | succ n ih => intro f; rw [Fin.sum_univ_succ, h, ih, List.ofFn_succ, List.prod_cons]

theorem map_nsmul_eq_pow_of_add_eq_mul {A G : Type} [AddCommGroup A] [Group G] (ev : A → G)
    (h : ∀ a b, ev (a + b) = ev a * ev b) (a : A) (k : ℕ) : ev (k • a) = ev a ^ k := by
  induction k with
  | zero =>
    have := h 0 0
    rw [add_zero] at this
    simpa using left_eq_mul.mp this
  | succ k ih => rw [succ_nsmul, h, ih, pow_succ]

theorem exists_faithfullyFlat_split_Zh : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z := by
  intro hL E _ _ _ H Dw l Xo S _ x0 n Λ N hU hN hle
  obtain ⟨B, iB, φ, ev, hff, hadd, hsm, hk, hinj⟩ :=
    GlobalTheory.T.exists_faithfullyFlat_full_linear_level_structure hL E H Dw l Xo S x0 (N ^ 2) (pow_pos hN 2)
  obtain ⟨zz, hz, hzi, -⟩ := GlobalTheory.T.exists_isotropic_group_lattice_class_representatives E H Dw n Λ N hU hN hle
  refine ⟨B, iB, φ, fun i b => ev (zz i b), hff, fun i => ⟨fun b => ?_, ?_⟩, ?_⟩
  · rw [← map_nsmul_eq_pow_of_add_eq_mul ev hadd, hk]
  · intro mu hmu cm hcm i'
    have h1 := hz i mu hmu cm hcm i'
    simp only [← hsm]
    rw [← map_sum_eq_prod_ofFn_of_add_eq_mul ev hadd]
    obtain ⟨y, hy⟩ := h1
    rw [hy]
    exact hk y
  · intro k _ ψ g hg i i' hii
    apply hzi
    intro b
    apply hinj k ψ
    have := congrArg (fun f => f.left) (congrFun hii b)
    simp only [Over.comp_left, hg] at this
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatSplitIsotropicGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_split_isotropicGroup : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z := by
  first | exact @GlobalTheory.exists_faithfullyFlat_split_Zh | exact GlobalTheory.exists_faithfullyFlat_split_Zh | (intros; apply GlobalTheory.exists_faithfullyFlat_split_Zh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem shortSum_toΓ_injective (S : Type) [CommRing S] : Function.Injective (toΓ S) := by
  intro a b h
  have hinv : ∀ x : S, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (toΓ S x) = x := by
    intro x
    unfold toΓ
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hinv a, ← hinv b, h]

private theorem eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one {M : Type*} [CommMonoid M] (x : M) (N : ℕ) (hN : Odd N)
    (h2 : x ^ 2 = 1) (hN2 : x ^ (N ^ 2) = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hN.pow (n := 2)
  rw [hk, pow_succ, pow_mul, h2, one_pow, _root_.one_mul] at hN2
  exact hN2


set_option maxHeartbeats 1000000 in
theorem shortSum_indep_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  intro hL E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hTr hLev P T _ _ _ y z1 tp1 F1 z2 tp2 F2 hz1 hg1 htp1 hF1 hz2 hg2 htp2 hF2 q
  obtain ⟨hNodd, hMN, hNL⟩ := hLev
  have hN0 : 0 < N := hNodd.pos
  have hLa : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hNL.trans inf_le_left
  have hsurj := (GlobalTheory.T.isotropic_enumeration_surjective_local_ring hL E H Dw l Xo T y.x n Λ N hU hN0 hLa z1 hz1 hg1).1
  have h58 := GlobalTheory.T.torsion_isotropic_commutator_pairing hL E H Dw l Xo T y.x n Λ N hU hN0 hLa
  have h56 := GlobalTheory.T.inZh_geoInj_stable_alt E H Dw l Xo n Λ N
  have h57 := (GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN0).2.1

  have hz2inj : Function.Injective z2 := by
    intro i i' h
    let g : ptO Xo (spMap (IsLocalRing.residue T) ≫ y.x) ⟶ ptO Xo y.x :=
      Over.homMk (spMap (IsLocalRing.residue T)) rfl
    exact hg2 (IsLocalRing.ResidueField T) (IsLocalRing.residue T) g rfl
      (congrArg (fun (w : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (b : Fin n) => g ≫ w b) h)

  obtain ⟨u, hu⟩ : ∃ u : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G), ∀ b, u b = (tp1 q b)⁻¹ * tp2 q b :=
    ⟨_, fun _ => rfl⟩
  have htp : ∀ b, tp2 q b = tp1 q b * u b := fun b => by
    rw [hu, mul_inv_cancel_left]
  have hlev : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
    intro a
    obtain ⟨k, hk⟩ := hMN
    unfold levPt
    rw [← MonObj.comp_pow, hk, pow_mul, (GlobalTheory.moduli_univ_eta_killed hL E H Dw l Xo a).2.2, one_pow,
      MonObj.comp_one]
  have hu1 : ∀ b, u b ^ N = 1 := fun b => by
    rw [hu, mul_pow, inv_pow, (htp1 q b).1, (htp2 q b).1, inv_mul_cancel]
  have hsq : ∀ x : ptO Xo y.x ⟶ Xo.univ.t.G, x ^ N = 1 → x ^ (N ^ 2) = 1 := fun x hx => by
    rw [sq, pow_mul, hx, one_pow]
  have ht2 : ∀ b, tp1 q b ^ (N ^ 2) = 1 := fun b => by
    rw [sq, pow_mul, (htp1 q b).1, hlev]
  have hkill : ∀ b, ∃ j, KilledBy Xo (l.Mb ^ j) (tp1 q b) ∧ KilledBy Xo (l.Mb ^ j) (u b) := by
    intro b
    obtain ⟨j1, hj1⟩ := (htp1 q b).2
    obtain ⟨j2, hj2⟩ := (htp2 q b).2
    have mono : ∀ {i j : ℕ} (t : ptO Xo y.x ⟶ Xo.univ.t.G), i ≤ j →
        KilledBy Xo (l.Mb ^ i) t → KilledBy Xo (l.Mb ^ j) t :=
      fun t hij ht a ha => ht a (Ideal.pow_le_pow_right hij ha)
    refine ⟨max j1 j2, mono _ (le_max_left _ _) hj1, ?_⟩
    intro a ha
    have := Xo.univ.t.act.hom a
    have k1 := mono _ (le_max_left _ _) hj1 a ha
    have k2 := mono _ (le_max_right _ _) hj2 a ha
    have h1 : ((tp1 q b)⁻¹ ≫ Xo.univ.t.act.act a) * (tp1 q b ≫ Xo.univ.t.act.act a) = 1 := by
      rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
    rw [k1, _root_.mul_one] at h1
    rw [hu, MonObj.mul_comp, h1, k2, _root_.one_mul]
  have hInU : InZh Xo Λ N u := h56.2.2.2 hTr (ptO Xo y.x) u (fun b => by
    obtain ⟨j, -, hj⟩ := hkill b
    exact ⟨hu1 b, j, hj⟩)

  have hw : ∀ i, ∃ j, z1 j = fun b => u b * z2 i b := fun i =>
    hsurj _ (h56.2.1 _ u (z2 i) hInU (hz2 i))
  choose ρ hρ using hw
  have hρinj : Function.Injective ρ := by
    intro i i' h
    apply hz2inj
    funext b
    have hii := (hρ i).symm.trans ((congrArg z1 h).trans (hρ i'))
    exact mul_left_cancel (show u b * z2 i b = u b * z2 i' b from congrFun hii b)
  have hρbij : Function.Bijective ρ := Finite.injective_iff_bijective.mp hρinj

  have key : ∀ i, (∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) (colOf m b) := by
    intro i
    have he : ∀ b, ∃ e : Γ((ptO Xo y.x).left, ⊤)ˣ,
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (u b) (z2 i b) e := fun b =>
      (h57 (ptO Xo y.x) (u b) (z2 i b) (hsq _ (hu1 b)) ((hz2 i).1 b)).imp fun _ h => h.1
    choose e he using he
    have hpe : ∏ b, e b = 1 := h58.1 u (z2 i) e hInU (hz2 i) he
    have hr : ∀ b, ∃ r : T, (toΓ T r) ^ 2 = ((e b : Γ((ptO Xo y.x).left, ⊤))) ∧ r ^ (N ^ 2) = 1 ∧
        ∀ α, nab y ((N : ℤ) ^ 2) (F2 q i b) α = r * nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) α := by
      intro b
      obtain ⟨j, hj1, hj2⟩ := hkill b
      have hW1 := h58.2 (tp1 q b) (u b) j (ht2 b) (hsq _ (hu1 b)) hj1 hj2
      have hA : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp1 q b * u b) (F2 q i b) := by
        rw [← htp b]
        exact hF2 q i b
      have hB : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (u b * z2 i b) (tp1 q b) (F1 q (ρ i) b) := by
        have h1 := hF1 q (ρ i) b
        rw [hρ i] at h1
        exact h1
      obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.thetaGroup_shift_halfTorsion_root hL E H Dw l Xo T y.x N hNodd y.s (tp1 q b) (u b) (z2 i b)
        (e b) (ht2 b) (hsq _ (hu1 b)) ((hz2 i).1 b) hW1 (he b) _ _ hA hB
      exact ⟨r, hr1, hr2, GlobalTheory.T.connection_linear_in_section E H Dw l Xo c nab hnab T y N _ _ r hr3⟩
    choose r hr using hr
    have hprod : ∏ b, r b = 1 := by
      apply eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one _ N hNodd
      · apply shortSum_toΓ_injective T
        rw [map_one, map_pow, map_prod, ← Finset.prod_pow,
          Finset.prod_congr rfl (fun b _ => (hr b).1), ← Units.coe_prod, hpe, Units.val_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_eq_one (fun b _ => (hr b).2.1)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    rw [Finset.prod_congr rfl (fun b _ => (hr b).2.2 (colOf m b)), Finset.prod_mul_distrib, hprod, _root_.one_mul]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  exact (hρbij.sum_comp (fun j => ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
    ∏ b, nab y ((N : ℤ) ^ 2) (F1 q j b) (colOf m b))).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicSum_independent_of_choices_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  first | exact @GlobalTheory.shortSum_indep_local | exact GlobalTheory.shortSum_indep_local | (intros; apply GlobalTheory.shortSum_indep_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueCanonicalConnectionEqPolyDeriv
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdColumnFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdColumnFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

open scoped ContDiff

theorem filter_col_toMultiset {T : Type} [Fintype T] {r : T → ℕ} {n : ℕ}
    (m : Formalism.L2.Pj.Letter T r n →₀ ℕ) (b : Fin n) :
    (Finsupp.toMultiset m).filter (fun ℓ => ℓ.2.2 = b) =
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩)).map
        (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
  classical
  have hinj : Function.Injective
      (fun ℓ : (Σ τ : T, Fin (r τ)) => (⟨ℓ.1, ℓ.2, b⟩ : Formalism.L2.Pj.Letter T r n)) := by
    intro x y h
    exact congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => (⟨ℓ.1, ℓ.2.1⟩ : Σ τ : T, Fin (r τ))) h
  ext ⟨τ, i, c⟩
  rw [Multiset.count_filter]
  by_cases h : c = b
  · subst h
    rw [if_pos rfl]
    have := Multiset.count_map_eq_count' _ (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm
        fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, c⟩)) hinj ⟨τ, i⟩
    rw [this]
    simp [Finsupp.count_toMultiset]
  · rw [if_neg h]
    symm
    rw [Multiset.count_eq_zero, Multiset.mem_map]
    rintro ⟨x, -, hx⟩
    exact h (congrArg (fun ℓ : Formalism.L2.Pj.Letter T r n => ℓ.2.2) hx).symm

theorem polyDeriv_prod_cols : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : Type) [Fintype T] (r : T → ℕ) (n : ℕ) (u : (Σ τ : T, Fin (r τ)) → V) (θ : Fin n → V → ℂ), (∀ b, Differentiable ℂ (θ b)) → ∀ P : MvPolynomial (Formalism.L2.Pj.Letter T r n) ℂ, I2.polyDeriv P (fun ℓ => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) (fun z => ∏ b, θ b (z b)) 0 = ∑ m ∈ P.support, P.coeff m * ∏ b, I2.polyDeriv (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩) (1 : ℂ)) u (θ b) 0 := by
  intro V _ _ _ T _ r n u θ hθ P
  classical
  have hω : ∀ b x, ContDiffAt ℂ ω (θ b) x := fun b x =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (hθ b).differentiableOn Filter.univ_mem ω
  have hs : ∀ b, ContDiff ℂ (⊤ : ℕ∞) (θ b) := fun b =>
    contDiff_iff_contDiffAt.2 fun x => (hω b x).of_le le_top
  rw [I2.polyDeriv_eq_of_subset P _ _ _ (Finset.Subset.refl _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [I2.pdTerm_eq_itD]
  have e : (Finsupp.toMultiset m).toList.map
      (fun ℓ : Formalism.L2.Pj.Letter T r n => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) =
      ((Finsupp.toMultiset m).toList.map
        (fun ℓ : Formalism.L2.Pj.Letter T r n => ((ℓ.2.2, u ⟨ℓ.1, ℓ.2.1⟩) : Fin n × V))).map
        (fun p => Pi.single p.1 p.2) := by
    rw [List.map_map]; rfl
  rw [e, I2.itD_prod hs]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD]
  refine lD_perm (hω b 0) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe u, Multiset.coe_toList]
  have h := congrArg (Multiset.map fun ℓ : Formalism.L2.Pj.Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩)
    (filter_col_toMultiset m b)
  rw [Multiset.map_map] at h
  refine Eq.trans ?_ h
  conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
  rw [Multiset.filter_coe, Multiset.map_coe]
  unfold I2.colL
  rw [List.filter_map, List.map_map]
  rfl

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdColumnFunctionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDeriv_prod_column_functions : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : Type) [Fintype T] (r : T → ℕ) (n : ℕ) (u : (Σ τ : T, Fin (r τ)) → V) (θ : Fin n → V → ℂ), (∀ b, Differentiable ℂ (θ b)) → ∀ P : MvPolynomial (Formalism.L2.Pj.Letter T r n) ℂ, I2.polyDeriv P (fun ℓ => (Pi.single ℓ.2.2 (u ⟨ℓ.1, ℓ.2.1⟩) : Fin n → V)) (fun z => ∏ b, θ b (z b)) 0 = ∑ m ∈ P.support, P.coeff m * ∏ b, I2.polyDeriv (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun ℓ : (Σ τ : T, Fin (r τ)) => m ⟨ℓ.1, ℓ.2, b⟩) (1 : ℂ)) u (θ b) 0 := by
  first | exact @GlobalTheory.AnVal.polyDeriv_prod_cols | exact GlobalTheory.AnVal.polyDeriv_prod_cols | (intros; apply GlobalTheory.AnVal.polyDeriv_prod_cols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueCanonicalConnectionEqPolyDeriv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem sum_support_natCast_smul {σ K : Type} [Field K] [Algebra K ℂ] (N : ℕ) (P : MvPolynomial σ K)
    (hs : ((N : K) • P).support = P.support) (v : (σ →₀ ℕ) → ℂ) :
    ∑ m ∈ ((N : K) • P).support, algebraMap K ℂ (((N : K) • P).coeff m) * v m =
      (N : ℂ) * ∑ m ∈ P.support, algebraMap K ℂ (P.coeff m) * v m := by
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, map_natCast, _root_.mul_assoc]

theorem harm_nab_eq_polyDeriv : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : Fin n → (Fin g → ℂ) → ℂ), (∀ b, Φ.toAnFr.Rd k (F b) (θ b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, θ b (z b)) 0 := by
  intro hC E _ _ _ H Dw l Xo c _ _ y g ty el Φ nab hnab k n F θ hθ a P hP
  classical
  obtain ⟨N, hN, hNP, hs⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := hnab.2 ℂ y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  obtain ⟨C, hd, hh, hF, hu, hgerm⟩ := GlobalTheory.T.exists_analytic_biextension_chart_complex_point E H Dw l Xo c y g ty el Φ hnab.1
  subst hd
  have hdiff : ∀ b, Differentiable ℂ (θ b) := fun b =>
    ((GlobalTheory.T.section_reading_existsUnique_isTheta _ _ _ _ _ Φ.toAnFr k (F b)).2.1 (θ b) (hθ b)).1
  have hg : ∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (tay (θ b) 0) := fun b => by
    have h := hgerm k (F b) (θ b) (hθ b)
    have e : (fun p : Fin 1 × Fin C.d => (p.1, Fin.cast (rfl : C.d = C.d).symm p.2)) = id := rfl
    simp only [e, MvPowerSeries.rename_id, AlgHom.id_apply] at h
    exact h
  have h := hC E H Dw l Xo c hnab.1 ℂ y C₁ C k n F f₁ (fun b => tay (θ b) 0) hf₁ hg a _ hNP
  unfold chartVal at h
  rw [sum_support_natCast_smul N P hs, sum_support_natCast_smul N P hs] at h
  have h' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hN.ne' : (N : ℂ) ≠ 0) h
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal ℂ C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  simp only [e₁]
  rw [h']
  have huu : C.uvec = fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ) := by
    funext ℓ i
    rw [hu ℓ i, Pi.single_apply]
    rfl
  have hpd := GlobalTheory.T.polyDeriv_prod_column_functions (Fin C.d → ℂ) (E →+* ℂ) Dw.mult n
    (fun ℓ : Lt1 Dw => (Pi.single (el.symm ℓ) 1 : Fin C.d → ℂ)) θ hdiff
    (MvPolynomial.map (algebraMap c.F ℂ) P)
  refine Eq.trans ?_ hpd.symm
  rw [MvPolynomial.support_map_of_injective P (algebraMap c.F ℂ).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [hh, huu]
  exact nabVal_additive C.B hF H.w0 k ((GlobalTheory.SCV.contDiff_of_differentiable (hdiff b) _).contDiffAt) _ _

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueCanonicalConnectionEqPolyDerivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_canonicalConnection_eq_polyDeriv : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : Fin n → (Fin g → ℂ) → ℂ), (∀ b, Φ.toAnFr.Rd k (F b) (θ b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∑ m ∈ P.support, algebraMap c.F ℂ (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) = I2.polyDeriv (MvPolynomial.map (algebraMap c.F ℂ) P) (letDir el) (fun z => ∏ b, θ b (z b)) 0 := by
  first | exact @GlobalTheory.AnVal.harm_nab_eq_polyDeriv | exact GlobalTheory.AnVal.harm_nab_eq_polyDeriv | (intros; apply GlobalTheory.AnVal.harm_nab_eq_polyDeriv <;> assumption)
end
end
