module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Val

variable {F : Type} [Field F] {X Y : Scheme.{0}}

theorem valF_appLE {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_mul {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a * b) = valF x U a * valF x U b := by
  simp only [valF, dif_pos h, map_mul]

theorem valF_mul_inv {x : Sp F ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valF x U a.val * valF x U (a⁻¹).val = 1 := by
  rw [← valF_mul h, a.mul_inv]
  simp only [valF, dif_pos h, map_one]

theorem valF_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (χ : Γ(X, V) →+* F) (s : Γ(X, V)) :
    valF (spMap χ ≫ hV.fromSpec) V s = χ s := by
  have h0 : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V := fun q _ => h0 (Set.mem_univ (spMap χ q))
  rw [valF, dif_pos h]
  have e : (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom = CommRingCat.ofHom χ := by
    have e1 : hV.fromSpec.appLE V ⊤ h0 = (Scheme.ΓSpecIso Γ(X, V)).inv := by
      rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg _ ((Spec Γ(X, V)).presheaf.map_id _)).trans (Category.comp_id _)
    rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h0 le_rfl, e1, Category.assoc, Iso.inv_comp_eq]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
  exact congrArg (fun g => g.hom s) e

theorem exists_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] (w : Sp R ⟶ X)
    (h : ⊤ ≤ w ⁻¹ᵁ V) : ∃ χ : Γ(X, V) →+* R, spMap χ ≫ hV.fromSpec = w := by
  have h' : Set.range w ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hV.range_fromSpec]
    exact h (Set.mem_univ q)
  exact ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec w h')).hom,
    (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)⟩

theorem le_of_fromSpec {V : X.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R] {w : Sp R ⟶ X}
    {χ : Γ(X, V) →+* R} (h : spMap χ ≫ hV.fromSpec = w) : ⊤ ≤ w ⁻¹ᵁ V := fun q _ =>
  h ▸ hV.fromSpec_preimage_self.ge (Set.mem_univ (spMap χ q))

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Frames

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l l' : Level H} {c : Coeff l} {c' : Coeff l'}

theorem eig_iff {R : Type} [CommRing R] {x : Sp R ⟶ X} (v : TanM x t.G) (a : 𝓞 E) (s : R) :
    (tv v).left ≫ (t.act.act a).left = spMap (epsMul s) ≫ (tv v).left ↔ actR t.act a v = s • v :=
  ⟨fun h => tan_ext h, fun h => congrArg (fun z => (tv z).left) h⟩

theorem frame_ind {k : Type} [Field k] {f : c.F →+* k} {x : Sp k ⟶ X} {u : Vecs Dw t k}
    (h : GlobalTheory.LocM.IsFrame t f x u) (τ : E →+* ℂ) : Ind t x (u τ) := by
  refine ⟨fun i => (h.1 τ i).1, fun cf cf' w h1 h2 => ?_⟩
  obtain ⟨U, hU⟩ := exists_tan fun i => (h.1 τ i).1
  have e := (comb_iff U cf w).1 (hU ▸ h1)
  refine (h.2 τ w (e ▸ isTan_tv _) fun a => ?_).unique h1 h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, eig_iff, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_comm, (eig_iff (U i) a _).1 (congrFun hU i ▸ (h.1 τ i).2 a)]

variable {g : X' ⟶ X} (mu : SABMap t' t g) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X} (hx : x' ≫ g = x)

include hx

theorem comb_push {m : ℕ} {u : Fin m → (Sp (DualNumber R) ⟶ t'.G.left)} (hu : ∀ i, IsTanAtG t' x' (u i))
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : IsTanAtG t' x' w) (cf : Fin m → R) :
    IsCombAtG t x (fun i => u i ≫ mu.φ) cf (w ≫ mu.φ) ↔ IsCombAtG t' x' u cf w := by
  refine (GlobalTheory.LieMet.isComb_iff (fun i => pushE mu x' hx (tanOf (hu i))) cf (pushE mu x' hx (tanOf hw))).trans
    (Iff.trans ?_ (GlobalTheory.LieMet.isComb_iff (fun i => tanOf (hu i)) cf (tanOf hw)).symm)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_smul, ← map_sum, EmbeddingLike.apply_eq_iff_eq]

theorem frame_push {f' : c'.F →+* R} {f : c.F →+* R} (hf : ∀ τ a, f (embK c τ a) = f' (embK c' τ a))
    {u : Vecs Dw t' R} (h : GlobalTheory.LocM.IsFrame t' f' x' u) : GlobalTheory.LocM.IsFrame (Dw := Dw) t f x fun τ i => u τ i ≫ mu.φ := by
  refine ⟨fun τ i => ⟨isTan_push mu x' hx (h.1 τ i).1, fun a => ?_⟩, fun τ w hw he => ?_⟩
  · rw [Category.assoc, ← mu.act, ← Category.assoc, (h.1 τ i).2, hf, Category.assoc]
  · obtain ⟨v, hv⟩ := (pushE mu x' hx).surjective (tanOf hw)
    obtain rfl : (tv v).left ≫ mu.φ = w := congrArg (fun z => (tv z).left) hv
    refine (existsUnique_congr fun cf => comb_push mu hx (fun i => (h.1 τ i).1) (isTan_tv v) cf).2
      (h.2 τ _ (isTan_tv v) fun a => (eig_iff v a _).2 ((pushE mu x' hx).injective ?_))
    rw [pushE_act, map_smul, ← hf]
    exact (eig_iff _ a _).1 (he a)

end Frames

section Steps

variable {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {l : Level H} {c : Coeff l} {p : ℕ}

end Steps

section Models

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem chart_frame (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    GlobalTheory.LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (w ≫ Z.π) ((Z.fr a).bc φ) := by
  rw [← h, Category.assoc]
  exact GlobalTheory.T.isFrame_compose_ringHom_baseChange E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)

theorem affineOpenChart_comp_structure_eq_spMap (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    w ≫ Z.π ≫ (Y Z.i).s = spMap (φ.comp (Z.alg a)) ≫ spMap (Z.i.c.V W).subtype := by
  rw [Z.π_s, ← h, Category.assoc, Z.alg_s, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, RingHom.comp_assoc]

theorem range_opn (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) : Set.range w ⊆ Z.opn := by
  rintro _ ⟨q, rfl⟩
  rw [← Z.cover]
  exact Set.mem_iUnion.2 ⟨a, le_of_fromSpec (Z.U a).2 h (Set.mem_univ q)⟩

theorem exists_open_lift (Z : Mdl Y i₀) {a : Fin Z.m} {R : Type} [CommRing R] {φ : Γ(Z.X, (Z.U a).1) →+* R}
    {w : Sp R ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w) :
    ∃ y : Sp R ⟶ (Xo Z.i.l).XF Z.i.c, y ≫ (Y Z.i).j = w ≫ Z.π := by
  have := (Y Z.i).jQ_open
  let q : Sp R ⟶ pullback (Y Z.i).s (spMap (Z.i.c.V W).subtype) :=
    pullback.lift (w ≫ Z.π) _ ((Category.assoc _ _ _).trans (affineOpenChart_comp_structure_eq_spMap Z h))
  have hq : q ≫ pullback.fst _ _ = w ≫ Z.π := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap (Z.i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := Z.i.c.V W) (S := Z.i.c.F) (nonZeroDivisors _)
  have hr : Set.range q ⊆ Set.range (Y Z.i).jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := range_opn Z h ⟨z, rfl⟩
    refine ⟨y, (pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply w]
    exact hy
  exact ⟨IsOpenImmersion.lift _ q hr, by rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, IsOpenImmersion.lift_fac_assoc, hq]⟩

theorem tri_of_sameFlag {X : Scheme.{0}} {t : SAB H X} {k : Type} [Field k] {x : Sp k ⟶ X} {u u' : Vecs Dw t k}
    {ty : (E →+* ℂ) → Finset ℕ} (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ ty τ) (h : SameFlag ty t x u u') (τ : E →+* ℂ) :
    Tri t x (u τ) (u' τ) := fun j => h τ (j + 1) (hty τ _ j.2) j (Nat.lt_succ_self _)

theorem chart_tri (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) {k : Type} [Field k] {a a' : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} {φ' : Γ(Z.X, (Z.U a').1) →+* k} {w : Sp k ⟶ Z.X} (h : spMap φ ≫ Z.chart a = w)
    (h' : spMap φ' ≫ Z.chart a' = w) (τ : E →+* ℂ) :
    Tri (Y Z.i).t (w ≫ Z.π) ((Z.fr a).bc φ τ) ((Z.fr a').bc φ' τ) := by
  have := tri_of_sameFlag hty (Z.glue k a a' φ φ' (h.trans h'.symm)) τ
  rwa [← Category.assoc, h] at this

theorem isReduced_model (Z : Mdl Y i₀) : IsReduced Z.X :=
  have := Z.normal
  inferInstance

theorem isSeparated_base (i : Idx H p) : (Y i).X.IsSeparated := by
  have := projProper _ _ _ (Y i).proj
  exact ⟨by rw [← terminal.comp_from (Y i).s]; infer_instance⟩

theorem ext_unique (i : Idx H p) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ (Y i).X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have := isSeparated_base (Y := Y) i
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

variable {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)

include hf hT

end Models

section Bundle

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

end Bundle

section Main

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z Z' : Mdl Y i₀} {f : Z'.X ⟶ Z.X} {τ : (Y Z'.i).X ⟶ (Y Z.i).X}
  {b : Bool} {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw}

variable (hf : IsMap Z' Z f) {mu : SABMap (Y Z'.i).t (Y Z.i).t τ} (hT : IsTrans Z.i Z'.i τ mu)
  (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ) (M : LineModel Z b st x)

include hf hT hty

end Main

end GlobalTheory.ShFam.Pad.Pull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CechPic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.InvertIdeal

section General

variable {X : Scheme.{0}} [IsIntegral X]

theorem exists_mul_pow {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (α : Γ(X, U))
    (hα : genericPoint X ∈ X.basicOpen α) {f : X.functionField} (hf : ∀ x ∈ X.basicOpen α, RegAt x f) :
    ∃ (n : ℕ) (γ : Γ(X, U)), fnOf U h γ = f * fnOf U h α ^ n := by
  obtain ⟨β, rfl⟩ := exists_fnOf_eq hα hf
  have := hU.isLocalization_basicOpen α
  obtain ⟨n, γ, e⟩ := IsLocalization.Away.surj α β
  refine ⟨n, γ, ?_⟩
  have e' := congrArg (fnOf _ hα) e
  rw [map_mul, map_pow] at e'
  have r (a : Γ(X, U)) : fnOf _ hα (algebraMap _ Γ(X, X.basicOpen α) a) = fnOf U h a :=
    fnOf_resG (X.basicOpen_le α) hα a
  rw [r, r] at e'
  exact e'.symm

theorem exists_denom {U : X.Opens} (hU : IsAffineOpen U) (h : genericPoint X ∈ U) {x : X} (hx : x ∈ U)
    {f : X.functionField} (hf : RegAt x f) :
    ∃ β γ : Γ(X, U), x ∈ X.basicOpen β ∧ fnOf U h γ = f * fnOf U h β := by
  obtain ⟨W, hW, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨α, hle, hα⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hW⟩ hx
  obtain ⟨n, γ, e⟩ := exists_mul_pow hU h α (gen_mem hα) fun y hy => regAt_fnOf (hle hy) (gen_mem hW) a
  refine ⟨α ^ (n + 1), γ * α, by rwa [X.basicOpen_pow α n.succ_pos], ?_⟩
  rw [map_mul, e, map_pow, pow_succ, mul_assoc]

theorem exists_unitAt {x : X} {ι : Type} [Fintype ι] {c g : ι → X.functionField} (hc : ∀ i, RegAt x (c i))
    (hg : ∀ i, RegAt x (g i)) (e : ∑ i, c i * g i = 1) : ∃ i, UnitAt x (g i) := by
  by_contra! H
  have : ZeroAt x (∑ i, c i * g i) := Finset.sum_induction _ _ (fun _ _ => ZeroAt.add) (zeroAt_zero x) fun i _ =>
    mul_comm (g i) (c i) ▸ (zeroAt_iff.2 ⟨hg i, H i⟩).mul (hc i)
  exact (zeroAt_iff.1 (e ▸ this)).2 (unitAt_one x)

theorem exists_common_open {x : X} {ι : Type} [Finite ι] {g : ι → X.functionField} (hg : ∀ i, RegAt x (g i)) :
    ∃ (W : X.Opens) (hx : x ∈ W), ∀ i, ∃ a : Γ(X, W), fnOf W (gen_mem hx) a = g i := by
  choose U hU a ha using fun i => (hg i).exists_fnOf
  let W : X.Opens := ⟨⋂ i, U i, isOpen_iInter_of_finite fun i => (U i).isOpen⟩
  have hle (i) : W ≤ U i := Set.iInter_subset (fun i => (U i : Set X)) i
  exact ⟨W, Set.mem_iInter.2 hU, fun i => ⟨resG X (hle i) (a i), (fnOf_resG _ _ _).trans (ha i)⟩⟩

end General

variable {F : Type} [Field F] [NumberField F]

end GlobalTheory.InvertIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRootsHolds
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

namespace GlobalTheory.LocM.RootsPrescribe

theorem exists_smul_of_mem_of_coprime {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L] {I J : Ideal R} {r : R}
    (hc : I ⊔ J = ⊤) (hp : I * J = Ideal.span {r}) {x : L} (hI : x ∈ I • (⊤ : Submodule R L))
    (hJ : x ∈ J • (⊤ : Submodule R L)) : ∃ b, x = r • b := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : R) ∈ I ⊔ J from hc ▸ Submodule.mem_top)
  have h1 : u • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_smul]; exact Submodule.smul_mem_smul hu hJ
  have h2 : v • x ∈ (I * J) • (⊤ : Submodule R L) := by
    rw [mul_comm, mul_smul]; exact Submodule.smul_mem_smul hv hI
  have h3 : x ∈ (I * J) • (⊤ : Submodule R L) := by
    have := Submodule.add_mem _ h1 h2
    rwa [← add_smul, huv, one_smul] at this
  rw [hp, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨b, -, hb⟩ := h3
  exact ⟨b, hb.symm⟩

theorem exists_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) (hpq : 1 ≤ Dw.p + Dw.q) {m : ℕ} (hm : 0 < m) {w : kˣ}
    (hw : IsPrimitiveRoot w (l.A * m)) (hA : w ^ m = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, I'.ζ (l.A * m) = w ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  have hN : 0 < l.A * m := Nat.mul_pos l.A_pos hm
  have hM : 0 < l.M := by have := l.three_le; omega
  have : NeZero (l.A * m) := ⟨hN.ne'⟩
  have hζ : IsPrimitiveRoot ((I.ζ (l.A * m) : kˣ) : k) (l.A * m) := IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim _ hN)
  obtain ⟨i, -, hi, hiz⟩ := (hζ.isPrimitiveRoot_iff).1 (IsPrimitiveRoot.coe_units_iff.2 hw)
  have hiz' : I.ζ (l.A * m) ^ i = w := Units.ext (by rw [Units.val_pow_eq_pow_val, hiz])
  have hi1 : (l.A : ℤ) ∣ (i : ℤ) - 1 := by
    rw [← (I.ζ_prim l.A l.A_pos).zpow_eq_one_iff_dvd, zpow_sub, zpow_one, zpow_natCast, mul_inv_eq_one]
    conv_lhs => rw [← I.ζ_pow l.A m l.A_pos hm, ← pow_mul, mul_comm m, pow_mul, hiz', hA]
  obtain ⟨g, hg, -, hgM, hgA⟩ := GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift E H Dw
    l (l.A * m) i hN (Nat.isCoprime_iff_coprime.2 hi) hi1
  refine ⟨GlobalTheory.LevelTwist.twist I g ((GlobalTheory.SimAlg.sim_group E H Dw hpq).1 g), ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.LevelTwist.twist_ζ, GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, hiz']
  · exact GlobalTheory.LevelTwist.ev_congr I l.A_pos (hgA a)
  · refine GlobalTheory.LevelTwist.ev_congr I hM ?_
    obtain ⟨b, hb⟩ := exists_smul_of_mem_of_coprime l.coprime l.prod (hgM a)
      (Submodule.sub_mem _ (GlobalTheory.LevelTwist.map_mem_smul_top _ _ ha) ha)
    exact ⟨b, hb.trans (Nat.cast_smul_eq_nsmul _ _ _)⟩

private theorem exists_finite_reps (L : Type) [AddCommGroup L] [Module.Finite ℤ L] {M : ℕ} (hM : 0 < M) :
    ∃ (A : Type) (_ : Finite A) (r : A → L), ∀ a, ∃ x b, a = r x + M • b := by
  let N : Submodule ℤ L := LinearMap.range ((M : ℤ) • (LinearMap.id : L →ₗ[ℤ] L))
  have hfin : Finite (L ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(M : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hM.ne')⟩, ?_⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    change (M : ℤ) • N.mkQ y = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨L ⧸ N, hfin, Quotient.out, fun a => ⟨Submodule.Quotient.mk a, ?_⟩⟩
  have h : a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) ∈ N :=
    (Submodule.Quotient.eq N).1 (Quotient.out_eq (Submodule.Quotient.mk a : L ⧸ N)).symm
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  have : M • b = a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) := by
    rw [← hb]; simp
  rw [this]; abel

private theorem ev_add_nsmul {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) {M : ℕ} (hM : 0 < M) (a b : Dw.La) : I.ev M (a + M • b) = I.ev M a := by
  rw [I.add, (I.ker M hM _).2 ⟨b, rfl⟩, _root_.mul_one]

private theorem finite_level {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    {M : ℕ} (hM : 0 < M) :
    (Set.range fun I : TateIso Dw k Q act e => (I.ev M, I.ζ M)).Finite := by
  rcases isEmpty_or_nonempty (TateIso Dw k Q act e) with h | ⟨⟨I₀⟩⟩
  · exact Set.finite_range _
  haveI := Dw.fin
  haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  obtain ⟨A, hA, r, hr⟩ := exists_finite_reps Dw.La hM
  have hT : {x : Q | x ^ M = 1}.Finite := by
    refine (Set.finite_range fun x => I₀.ev M (r x)).subset fun x hx => ?_
    obtain ⟨a, rfl⟩ := (I₀.onto M hM x).1 hx
    obtain ⟨y, b, rfl⟩ := hr a
    exact ⟨y, (ev_add_nsmul I₀ hM _ _).symm⟩
  have h₁ : (Set.range fun I : TateIso Dw k Q act e => I.ev M).Finite := by
    refine Set.Finite.of_finite_image (f := fun f => f ∘ r) ?_ ?_
    · refine (Set.Finite.pi' fun _ : A => hT).subset ?_
      rintro _ ⟨_, ⟨I, rfl⟩, rfl⟩ x
      exact (I.onto M hM _).2 ⟨_, rfl⟩
    · rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩ h
      funext a
      obtain ⟨y, b, rfl⟩ := hr a
      simp only [ev_add_nsmul _ hM]
      exact congrFun h y
  have h₂ : (Set.range fun I : TateIso Dw k Q act e => I.ζ M).Finite := by
    haveI : NeZero M := ⟨hM.ne'⟩
    have hfin : Finite (rootsOfUnity M k) := inferInstance
    refine Set.Finite.subset (s := (rootsOfUnity M k : Set kˣ)) hfin ?_
    rintro _ ⟨I, rfl⟩
    exact (I.ζ_prim M hM).pow_eq_one
  refine (h₁.prod h₂).subset ?_
  rintro _ ⟨I, rfl⟩
  exact ⟨⟨I, rfl⟩, ⟨I, rfl⟩⟩

private theorem exists_limit (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop)
    (I : ℕ → TateIso Dw k Q act e) :
    ∃ I' : TateIso Dw k Q act e, ∀ M, 0 < M → ∀ j₀, ∃ j, j₀ ≤ j ∧ I'.ev M = (I j).ev M ∧ I'.ζ M = (I j).ζ M := by
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have key : ∀ M, ∃ p : (Dw.La → Q) × kˣ, (∃ j, p.1 = (I j).ev M) ∧
      (0 < M → ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M) := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact ⟨((I 0).ev 0, 1), ⟨0, rfl⟩, fun h => absurd h (lt_irrefl _)⟩
    obtain ⟨p, -, hp⟩ := Ultrafilter.eq_pure_of_finite_mem (f := U.map fun j => ((I j).ev M, (I j).ζ M))
      (finite_level (Dw := Dw) (act := act) (e := e) hM)
      (Ultrafilter.mem_map.2 (Filter.univ_mem' fun j => ⟨I j, rfl⟩))
    have h : ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M := by
      have : {p} ∈ U.map fun j => ((I j).ev M, (I j).ζ M) := by rw [hp]; exact Ultrafilter.mem_pure.2 rfl
      filter_upwards [Ultrafilter.mem_coe.2 (Ultrafilter.mem_map.1 this)] with j hj
      have hj' : ((I j).ev M, (I j).ζ M) = p := hj
      rw [← hj']; exact ⟨rfl, rfl⟩
    exact ⟨p, h.exists.imp fun _ h => h.1, fun _ => h⟩
  choose p hp₀ hp using key
  have one : ∀ n, 0 < n → ∃ j, (p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n := fun n hn => (hp n hn).exists
  have two : ∀ n m, 0 < n → 0 < m → ∃ j, ((p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n) ∧
      (p (n * m)).1 = (I j).ev (n * m) ∧ (p (n * m)).2 = (I j).ζ (n * m) := fun n m hn hm =>
    ((hp n hn).and (hp _ (Nat.mul_pos hn hm))).exists
  refine ⟨{ ζ := fun n => (p n).2
            ev := fun n => (p n).1
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => ?_
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun M hM j₀ => ?_⟩
  · obtain ⟨j, -, h⟩ := one n hn
    rw [h]; exact (I j).ζ_prim n hn
  · obtain ⟨j, ⟨-, h⟩, -, h'⟩ := two n m hn hm
    rw [h, h']; exact (I j).ζ_pow n m hn hm
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).add n a b
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).lin n c a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).ker n hn a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).onto n hn x
  · obtain ⟨j, ⟨h, -⟩, h', -⟩ := two n m hn hm
    rw [h, h']; exact (I j).tower n m hn hm a
  · obtain ⟨j, h, h'⟩ := one n hn
    rw [h, h']; exact (I j).isom n hn a b
  · have h : ∀ᶠ j in (U : Filter ℕ), j₀ ≤ j := Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop j₀)
    exact (h.and (hp M hM)).exists

theorem roots : GlobalTheory.LocM.Cht.RootsSt := by
  intro E _ _ _ H Dw l k _ Q _ act e I z hpq hz hzp hA
  have hM : 0 < l.M := by have := l.three_le; omega
  have key := fun j : ℕ => exists_one l I hpq j.factorial_pos (hz _ (Nat.mul_pos l.A_pos j.factorial_pos))
    ((hzp _ _ l.A_pos j.factorial_pos).trans hA)
  choose J hJ hJA hJM using key
  obtain ⟨I', hI'⟩ := exists_limit E H Dw k Q act e J
  refine ⟨I', fun n hn => ?_, fun a => ?_, fun a ha => ?_⟩
  · obtain ⟨j, hj, -, h⟩ := hI' n hn n
    obtain ⟨t, ht⟩ : n ∣ l.A * j.factorial := (Nat.dvd_factorial hn hj).mul_left _
    have ht0 : 0 < t := Nat.pos_of_mul_pos_left (ht ▸ Nat.mul_pos l.A_pos j.factorial_pos : 0 < n * t)
    rw [h, ← (J j).ζ_pow n t hn ht0, ← hzp n t hn ht0, ← ht, hJ]
  · obtain ⟨j, -, h, -⟩ := hI' l.A l.A_pos 0
    rw [h, hJA]
  · obtain ⟨j, -, h, -⟩ := hI' l.M hM 0
    rw [h, hJM j a ha]

end GlobalTheory.LocM.RootsPrescribe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCoordinatesStep
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull ev_res ev_appLE le_preimage_inf le_preimage_map le_preimage_mono)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.GrCl

section Frames

variable {X Z : Scheme.{0}} {F : X.Modules} {S : Type} [CommRing S]

def frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') : Matrix (Fin n) (Fin n') Γ(X, U) :=
  ((hm'.basis h').toMatrix (hm.basis h)).transpose

theorem sum_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (l : Fin n) :
    resM F h (m l) = ∑ l', frMat hm hm' h h' l l' • resM F h' (m' l') := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, ← hm'.basis_apply h']
  rw [Module.Basis.sum_repr, hm.basis_apply]

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Lin

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens}

def tanLin (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) : TanM x t.G →ₗ[S] (Fin n → S) where
  toFun v l := tanEv t (isTan_tv v) h (s l)
  map_add' v w := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 2 (fun i => (tv (![v, w] i)).left) (fun i => isTan_tv _) ![1, 1] _
      (isTan_tv (v + w)) ((LieMet.isComb_iff _ _ _).2 (by simp)) (s l)
    simpa using this
  map_smul' a v := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 1 (fun _ => (tv v).left) (fun _ => isTan_tv _) (fun _ => a) _
      (isTan_tv (a • v)) ((LieMet.isComb_iff (fun _ => v) _ _).2 (by simp)) (s l)
    simpa using this

theorem tanLin_apply (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) (l : Fin n) :
    tanLin t h s v l = tanEv t (isTan_tv v) h (s l) := rfl

theorem tanEv_sum_smul (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ l, a l • s l) = ∑ l, ev x V h (a l) * tanEv t hv h (s l) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have := tanEv_smul t hv h 0 0
    simpa using this
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tanEv_add, tanEv_smul, ih]; rfl

theorem tanLin_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ V)
    (h' : ⊤ ≤ x' ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) :
    tanLin t h' s (tanPull φ e v) = φ ∘ tanLin t h s v := by
  subst e
  exact funext fun l =>
    GlobalTheory.LocM.tanEv_baseChange E H X t S x V h _ (isTan_tv v) S' φ _ h' (s l)

theorem tanLin_injective (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) {U : X.Opens} (e : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hs : VB.IsFrame fun l => resM _ e (s l)) : Function.Injective (tanLin t h s) := fun v w hvw =>
  tan_ext ((GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x U hU n _ hs (tanLin t h s w)).unique
    ⟨isTan_tv v, fun l => (tanEv_resM t _ hU e _).trans (congrFun hvw l)⟩
    ⟨isTan_tv w, fun _ => tanEv_resM t _ hU e _⟩)

end Lin

section Phi

variable {X X' X₀ Z : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {t₀ : SAB H X₀} {τ : X ⟶ X₀} {τ' : X' ⟶ X₀}
  (mu : SABMap t t₀ τ) (mu' : SABMap t' t₀ τ') {π : Z ⟶ X} {g : Z ⟶ X'} (e : g ≫ τ' = π ≫ τ)
  {S : Type} [CommRing S]

end Phi

end GlobalTheory.GrCl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

private theorem wedgeForm_update_eq_zero_of_mem_span_others {S N : Type} [CommRing S]
    [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S) (v : Fin k → N) (i : Fin k)
    {x : N} (hx : x ∈ Submodule.span S (v '' {j | j ≠ i})) :
    F (Function.update v i x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j ≠ i := hj
    exact F.map_eq_zero_of_eq (Function.update v i (v j)) (i := i) (j := j)
      (by simp [Function.update_of_ne hj']) (Ne.symm hj')
  | zero => exact F.map_update_zero v i
  | add y z _ _ hy hz => rw [F.map_update_add, hy, hz, add_zero]
  | smul a y _ hy => rw [F.map_update_smul, hy, smul_zero]

private theorem wedgeForm_eq_prod_mul_of_triangular_change {T : Type} {m : T → ℕ} {S N : Type}
    [CommRing S] [AddCommGroup N] [Module S N] {k : ℕ} (F : N [⋀^Fin k]→ₗ[S] S)
    (c c' : _root_.GlobalTheory.FlagEmb.Let m → N) (d : _root_.GlobalTheory.FlagEmb.Let m → S)
    (ht : ∀ z : _root_.GlobalTheory.FlagEmb.Let m, c' z - d z • c z ∈
      Submodule.span S ((fun j => c ⟨z.fst, j⟩) '' {j | j < z.snd}))
    (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    F (fun l => c' (e l)) = (∏ l, d (e l)) * F (fun l => c (e l)) := by
  classical
  obtain ⟨_, hdown⟩ := he
  let w : Finset (Fin k) → Fin k → N := fun s l => if l ∈ s then c' (e l) else c (e l)
  have key : ∀ s : Finset (Fin k), F (w s) = (∏ l ∈ s, d (e l)) * F (w ∅) := by
    intro s
    refine Finset.induction_on_min_value (fun l => ((e l).snd : ℕ)) s ?_ ?_
    · simp
    · intro a s ha hmin ih
      have hw : w (insert a s) = Function.update (w s) a
          (d (e a) • w s a + (c' (e a) - d (e a) • c (e a))) := by
        funext l
        by_cases hl : l = a
        · subst hl
          simp [w, ha]
        · simp [w, hl, Function.update_of_ne hl]
      have hzero : F (Function.update (w s) a (c' (e a) - d (e a) • c (e a))) = 0 := by
        refine wedgeForm_update_eq_zero_of_mem_span_others F (w s) a ?_
        refine Submodule.span_mono ?_ (ht (e a))
        rintro _ ⟨j, hj, rfl⟩
        have hj' : (j : ℕ) < ((e a).snd : ℕ) := hj
        obtain ⟨l', hl'⟩ := hdown a j hj
        have hsnd : ((e l').snd : ℕ) = j := by
          have := congrArg (fun z : _root_.GlobalTheory.FlagEmb.Let m => (z.snd : ℕ)) hl'
          simpa using this
        have hne : l' ≠ a := by
          rintro rfl
          omega
        have hns : l' ∉ s := by
          intro h
          have := hmin l' h
          omega
        refine ⟨l', hne, ?_⟩
        simp [w, hns, hl']
      rw [hw, F.map_update_add, F.map_update_smul, Function.update_eq_self, hzero,
        Finset.prod_insert ha, ih, smul_eq_mul, add_zero, mul_assoc]
  have h1 : w Finset.univ = fun l => c' (e l) := by
    funext l
    simp [w]
  have h2 : w ∅ = fun l => c (e l) := by
    funext l
    simp [w]
  have := key Finset.univ
  rwa [h1, h2] at this

theorem _root_.GlobalTheory.FlagEmb.plk_tri (T : Type) (m : T → ℕ) (S : Type) [CommRing S]
    (M : ℕ) (c c' : _root_.GlobalTheory.FlagEmb.Let m → Fin (M + 1) → S)
    (d : _root_.GlobalTheory.FlagEmb.Let m → S) (k : ℕ) (e : Fin k → _root_.GlobalTheory.FlagEmb.Let m)
    (ht : _root_.GlobalTheory.FlagEmb.Tri c c' d) (he : _root_.GlobalTheory.FlagEmb.Down e) :
    _root_.GlobalTheory.FlagEmb.plk c' e = (∏ l, d (e l)) • _root_.GlobalTheory.FlagEmb.plk c e := by
  funext q
  have := wedgeForm_eq_prod_mul_of_triangular_change
    ((Matrix.detRowAlternating (n := Fin k) (R := S)).compLinearMap
      (LinearMap.funLeft S S (_root_.GlobalTheory.FlagEmb.plE M k q))) c c' d ht e he
  unfold _root_.GlobalTheory.FlagEmb.plk
  simp only [Pi.smul_apply, smul_eq_mul]
  exact this

end GlobalTheory.FlagEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerVectorBlockTriangularFrameChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluckerVector_blockTriangular_frame_change : ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (c c' : Let m → Fin (M + 1) → S) (d : Let m → S) (k : ℕ) (e : Fin k → Let m), Tri c c' d → Down e → plk c' e = (∏ l, d (e l)) • plk c e := by
  first | exact @GlobalTheory.FlagEmb.plk_tri | exact GlobalTheory.FlagEmb.plk_tri | (intros; apply GlobalTheory.FlagEmb.plk_tri <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)

namespace GlobalTheory.VanStalk

theorem eq_of_forall_prime {R : Type*} [CommRing R] {A B : Ideal R} (hA : A.IsRadical) (hB : B.IsRadical)
    (h : ∀ q : PrimeSpectrum R, A ≤ q.asIdeal ↔ B ≤ q.asIdeal) : A = B := by
  rw [← hA.radical, ← hB.radical, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext J
  exact ⟨fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).2 h1, h2⟩⟩

variable {X X' : Scheme.{0}}

theorem van_spec (Z : Closeds X) (x : X) :
    (stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x).IsRadical ∧
    ∀ q : PrimeSpectrum (X.presheaf.stalk x),
      X.fromSpecStalk x q ∈ Z ↔ stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x ≤ q.asIdeal := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  have hg : (X.presheaf.germ W x hx).hom = algebraMap Γ(X, W) (X.presheaf.stalk x) := rfl
  have hcl : IsClosed (X := PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage hW.fromSpec.continuous
  rw [hg]
  generalize hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) = J
  have hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (Z : Set X) := by
    rw [← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]
    rfl
  have hr : J.radical = J := hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  refine ⟨?_, fun q => ?_⟩
  · rw [← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl]
    exact Ideal.radical_isRadical _
  · have e : X.fromSpecStalk x q =
        hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q) := by
      rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
      rfl
    rw [e, Ideal.map_le_iff_le_comap]
    change PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q ∈ hW.fromSpec ⁻¹' (Z : Set X) ↔ _
    rw [← hz]
    exact (PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe

end GlobalTheory.VanStalk

namespace GlobalTheory.VanStalk

variable {X X' : Scheme.{0}}

theorem stalkId_comap_of_affine {T : Scheme.{0}} [IsAffine T] (J : X.IdealSheafData) (χ : T ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) (z : T) :
    stalkId (J.comap χ) z = (stalkId J (χ z)).map (χ.stalkMap z).hom := by
  have key : ∀ z : T, stalkId (Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom)) z =
      (stalkId J (χ z)).map (χ.stalkMap z).hom := by
    intro z
    have hz : χ z ∈ U.1 := hle trivial
    rw [GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE,
      Category.assoc]
    congr 3
    exact T.presheaf.germ_res (homOfLE hle) z (by trivial)
  rw [← GlobalTheory.Vanishing.eq_comap_of_stalk key, key]

theorem map_le_stalkId_comap (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X') :
    (stalkId J (π x')).map (π.stalkMap x').hom ≤ stalkId (J.comap π) x' := by
  by_cases hx : x' ∈ (J.comap π).support
  · obtain ⟨z, rfl⟩ := GlobalTheory.Vanishing.exists_ι_eq hx
    have h : stalkId J (π ((J.comap π).subschemeι z)) ≤ RingHom.ker
        (((J.comap π).subschemeι.stalkMap z).hom.comp (π.stalkMap ((J.comap π).subschemeι z)).hom) := by
      have h0 := (GlobalTheory.Vanishing.le_ker_iff_stalk ((J.comap π).subschemeι ≫ π)).1
        (Scheme.IdealSheafData.le_map_comap J π) z
      rw [Scheme.Hom.stalkMap_comp] at h0
      exact h0
    rw [← RingHom.comap_ker, GlobalTheory.Vanishing.ker_stalkMap] at h
    exact Ideal.map_le_iff_le_comap.2 h
  · rw [GlobalTheory.Vanishing.stalkId_eq_top _ hx]
    exact le_top

theorem stalkId_comap (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X') :
    stalkId (J.comap π) x' = (stalkId J (π x')).map (π.stalkMap x').hom := by
  refine le_antisymm ?_ (map_le_stalkId_comap π J x')
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show π x' ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V₀, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x' ∈ π ⁻¹ᵁ U from hxU)
  let V : X'.Opens := V₀
  haveI : IsAffine V.toScheme := hV
  obtain ⟨z, rfl⟩ : ∃ z : V.toScheme, V.ι z = x' := ⟨⟨x', hxV⟩, rfl⟩
  have hle : ⊤ ≤ (V.ι ≫ π) ⁻¹ᵁ U := fun w _ => hVU w.2
  have h1 := stalkId_comap_of_affine J (V.ι ≫ π) ⟨U, hU⟩ hle z
  rw [Scheme.IdealSheafData.comap_comp] at h1
  have h2 : (stalkId (J.comap π) (V.ι z)).map (V.ι.stalkMap z).hom ≤
      ((stalkId J (π (V.ι z))).map (π.stalkMap (V.ι z)).hom).map (V.ι.stalkMap z).hom := by
    have h0 := map_le_stalkId_comap V.ι (J.comap π) z
    rw [h1, Scheme.Hom.stalkMap_comp] at h0
    rw [Ideal.map_map]
    exact h0
  have hb : Function.Bijective (V.ι.stalkMap z).hom := ConcreteCategory.bijective_of_isIso _
  rwa [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hb] at h2

end GlobalTheory.VanStalk

namespace GlobalTheory.TorRef

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Points

namespace GlobalTheory.FlagEmb.QuotLine

section Pull

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (L : LB X)

variable {f L} {W V : Z.Opens} {i j k : L.ι}

end Pull

section Three

variable {X X₀ X₁ Z : Scheme.{0}} (f : Z ⟶ X) (f₀ : Z ⟶ X₀) (f₁ : Z ⟶ X₁) (L : LB X) (L₀ : LB X₀) (L₁ : LB X₁)
  {I : Type} (a : I → L.ι) (b : I → L₀.ι) (c : I → L₁.ι)

variable {f f₀ f₁ L L₀ L₁ a b c}

end Three

section Val

variable {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U)

theorem valR_chart {C : Type} [CommRing C] (φ : Γ(Z, U) →+* C) (s : Γ(Z, U)) : valR (spMap φ ≫ hU.fromSpec) U s = φ s := by
  have h := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)
  exact (valR_eq _ U h s).trans (congrArg (fun t => t.hom s) (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) h))

end Val

end GlobalTheory.FlagEmb.QuotLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)

def liftEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : Sp ℂ ⟶ Z.oF.t.G.left :=
  Z.m0.toSABMap.cart.1.lift (Fu.ex i P z).left y (by rw [Over.w (Fu.ex i P z), ← hu]; rfl)

def pushEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) : Over.mk p ⟶ Z.t.G :=
  Over.homMk (liftEx Z Fu y i P hu z ≫ Z.m.φ) (by
    show (liftEx Z Fu y i P hu z ≫ Z.m.φ) ≫ Z.t.G.hom = p
    rw [Category.assoc, Z.m.cart.1.w, ← Category.assoc, liftEx, IsPullback.lift_snd, ← hp])

theorem liftEx_fst (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.m0.toSABMap.φ = (Fu.ex i P z).left :=
  IsPullback.lift_fst _ _ _ _

theorem liftEx_snd (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.oF.t.G.hom = y :=
  IsPullback.lift_snd _ _ _ _

theorem pushEx_left (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) :
    (pushEx Z Fu y i P p hu hp z).left = liftEx Z Fu y i P hu z ≫ Z.m.φ := rfl

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFin

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.FlagMod GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)

attribute [local instance] Over.cartesianMonoidalCategory

section Push

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {π : X' ⟶ X} {F : G'.left ⟶ G.left} {S S' : Type} [CommRing S] [CommRing S']

def tanPush (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' →ₗ[S] TanM (x ≫ π) G where
  toFun v := mkT (pushHom h (overAt x (DualNumber S)) (tv v)) (by
    have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) (tv v)) =
        pushHom h (overAt x (DualNumber S)) (smT x 0 (tv v)) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, tv_mem]
    exact map_one _)
  map_add' u v := tanM_ext (map_mul (pushHom h (overAt x (DualNumber S))) _ _)
  map_smul' a v := tanM_ext (Over.OverMorphism.ext (Category.assoc _ _ _))

theorem tanPush_bijective (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : Function.Bijective (tanPush h x) := by
  have inj : Function.Injective (pushHom h (overAt x (DualNumber S))) := fun p q hpq =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun V => V.left) hpq) ((Over.w p).trans (Over.w q).symm))
  refine ⟨fun u v e => tanM_ext (inj (congrArg tv e)), fun V => ?_⟩
  let p : overAt x (DualNumber S) ⟶ G' :=
    Over.homMk (h.1.lift (tv V).left (overAt x (DualNumber S)).hom (Over.w (tv V))) (h.1.lift_snd _ _ _)
  have hp : pushHom h (overAt x (DualNumber S)) p = tv V := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  refine ⟨mkT p (inj ?_), tanM_ext hp⟩
  have e : smT (x ≫ π) 0 (pushHom h (overAt x (DualNumber S)) p) =
      pushHom h (overAt x (DualNumber S)) (smT x 0 p) := Over.OverMorphism.ext (Category.assoc _ _ _).symm
  rw [← e, hp, map_one]
  exact tv_mem V

def tanEquiv (h : IsGrpPullback G' G π F) (x : Sp S ⟶ X') : TanM x G' ≃ₗ[S] TanM (x ≫ π) G :=
  LinearEquiv.ofBijective _ (tanPush_bijective h x)

theorem tanPull_tanEquiv (h : IsGrpPullback G' G π F) (φ : S →+* S') {x : Sp S ⟶ X'} {x' : Sp S' ⟶ X'}
    (e : spMap φ ≫ x = x') (e' : spMap φ ≫ x ≫ π = x' ≫ π) (v : TanM x G') :
    tanPull φ e' (tanEquiv h x v) = tanEquiv h x' (tanPull φ e v) :=
  tan_ext_left (Category.assoc _ _ _).symm

end Push

theorem ev_pull_g {X X' : Scheme.{0}} {S : Type} [CommRing S] (L : LB X) (π : X' ⟶ X) (z : Sp S ⟶ X')
    (J J' : PUnit → L.ι) (h : ⊤ ≤ z ⁻¹ᵁ ((L.pull π).U J ⊓ (L.pull π).U J'))
    (h' : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit))) :
    ev z _ h ((L.pull π).g J J').val = ev (z ≫ π) _ h' (L.g (J PUnit.unit) (J' PUnit.unit)).val := by
  have le : (L.pull π).U J ⊓ (L.pull π).U J' ≤ π ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => π) J PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => π) J' PUnit.unit))
  have e : (L.pull π).g J J' = res le (pullU π _ (L.g (J PUnit.unit) (J' PUnit.unit))) := by
    show ∏ _k : PUnit, res le (pullU π _ (L.g (J _k) (J' _k))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e, ← ev_appLE z π le h]
  rfl

section Det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l' : Level H}
  {Xo : Moduli D l} {Xo' : Moduli D l'} {c : Coeff l} {c' : Coeff l'} {O O' : Type} [CommRing O] [CommRing O']
  {β : O →+* c.F} {β' : O' →+* c'.F} {Z : Model Xo c β} {Z' : Model Xo' c' β'} {π : Z'.X ⟶ Z.X}
  {F : Z'.t.G.left ⟶ Z.t.G.left} (h : IsGrpPullback Z'.t.G Z.t.G π F) {S : Type} [CommRing S]

end Det

end GlobalTheory.PolFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbedding
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DRFlag GlobalTheory.ProjSpace
open GlobalTheory.FlagMod (ev ev_spMap le_preimage_comp)

namespace GlobalTheory.SubClosure

section General

variable {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] {N : ℕ}

instance subsingleton_sp (K : Type) [Field K] : Subsingleton (Sp K) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

end General

end GlobalTheory.SubClosure
end
end
