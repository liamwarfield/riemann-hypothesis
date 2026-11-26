module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGenericAgree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineDegreeSpecialFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicFrame

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpOnto

theorem isHolTo_slice {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    {X : Scheme.{0}} {B : Set V} {b : V} (hb : b ∈ B) {c : V × V' → (Sp ℂ ⟶ X)}
    (h : IsHolTo (B ×ˢ Set.univ) c) : IsHolTo Set.univ (fun z => c (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hj : Differentiable ℂ (fun z : V' => (b, z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage hj.continuous
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_true, hb, true_and] using h3
  · exact h2.comp hj.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩

theorem isHolTo_const_param {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {c : V' → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ c) :
    IsHolTo (Set.univ ×ˢ Set.univ) (fun p : V × V' => c p.2) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, ?_⟩
  · have h3 := h1.preimage (continuous_snd (X := V) (Y := V'))
    simpa only [Set.preimage_setOf_eq, Set.mem_prod, Set.mem_univ, and_self, true_and] using h3
  · exact h2.comp differentiable_snd.differentiableOn fun z hz => ⟨trivial, hz.2⟩

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
  {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}

theorem isHolTo_ex (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z => (e.ex b z).left) :=
  isHolTo_slice (V := Fin n → ℂ) (V' := Fin g → ℂ) (X := G.left) (b := b) (B := B)
    (c := fun bz => (e.ex bz.1 bz.2).left) hb e.hol

def atPoint (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) :
    FamExp G M (Set.univ : Set (Fin 0 → ℂ)) (fun _ => ψ b) where
  ex _ z := e.ex b z
  add _ _ z w := e.add b hb z w
  hol := isHolTo_const_param (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (e.ex b z).left) (isHolTo_ex e hb)
  diff _ _ a := e.diff b hb a
  log b₀ _ := by
    obtain ⟨V, N, f, L, h1, h2, h3, h4⟩ := e.log b hb
    have hφ : Continuous (fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) := by fun_prop
    have hφ' : Continuous (fun p : (Fin 0 → ℂ) × (Fin g → ℂ) => (b, p.2)) := by fun_prop
    refine ⟨V, N, f, fun p => L (b, p.2), h1, ?_, ?_, ?_⟩
    · exact AnalyticAt.comp (f := fun p : (Fin 0 → ℂ) × (Fin N → ℂ) => (b, p.2)) h2
        (analyticAt_const.prod analyticAt_snd)
    · exact (hφ'.tendsto (b₀, 0)).eventually h3
    · exact (hφ.tendsto (b₀, _)).eventually h4

end GlobalTheory.CompanionTheory.Ar.Flat.ExpOnto

namespace GlobalTheory.CompanionTheory.Ar.Flat

open ExpOnto

theorem famExp_ex_surjective : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ)
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ))
    (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Function.Surjective (e.ex b) := by
  intro R _ G _ _ g n M B ψ e hG b hb
  have hc : IsHolTo (Metric.ball (0 : ℂ) 1) (fun _ : ℂ => spMap (ψ b)) :=
    fun U f => ⟨Metric.isOpen_ball.inter isOpen_const, differentiableOn_const _⟩
  obtain ⟨m, ρ, u, hρ, -, -, hu, -⟩ := GlobalTheory.RelExp.exists_exp_along_disc (Sp R) G (fun _ => spMap (ψ b)) 1 hG one_pos hc
  obtain ⟨hadd, hsurj, hhol, -⟩ := hu 0 (Metric.mem_ball_self hρ)
  obtain ⟨h, -, hh⟩ := exists_linear_lift_of_additive_family R G g 0 M Set.univ (fun _ => ψ b) (atPoint e hb) m Set.univ
    (fun _ z => u 0 z) isOpen_univ subset_rfl (fun _ _ z w => hadd z w)
    (isHolTo_const_param (V := Fin 0 → ℂ) (X := G.left) (c := fun z => (u 0 z).left) hhol)
  intro x
  obtain ⟨z, rfl⟩ := hsurj x
  exact ⟨h 0 z, (hh 0 trivial).1 z⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExponentialSurjectiveSemiabelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_surjective_semiabelian : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSemiAbelian G → ∀ b ∈ B, Function.Surjective (e.ex b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective | exact GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.famExp_ex_surjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPoint
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.KapEquiv

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_kap_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → ∃ ψ : kap Z ≃+* Or.𝔐.Ω₀, spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ ∧ ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Z hgen
  have hb₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have hb₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    have hf : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact RingHom.flat_algebraMap_iff.2 hf
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  have hg : IsGenericPoint (Formalism.L2.Pj.genPt Z) (Z : Set (Xo.XF c)) :=
    Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  have hC : IsCptGen (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) :=
    GlobalTheory.CompanionTheory.Ar.Flat.isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) (Formalism.L2.Pj.genPt Z)
      (GlobalTheory.CompanionTheory.Ar.Flat.eq_genericPoint_of_specializes Z.2 hg)
  have e₁ : GlobalTheory.CompanionTheory.Ar.genPt (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z ≫ Y.j) = Y.j (Formalism.L2.Pj.genPt Z) :=
    congrArg Y.j ((Xo.XF c).fromSpecResidueField_apply (Formalism.L2.Pj.genPt Z) _)
  have e₂ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf := RegAtDom.map_genPt Or.g_over
  have e₃ : Or.𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ) = GlobalTheory.CompanionTheory.Ar.genPt Or.𝔐.ξ₀ := RegAtDom.map_genPt Or.𝔐.fn_over
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.FlagPull.exists_iso hC Or.𝔐.gen₀ (e₁.trans (hgen.symm.trans (e₂.symm.trans e₃)))
  refine ⟨ψ, hψ, ?_⟩
  have hsY : Y.j ≫ Y.s = Formalism.L2.Pj.strK ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
    (Spec.map_preimage _).symm
  have hfn : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
  let i : c.F →+* RM.Ω := (Or.𝔐.fn.comp ψ.toRingHom).comp (algebraMap c.F (Formalism.L2.Pj.kap Z))
  have e0 : i.comp (algebraMap (𝓞 c.F) c.F) = Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have hS : spMap (i.comp (algebraMap (𝓞 c.F) c.F)) = spMap (Or.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      refine Eq.trans ?_ Or.𝔐.cst_over
      have h3 : Or.𝔐.ξ ≫ Or.𝔐.f ≫ Y.s = spMap Or.𝔐.fn ≫ spMap ψ.toRingHom ≫
          (Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
        rw [← Category.assoc, hfn, ← hψ]
        simp only [Category.assoc]
        rw [hsY]
      rw [h3, h1]
      simp only [i, spMap_comp_eq, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hS)
  have e4 : i = Or.𝔐.cst := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  intro a
  exact congrArg (fun φ : c.F →+* RM.Ω => φ a) e4

end GlobalTheory.CompanionTheory.Ar.KapEquiv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPointStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_component_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → ∃ ψ : kap Z ≃+* Or.𝔐.Ω₀, spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ ∧ ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv | exact GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeValuationAgree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeValuationAgree
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.COrder

theorem order_on_component : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q : ℕ) (𝓗 : HodgeLat L ρ bar (p + q)) (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V) (α κ : Ω) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → ConstClosed O Ω → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Ω).range) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w → Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u → 𝓗.DegZero σ (algebraMap O Ω ϖ) → IsLineGenOn (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (α • exteriorPower.ιMulti Ω p v) (κ • exteriorPower.ιMulti Ω q w) (genFibre O ξ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ x : Cpt ξ, OrderAt (detLat (𝓗.quot σ) u) (α / κ) (algebraMap O Ω ϖ) M a x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q 𝓗 σ σ' v w u α κ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hc hσ h1 h2
    hv hvs hw hws had hdz hgen
  obtain ⟨hu, husp, -⟩ := AdaptedSpan.adapted_span X Ω ξ E V L ρ bar p q (p + q) 𝓗 σ σ' v w u h1 h2 hv hvs hw hws had
  have hO : ∀ (x : Cpt ξ) (o : O), algebraMap O Ω o ∈ regAt ξ x := fun x o =>
    (ConstReg.regular_const X Ω ξ O s hs x o).1
  have hσr : ∀ (x : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ x := fun x a => by
    obtain ⟨o, ho⟩ := hσ a
    exact ho ▸ hO x o
  have hinv : ∀ x ∈ genFibre O ξ, ∀ b : 𝓞 E, (σ (b : E))⁻¹ ∈ regAt ξ x := fun x hx b => by
    obtain ⟨o, ho⟩ := hσ b
    rw [← ho]
    by_cases h0 : o = 0
    · rw [h0, map_zero, inv_zero]
      exact zero_mem _
    · exact (hx o h0).2.2
  refine GlobalTheory.T.line_degree_special_fibre X Ω ξ O s ϖ hϖ hinj hs hg hn (GlobalTheory.T.isConnected_zeroSet_uniformizer X Ω ξ O s ϖ hϖ hinj hs hg hc) _ _
    (𝓗.det_isVB σ hσr hu husp) (hdz u hu husp) fun x hx => ?_
  obtain ⟨ha, hb, hco⟩ := hgen
  have hα : α ≠ 0 := left_ne_zero_of_smul ha
  have hκ : κ ≠ 0 := left_ne_zero_of_smul hb
  refine (GenAgree.generic_agree X Ω ξ E V L ρ bar p q 𝓗 σ σ' v w u x (α / κ) hg h1 h2 (fun a => ?_)
    hv hvs hw hws had).2 ⟨div_ne_zero hα hκ, ?_⟩
  · obtain ⟨y, z, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    have e : ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = (c : E) := fun _ => rfl
    rw [e, e, map_div₀, map_div₀, h1, h1, div_eq_mul_inv, div_eq_mul_inv]
    exact ⟨mul_mem (hσr x _) (hinv x hx _), mul_mem (hσr x _) (hinv x hx _)⟩
  · obtain ⟨a', b', ha', hb', hA, hB, e⟩ := hco x hx
    rw [one_mul] at e
    subst e
    refine ⟨a' * α, a' * κ, mul_ne_zero ha' hα, mul_ne_zero ha' hκ, by rw [hA, smul_smul], by rw [hB, smul_smul], ?_⟩
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.COrder
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeValuationAgreeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_valuation_agree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q : ℕ) (𝓗 : HodgeLat L ρ bar (p + q)) (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V) (α κ : Ω) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → ConstClosed O Ω → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Ω).range) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w → Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u → 𝓗.DegZero σ (algebraMap O Ω ϖ) → IsLineGenOn (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (α • exteriorPower.ιMulti Ω p v) (κ • exteriorPower.ιMulti Ω q w) (genFibre O ξ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ x : Cpt ξ, OrderAt (detLat (𝓗.quot σ) u) (α / κ) (algebraMap O Ω ϖ) M a x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.COrder.order_on_component | exact GlobalTheory.CompanionTheory.Ar.Flat.COrder.order_on_component | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.COrder.order_on_component <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHolds
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FinAll

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem iotaMulti_coe_eq_det_smul {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {r : ℕ}
    {S : Submodule R M} (c : Module.Basis (Fin r) R S) (v : Fin r → S) :
    exteriorPower.ιMulti R r (fun i => (v i : M)) =
      c.det v • exteriorPower.ιMulti R r (fun i => (c i : M)) := by
  have h : (exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype =
      c.det.smulRight (exteriorPower.ιMulti R r (fun i => (c i : M))) := by
    refine Module.Basis.ext_alternating c fun i hi => ?_
    let σ : Equiv.Perm (Fin r) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change ((exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype) (c ∘ σ) =
      c.det (c ∘ σ) • exteriorPower.ιMulti R r (fun i => (c i : M))
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]
    rfl
  exact DFunLike.congr_fun h v

theorem exists_smul_iotaMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (S : Submodule Ω V) {n : ℕ} (v : Fin n → V)
    (a : ⋀[Ω]^n V) (x : Cpt ξ) (α : Ω) (hα : α ≠ 0) (hv : LinearIndependent Ω v)
    (hS : Submodule.span Ω (Set.range v) = S)
    (h : (L.inter S).wedge n x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ c : Ω, a = c • exteriorPower.ιMulti Ω n v := by
  have hmem : α • a ∈ (L.inter S).wedge n x := by rw [h]; exact Submodule.mem_span_singleton_self _
  have key : ∀ y ∈ (L.inter S).wedge n x, ∃ c : Ω, y = c • exteriorPower.ιMulti Ω n v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      let e : Module.Basis (Fin n) Ω (Submodule.span Ω (Set.range v)) := Module.Basis.span hv
      let b' : Fin n → Submodule.span Ω (Set.range v) := fun i => ⟨b i, by rw [hS]; exact (hb i).2⟩
      refine ⟨e.det b', ?_⟩
      have h1 := iotaMulti_coe_eq_det_smul e b'
      have h2 : (fun i => ((e i : Submodule.span Ω (Set.range v)) : V)) = v := by
        funext i; show ((Module.Basis.span hv i : Submodule.span Ω (Set.range v)) : V) = v i
        rw [Module.Basis.span_apply]
      rw [h2] at h1
      exact h1
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨d, rfl⟩ := hz
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r y _ hy =>
      obtain ⟨c, rfl⟩ := hy
      exact ⟨(r : Ω) * c, by rw [Subring.smul_def, smul_smul]⟩
  obtain ⟨c, hc⟩ := key _ hmem
  refine ⟨α⁻¹ * c, ?_⟩
  rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hα, one_smul]

theorem norm_le_one_of_isIntegral (p : Nat.Primes) (R : Type) [CommRing R] (κ : R →+* ℂ_[p]) (x : R)
    (hx : IsIntegral ℤ x) : ‖κ x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (κ x) := by
    convert map_isIntegral_int κ hx using 1 <;> first | exact Subsingleton.elim _ _ | rfl
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (κ x) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖κ x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem mem_or_inv_mem {F : Type} [Field F] {O : Type} [CommRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) (x : F) : x ∈ β.range ∨ x⁻¹ ∈ β.range := by
  by_cases hx : ‖κ x‖ ≤ 1
  · exact Or.inl ((h x).1 hx)
  · right
    apply (h _).1
    rw [map_inv₀, norm_inv]
    push_neg at hx
    exact inv_le_one_of_one_le₀ hx.le

theorem exists_frac {F : Type} [Field F] {O : Type} [CommRing O] [IsDomain O] (β : O →+* F)
    (hr : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) (x : F) : ∃ a b : O, b ≠ 0 ∧ x * β b = β a := by
  rcases hr x with ⟨a, rfl⟩ | ⟨b, hb⟩
  · exact ⟨a, 1, one_ne_zero, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, one_ne_zero, by simp [hx]⟩
    · refine ⟨1, b, ?_, ?_⟩
      · rintro rfl; simp at hb; exact hx hb.symm
      · rw [hb, mul_inv_cancel₀ hx, map_one]

theorem norm_natCast_prime (p : Nat.Primes) : ‖(((p : ℕ) : ℂ_[p]))‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[(p : ℕ)] ℂ_[(p : ℕ)]) (p : ℕ), norm_algebraMap', Padic.norm_p]

theorem dvd_prime {F : Type} [Field F] [CharZero F] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) {ϖ : O} (hϖ : Irreducible ϖ) :
    ϖ ∣ ((p : ℕ) : O) := by
  have hnu : ¬ IsUnit ((p : ℕ) : O) := by
    rintro ⟨u, hu⟩
    have hmem : ((p : ℕ) : F)⁻¹ ∈ β.range := by
      refine ⟨(u⁻¹ : Oˣ), ?_⟩
      have h1 : β (u : O) * β ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      rw [hu, map_natCast] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hle := (h _).2 hmem
    rw [map_inv₀, map_natCast, norm_inv, norm_natCast_prime, inv_inv] at hle
    have h1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    linarith
  have hm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

theorem constClosed_of_isGeom {F : Type} [Field F] {Ω : Type} [Field Ω] {O : Type} [CommRing O]
    (β : O →+* F) (inc : F →+* Ω) (hβ : Function.Injective β)
    (hfr : ∀ x : F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a)
    (hg : ∀ x : Ω, (∃ f : Polynomial F, f ≠ 0 ∧ f.eval₂ inc x = 0) → x ∈ Set.range inc) :
    @ConstClosed O Ω _ _ (inc.comp β).toAlgebra := by
  letI : Algebra O Ω := (inc.comp β).toAlgebra
  intro a ha
  obtain ⟨f, hf0, hfa⟩ := ha
  obtain ⟨y, rfl⟩ := hg a ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by
    rw [Polynomial.eval₂_map]; exact hfa⟩
  obtain ⟨x', y', hy', e⟩ := hfr y
  refine ⟨x', y', hy', ?_⟩
  show inc y * inc (β y') = inc (β x')
  rw [← map_mul, e]

theorem exists_basis_of_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) {n : ℕ} (h : Module.finrank K S = n) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  have hli : LinearIndependent K (S.subtype ∘ b) := b.linearIndependent.map' S.subtype S.ker_subtype
  refine ⟨S.subtype ∘ b, hli, ?_⟩
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem finConstAll : FinConstAll := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ p κ φ hτ hβ hnorm hsplit hN3 hgeom hflat hline
  have hr := mem_or_inv_mem β κ hnorm
  have hfr := exists_frac β hr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ ((p : ℕ) : O) := dvd_prime β κ hnorm hϖ
  obtain ⟨hprop, hnormal, hover, hgf, hfd, hrk, hrk'⟩ :=
    GlobalTheory.T.proper_normal_compactification E H D l Xo c O β Y U Z τ hβ hfr hτ
  letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  haveI := hfd
  haveI := hprop
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  let σ : E →+* Z.Ω := Z.inc.comp (τ.codRestrict c.F.toSubfield (c.conj τ) : E →+* c.F)
  let σ' : E →+* Z.Ω := Z.inc.comp
    ((ComplexEmbedding.conjugate τ).codRestrict c.F.toSubfield (c.conj _) : E →+* c.F)
  have hσ : ∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b) := fun b => rfl
  have hbar : ∀ a : 𝓞 E, σ' (a : E) = σ (H.bar a : 𝓞 E) := by
    intro a
    show Z.inc _ = Z.inc _
    congr 1
    apply Subtype.ext
    show (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have hinv : ∀ a, H.bar (H.bar a) = a := by
    intro a
    apply RingOfIntegers.ext
    apply τ.injective
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, H.bar_eq, IsCMField.complexEmbedding_complexConj,
      Complex.conj_conj]
  have heig : HT.eigSp Z.ρ σ = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) := rfl
  have heig' : HT.eigSp Z.ρ σ' = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) := rfl
  obtain ⟨v, hvli, hvsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ) (heig ▸ hrk)
  obtain ⟨w, hwli, hwsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ') (heig' ▸ hrk')
  obtain ⟨𝓗, hdeg⟩ := GlobalTheory.T.eigen_line_p_adic_bound E H D l Xo c O β Y U Z τ ϖ (p : ℕ) hϖ p.2 hdvd hβ hr hsplit hN3
  obtain ⟨u, hu, -, -⟩ := GlobalTheory.T.hermitian_signature_basis E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar σ σ' D.p D.q v w 𝓗.act_fst 𝓗.act_inr
    hbar hinv hvli hvsp hwli hwsp
  obtain ⟨-, a, b, ⟨ha0, hb0, hco⟩, hrep⟩ := hflat
  let x₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩
  have hx₀ : x₀ ∈ Z.genFib := ⟨Y.jQ (genPt Z.ξ₀), rfl⟩
  obtain ⟨α₁, β₁, hα₁, hβ₁, hA, hB, -⟩ := hco x₀ hx₀
  obtain ⟨α, rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ) v a x₀ α₁ hα₁ hvli hvsp hA
  obtain ⟨κ', rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ') w b x₀ β₁ hβ₁ hwli hwsp hB
  have hκ' : κ' ≠ 0 := fun h => hb0 (by rw [h, zero_smul])
  have hgfe : Z.genFib = genFibre O (Z.ξ₀ ≫ Y.j) := Set.ext fun x => hgf x
  have hline' : IsLineGenOn (Z.M.lat.inter (HT.eigSp Z.ρ σ)) (Z.M.lat.inter (HT.eigSp Z.ρ σ')) D.p D.q
      (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w)
      (genFibre O (Z.ξ₀ ≫ Y.j)) := by
    rw [← hgfe]; exact ⟨ha0, hb0, hco⟩
  have hinjO : Function.Injective (algebraMap O Z.Ω) := Z.inc.injective.comp hβ
  have hσrange : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Z.Ω).range := by
    intro a
    obtain ⟨o, ho⟩ := (hnorm (tauIn c τ a)).1
      (norm_le_one_of_isIntegral p (𝓞 E) (κ.comp (tauIn c τ)) a (RingOfIntegers.isIntegral a))
    exact ⟨o, by show Z.inc (β o) = Z.inc (tauIn c τ a); rw [ho]⟩
  have hcc : ConstClosed O Z.Ω := constClosed_of_isGeom β Z.inc hβ hfr hgeom
  obtain ⟨M, k, hM, hord⟩ := GlobalTheory.T.hodge_lattice_valuation_agree Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E Z.V Z.M.lat Z.ρ H.bar D.p D.q 𝓗 σ σ'
    v w u α κ' O Y.s ϖ hϖ hinjO hover Z.gen hnormal hcc hσrange hbar hinv hvli hvsp hwli hwsp hu (hdeg σ) hline'
  exact GlobalTheory.T.eigen_line_p_adic_frame E H D l Xo c O β Y U Z τ ϖ p κ φ 𝓗 σ v w u α κ' M k hτ hϖ hβ hnorm hσ hvli hvsp hwli
    (hwsp.trans heig') hu hM hord hκ' hrep hline

end GlobalTheory.CompanionTheory.Ar.Flat.FinAll
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_constant_all_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConstAll := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll | exact GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScaling
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FieldPt

section Charts

variable {K : Type} [Field K] {Jx : Type} [Fintype Jx]
variable {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
variable {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop}
variable {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (Jx → Sˣ) → pts S → pts S → Prop}

theorem map_zpow_units {A B T : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] [CommRing T]
    [Algebra K T] (g : A →ₐ[K] T) (g' : B →ₐ[K] T) (x : Aˣ) (x' : Bˣ) (h : g (x : A) = g' (x' : B)) (n : ℤ) :
    g ((x ^ n : Aˣ) : A) = g' ((x' ^ n : Bˣ) : B) := by
  have e : Units.map (g : A →* T) x = Units.map (g' : B →* T) x' := Units.ext h
  have e' := congrArg (fun u : Tˣ => ((u ^ n : Tˣ) : T)) e
  simp only [← map_zpow] at e'
  exact e'

theorem wtAllZ_of_borChart (h : BorChart pts mapR borR) (e : Jx → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : Jx → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = (∏ i, ((t i ^ e i : (p.R)ˣ) : p.R)) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : Jx → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dite_eq_left hy, dite_eq_left hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  rw [Units.coe_prod, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ => map_zpow_units cB (locM K m) (tB i) (t i) (e3 i) (e i)

end Charts

theorem evR_frBor_secZ_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : GlobalTheory.CompanionTheory.Ar.Rec.WZ E) (f : Rul Xo c) (L : Type) [Field L] [Algebra c.F L] (t : Ix Dw → Lˣ) (y y' : FrPt Xo c L), f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a → FrBor t y y' → evR Xo c f y' = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c a f L _ _ t y y' hf hb
  obtain ⟨⟨-, -, hB, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  exact wtAllZ_of_borChart hB (GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a) hf.1 hf.2 L t y y' (hA L y) (hA L y') hb

end GlobalTheory.CompanionTheory.Ar.Rec.FieldPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScalingStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_borel_section_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : GlobalTheory.CompanionTheory.Ar.Rec.WZ E) (f : Rul Xo c) (L : Type) [Field L] [Algebra c.F L] (t : Ix Dw → Lˣ) (y y' : FrPt Xo c L), f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a → FrBor t y y' → evR Xo c f y' = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * evR Xo c f y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field | exact GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field <;> assumption)
end
end
