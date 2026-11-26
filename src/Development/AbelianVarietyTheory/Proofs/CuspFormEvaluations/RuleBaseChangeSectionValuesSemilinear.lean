module

public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormNormaliserEqHalfDegreeLog
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardCompUnfLe
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of ruleUp_mem_sec evR_ruleUp)

theorem rulBC_sec_val_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, rulBC hle f ∈ sec Xo c' a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h)) ∧ (∀ (t : c.F) (f g : Rul Xo c), rulBC hle (t • f + g) = incF c c' hle t • rulBC hle f + rulBC hle g) := by
  intro E _ _ _ H Dw l Xo c c' hle
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : HasBC Xo c := hasBC_of hS
  refine ⟨fun a n f hf => ⟨ruleUp_mem_sec hle hWD hBC hf, ?_⟩, fun t f g => ?_⟩
  · intro S _ A _ h y
    obtain rfl : A = resAlg hle S := Algebra.algebra_ext _ _ fun x => (h x).symm
    exact evR_ruleUp hle hWD hBC hf.1 y
  · funext p y
    letI := resAlg hle p.R
    have h1 : evR Xo c (t • f + g) (y.res hle (fun _ => rfl)) =
        algebraMap c.F p.R t * evR Xo c f (y.res hle (fun _ => rfl)) + evR Xo c g (y.res hle (fun _ => rfl)) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    show _ = incF c c' hle t • rulBC hle f p y + rulBC hle g p y
    rw [Algebra.smul_def]
    rfl

end GlobalTheory.FieldBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinearStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ruleBaseChange_section_values_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, rulBC hle f ∈ sec Xo c' a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h)) ∧ (∀ (t : c.F) (f g : Rul Xo c), rulBC hle (t • f + g) = incF c c' hle t • rulBC hle f + rulBC hle g) := by
  first | exact @GlobalTheory.FieldBC.rulBC_sec_val_linear | exact GlobalTheory.FieldBC.rulBC_sec_val_linear | (intros; apply GlobalTheory.FieldBC.rulBC_sec_val_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.BasicNotions

theorem actLev_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) : ActLev (Xo := Xo) c' lev := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    obtain ⟨z, hz⟩ := hL.total g S (y.res hle h)
    exact ⟨z.ext hle h, hz⟩
  · intro g S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.func g S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.one S (y.res hle h)
  · intro g g' S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.mul g g' S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro g S T _ _ _ _ φ y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    letI := resAlg hle T
    have hS : AlgOver c c' hle S := fun _ => rfl
    have hT : AlgOver c c' hle T := fun _ => rfl
    let ψ : S →ₐ[c.F] T := { φ.toRingHom with commutes' := fun x => φ.commutes _ }
    exact hL.nat g S T ψ (y.res hle hS) (y'.res hle hS) (z.res hle hT) (z'.res hle hT) h₀ h₁ h₂
  · intro g S _ _ t y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.bor g S t (y.res hle h) (y'.res hle h) (z.res hle h) (z'.res hle h) h₀ h₁ h₂

theorem actLev_and_actBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (G : Type) [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) :
    ActLev (Xo := Xo) c' lev ∧ ActBC hle (actLev (Xo := Xo) c lev) (actLev (Xo := Xo) c' lev) :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := fun c => GlobalTheory.Frames.chartCoverF_of_secBaseChange hS D.host.E H Dw l Xo c
  ⟨actLev_of_le hle lev hL, actBC_of hle lev (evalWD_fr (frChartF_of (hc c))) (evalWD_fr (frChartF_of (hc c'))) hL
    (actLev_of_le hle lev hL)⟩

end GlobalTheory.FieldBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SecBCAndCuspBC
set_option autoImplicit false

namespace GlobalTheory.FieldBC

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem secBC_and_cuspBC (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) :
    SecBC Xo hle ∧ ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), CuspBC hle U :=
  ⟨GlobalTheory.SecFieldChange.secBC_holds hle, fun _ U => GlobalTheory.SecFieldChange.cuspBC_holds hle U⟩

end GlobalTheory.FieldBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumUnique

theorem eq_of_forall_algClosed {K R : Type} [Field K] [CommRing R] [Algebra K R] [IsReduced R] (u v : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : R →ₐ[K] k), φ u = φ v) : u = v := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  let ψ : R →+* AlgebraicClosure J.ResidueField :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).comp (algebraMap R J.ResidueField)
  letI : Algebra K (AlgebraicClosure J.ResidueField) := (ψ.comp (algebraMap K R)).toAlgebra
  have e : ψ u = ψ v := h (AlgebraicClosure J.ResidueField) { ψ with commutes' := fun _ => rfl }
  have e' : algebraMap R J.ResidueField u = algebraMap R J.ResidueField v :=
    (algebraMap J.ResidueField (AlgebraicClosure J.ResidueField)).injective e
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, e', sub_self]

theorem sec_eq_of_geometric {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f f' : Rul Xo c} (hf : f ∈ sec Xo c a m)
    (hf' : f' ∈ sec Xo c a m)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c f' y) :
    f = f' := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : GlobalTheory.CoefChangeCompare.ValueWD Xo c :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hBC : GlobalTheory.CoefChangeCompare.HasBC Xo c := GlobalTheory.CoefChangeCompare.hasBC_of hS
  funext p y
  haveI := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  refine eq_of_forall_algClosed (K := c.F) _ _ fun k _ _ _ φ => ?_
  obtain ⟨z, hz⟩ := hBC p.R k φ y
  rw [← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf.1 hz, ← GlobalTheory.CoefChangeCompare.evR_of_map hWD hf'.1 hz]
  exact h k z

theorem isThClsD_unique : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F), d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ k, (La k).Unimod ∧ (La k).TrivAt d.l₂.M ∧ (La k).LevOK (Nc k) d.l₂.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ (x : Cl → Vs) (a' : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a' m, ∀ f' ∈ sec Xo c a' m, IsThClsD Xo c d w La Nc gam vol ep io x f → IsThClsD Xo c d w La Nc gam vol ep io x f' → f = f' := by
  intro hC E _ _ _ H Dw l Xo c n d Cl _ w La Nc gam vol ep Vs _ _ io hd hnab hLa a hio x a' m f hf f' hf' h h'
  obtain ⟨_, hnab⟩ := hnab
  refine sec_eq_of_geometric hf hf' fun k _ _ _ y => ?_
  letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have hk : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := fun a => by
    show algebraMap c.F k (d.eF.symm (d.eF a)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := h k hk y y₂ hy
  obtain ⟨v', hv', e'⟩ := h' k hk y y₂ hy
  have hvv : v = v' := funext fun cl =>
    ((GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n
      (La cl) (Nc cl) (hLa cl).1 (hLa cl).2.1 (hLa cl).2.2 a _
      ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hio (x cl))) (fun q => d.eF (w cl q)) 1).1 k y₂).unique
      (hv cl) (hv' cl)
  rw [e, e', hvv]

end GlobalTheory.ClassSumUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinear
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

namespace Rule

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {ta : c.F ≃+* c.F}

theorem fixes_symm (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => by rw [RingEquiv.symm_apply_eq, h.emb], fun a => by rw [RingEquiv.symm_apply_eq, h.base]⟩

def twHom (ta : c.F ≃+* c.F) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) : Tw ta S →ₐ[c.F] Tw ta T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (ta a) }

def untwHom {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] Tw ta T) : Tw ta.symm S →ₐ[c.F] T :=
  { φ.toRingHom with
    commutes' := fun a => (φ.commutes (ta.symm a)).trans
      (congrArg (algebraMap c.F T) (ta.apply_symm_apply a)) }

theorem fromT_tw_test (h : Fixes c ta) (hA : AllTest Xo c) (p : TRing c.F) (y : FrPt Xo c p.R) :
    FromT (twPt h y) := by
  haveI : IsReduced (Tw ta p.R) := ((GlobalTheory.reduced_finiteType_iff_testRing c.F).2 p).2
  exact hA _ _

theorem fromT_of_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y) (hm : FrMap φ y z) : FromT z := by
  obtain ⟨p, ψ, y₀, h₀⟩ := hy
  exact ⟨p, _, y₀, map_trans ψ φ h₀ hm⟩

theorem frMap_tw (h : Fixes c ta) {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap φ y z) :
    FrMap (twHom ta φ) (twPt h y) (twPt h z) := hm

theorem fromT_of_tw (h : Fixes c ta) (hA : AllTest Xo c) {S : Type} [CommRing S] [Algebra c.F S]
    {y : FrPt Xo c S} (hy : FromT (twPt h y)) : FromT y := by
  obtain ⟨p, φ, y₀, h₀⟩ := hy
  have h₁ : FrMap (untwHom φ) (twPt (fixes_symm h) y₀) y := h₀
  exact fromT_of_map (fromT_tw_test (fixes_symm h) hA p y₀) h₁

theorem evR_galRul (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) {f : Rul Xo c} (hf : Natural c f)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, hm, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_tw_test h hA q y₀) (frMap_tw h hm)]
    rfl
  · rw [evR_not hy, evR_not (fun h' => hy (fromT_of_tw h hA h'))]
    rfl

theorem galRul_mem_sec (h : Fixes c ta) (hWD : ValueWD Xo c) (hA : AllTest Xo c) (hB : BorChartF Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : galRul h f ∈ sec Xo c a n := by
  refine ⟨fun p q φ y z hm => ?_, fun q t y y' hb => ?_⟩
  · exact evR_map hWD hf.1 (fromT_tw_test h hA p y) (frMap_tw h hm)
  · have hb' : FrBor (S := Tw ta q.R) t (twPt h y) (twPt h y') := hb
    have h3 : evR Xo c f (twPt h y') = _ * evR Xo c f (twPt h y) :=
      wtAll_of_borChart hB (ex Dw a n) hf.1 hf.2 (Tw ta q.R) _ _ _ (fromT_tw_test h hA q y)
        (fromT_tw_test h hA q y') hb'
    exact h3

end Rule

theorem galRul_sec_val_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  intro E _ _ _ H Dw l Xo c ta h
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hWD : ValueWD Xo c := evalWD_fr (frChartF_of hc)
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hB : BorChartF Xo c := borChartF_of_cover hc
  refine ⟨fun a n f hf => ⟨Rule.galRul_mem_sec h hWD hA hB hf, fun S _ _ y => Rule.evR_galRul h hWD hA hf.1 y⟩,
    fun t f g => ?_, ?_⟩
  · funext p y
    have h1 : evR Xo c (t • f + g) (twPt h y) =
        algebraMap c.F (Tw ta p.R) t * evR Xo c f (twPt h y) + evR Xo c g (twPt h y) := by
      unfold evR
      rw [evalAt_add, evalAt_smul]
    refine h1.trans ?_
    show _ = ta t • galRul h f p y + galRul h g p y
    rw [Algebra.smul_def]
    rfl
  · intro c₀ hle hfix a n m as fs f hf hbc S _ A _ ho y
    letI : Algebra c₀.F (Tw ta S) := A
    have ho' : AlgOver c₀ c hle (Tw ta S) := fun x =>
      (congrArg (algebraMap c.F S) (hfix x)).trans (ho x)
    rw [Rule.evR_galRul h hWD hA hf.1 y]
    exact hbc (Tw ta S) ho' (twPt h y)

end GlobalTheory.GalTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinearStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSection_values_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  first | exact @GlobalTheory.GalTw.galRul_sec_val_semilinear | exact GlobalTheory.GalTw.galRul_sec_val_semilinear | (intros; apply GlobalTheory.GalTw.galRul_sec_val_semilinear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

private theorem log_norm_sOf_eq_DF_log_add_log_pPow (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ) :
    Real.log ‖σ (sOf B hinj EX w : B.KO)‖ =
      (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) := by
  obtain ⟨hnn, hlog⟩ := GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ
  have hp := ((GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w).2.2.2.2.2 (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)).1
  have hσ : σ (sOf B hinj EX w : B.KO) = σ (nnW B hinj EX w : B.KO) *
      (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℂ) := by
    unfold sOf
    push_cast
    rw [map_mul, map_natCast]
  have hne : σ (nnW B hinj EX w : B.KO) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hnn
  have hpne : ((pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℕ) : ℝ) ≠ 0 := by
    have : 0 < pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) := hp
    positivity
  rw [hσ, norm_mul, Complex.norm_natCast, Real.log_mul (norm_ne_zero_iff.mpr hne) hpne, hlog]

theorem sOf_ne_zero_and_log_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j), sOf B hinj EX w ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ≤ lamStar D * w.size := by
  intro D B hinj EX j w
  obtain ⟨_, _, hB0, hA0, hP, hpp⟩ := GlobalTheory.T.ramifiedPrimePowers_size_bounds D j w
  obtain ⟨hp1, hplog⟩ := hpp (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w)
  have hlp0 : 0 ≤ Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hlpB : Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ) ≤
      ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := by
    rw [hplog]; exact hP
  have hDF : (0 : ℝ) ≤ WeightAlgebra.DF w := Nat.cast_nonneg _

  have hsz : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have key : w.size = (WeightAlgebra.DF w : ℝ) +
        (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) + 1 := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF WeightAlgebra.degP
      push_cast
      ring
    have : (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      positivity
    linarith

  have hqq : Real.log (qq D : ℝ) ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rcases Nat.eq_zero_or_pos (qq D) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; exact hA0
    · have h0 : qq D ≤ D.host.g 0 := min_le_left _ _
      have h1 : qq D ≤ D.host.g 1 := min_le_right _ _
      have hle : qq D ≤ D.host.g 0 * D.host.g 1 :=
        h0.trans (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le h h1))
      have hcast : (qq D : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := by exact_mod_cast hle
      exact Real.log_le_log (by exact_mod_cast h) hcast
  refine ⟨?_, fun σ => ?_⟩
  · unfold sOf
    refine mul_ne_zero ?_ ?_
    · obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
      exact (GlobalTheory.T.log_norm_normaliser_eq_half_degree_log D B hinj EX j w σ).1
    · have : pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) ≠ 0 := by omega
      exact_mod_cast this
  · rw [log_norm_sOf_eq_DF_log_add_log_pPow D B hinj EX j w σ]
    have hA : (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D : ℝ) ≤
        (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hqq (by positivity)
    have hA1 : 0 ≤ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by positivity
    have hL : lamStar D = Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
        Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) := rfl
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    calc (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
          Real.log (pPow D (c2 D w) (Formalism.MainNotions.DIV.Cons.cHalf w) (Formalism.MainNotions.DIV.Cons.cHalf w) : ℝ)
        ≤ ((WeightAlgebra.DF w : ℝ) + 1) * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) := by
          nlinarith [mul_nonneg hDF hA0]
      _ ≤ w.size * (Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
            Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d)) :=
          mul_le_mul_of_nonneg_right hsz (by linarith)
      _ = lamStar D * w.size := by rw [hL]; ring

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLatticeWeightScalarNeZeroAndLogBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLatticeWeightScalar_ne_zero_and_log_bounds : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j), sOf B hinj EX w ≠ 0 ∧ ∀ σ : B.KO →+* ℂ, 0 ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log (qq D) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ∧ Real.log ‖σ (sOf B hinj EX w : B.KO)‖ ≤ lamStar D * w.size := by
  first | exact @GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds | exact GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds | (intros; apply GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyHeightOneSpectrumRingOfIntegers
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem nonempty_heightOneSpectrum_ringOfIntegers (K : Type) [Field K] [NumberField K] :
    Nonempty (HeightOneSpectrum (𝓞 K)) := by

  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩⟩

theorem shareRhoP_of_anFacts : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (CR c : ℝ) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T (WeightFamilies.MggK B CR T c j ka) xs → 2 ≤ WeightFamilies.dimY D j → 11 * WeightFamilies.dimY D j ^ 2 ≤ T → LatAt B j ka → ShareRhoP (D := D) (j := j) T (WeightFamilies.rhoP B CR T c j ka) (X.rk ka (B.Mlat j ka)) := by
  intro D B P j X ka wL wF N w R t T CR c δ xs hA hD hT hL
  obtain ⟨la⟩ := nonempty_heightOneSpectrum_ringOfIntegers B.KO

  have hdim : ∀ M : Submodule B.KO (B.Cusp j ka),
      Module.finrank ℂ (R.sp ka M) = Module.finrank B.KO M := fun M =>
    ((GlobalTheory.T.genericSections_polynomial_dictionary D B P j X R la N wL w t).2.2.2.2.2.2.2 ka M).2
  have hspan : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    Submodule.IsFullLattice.span_eq_top (self := hL)

  have hd : X.rk ka (B.Mlat j ka) = Module.finrank B.KO (B.Cusp j ka) := by
    unfold PJ.rk
    rw [hspan, finrank_top]
  have hup : Module.finrank ℂ (R.sp ka Set.univ) = Module.finrank B.KO (B.Cusp j ka) := by
    have h := hdim ⊤
    rwa [Submodule.top_coe, finrank_top] at h

  have hsum := Submodule.finrank_quotient_add_finrank (WeightFamilies.MggK B CR T c j ka)
  have hq := rhoP_eq_finrank B CR T c j ka hspan
  have hlo := hA.lower
  rw [hdim] at hlo
  have key := (GlobalTheory.T.card_exponents_and_choose_ratio_bounds_pair (WeightFamilies.dimY D j) T).2 δ (X.rk ka (B.Mlat j ka)) (WeightFamilies.rhoP B CR T c j ka) hD hT
    (by rw [hd, ← hup]; exact hA.upper)
  exact key.2 (by rw [hq, hd, ← hsum]; omega)

end GlobalTheory.Shares
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardComponentsLeAtGoodEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardComponentsLeAtGoodEmbedding
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_card_comp_le : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * Zb D large₂ ^ 2 := by
  intro D T h large₂ j hj w hP h2 hrn h16 σ hσ
  obtain ⟨hg, hlrd, hd, hcc, hf, -, -, -, hn⟩ := hP
  obtain ⟨-, -, -, -, -, hfd, hdE, -, -, -, hsk, hne, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L h2 hlrd hd hcc
  obtain ⟨AA, hFG, hA, hdual⟩ := GlobalTheory.T.principalDatum_fg_perfect_tracePairing D
  obtain ⟨-, -, hM, -, -, -, hJ⟩ := GlobalTheory.T.numerical_consequences_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hrL : Real.log D.R.r ≤ large₂.sc.L :=
    le_trans (Real.log_le_log (by exact_mod_cast hr) (by exact_mod_cast hrn)) hn
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    rcases Nat.eq_zero_or_pos (D.host.g 0) with a | a
    · rw [a]; simp; linarith
    rcases Nat.eq_zero_or_pos (D.host.g 1) with b | b
    · rw [b]; simp; linarith
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le GlobalTheory.T.hasse_norm_theorem_quadratic_extension GlobalTheory.T.thetaUniformisation_complexAbelianVariety GlobalTheory.T.abelianScheme_laws_unconditional.1 D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    D.host.xi0 AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact_mod_cast h16) h2 hdE hrL
    (by rw [hfd]; exact_mod_cast hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.RunIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardComponentsLeAtGoodEmbeddingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_card_components_le_at_good_embedding : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * Zb D large₂ ^ 2 := by
  first | exact @GlobalTheory.RunIn.log_card_comp_le | exact GlobalTheory.RunIn.log_card_comp_le | (intros; apply GlobalTheory.RunIn.log_card_comp_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoCommonZeroOfReadings
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameZero

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  classical
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  haveI := hM
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let g : (A ⧸ M) →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f : A →ₐ[K] ℂ := g.comp (Ideal.Quotient.mkₐ K M)
  refine ⟨⟨(f : A →+* ℂ), fun r => f.commutes r⟩, fun x hx => ?_⟩
  show g (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hx), map_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem noCommonZero_of_readings : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → T.R j), (∀ i, ws i ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, ∃ i, rdU (T.U j T.σ₀) (ws i) k x ≠ 0) → NoCommonZero (T.Q.Xo j) T.Q.c ws := by
  intro D T h j hj a n m ws hws hz
  obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hu := (h.toLawsCore.unf j hj T.σ₀ T.good_σ₀).2.2.1
  intro k _ _ _ y
  by_contra hne
  simp only [not_exists, not_not] at hne
  obtain ⟨C, ψ, z, t', hψ, hbor⟩ := hA hG k y
  have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (ws i) z = 0 := by
    intro i
    have e1 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t' z y hbor
    rw [hne i] at e1
    have hw : wchar (ex (T.Q.Dw j) a n) t' ≠ 0 := by
      unfold wchar
      exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
    exact (mul_eq_zero.mp e1.symm).resolve_left hw
  have hsm := C.sm
  have hI : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≠ ⊤ := by
    intro htop
    have hker : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker,
        ← GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ k ψ C.y z hψ]
      exact hz0 i
    have h1 := hker (htop ▸ Submodule.mem_top : (1 : C.R) ∈ _)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨ψ', hψ'⟩ := exists_complex_point T.σ₀ _ hI
  obtain ⟨z', hz'⟩ := hL.bc _ _ ψ' C.y
  obtain ⟨kk, x, t, hb⟩ := hu z'
  obtain ⟨i, hi⟩ := hz kk x.1 x.2
  apply hi
  haveI : IsDomain (CAt T.σ₀) := inferInstanceAs (IsDomain ℂ)
  have e2 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t _ _ hb
  have e3 := GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ _ ψ' C.y z' hz'
  have e4 : ψ' (evR (T.Q.Xo j) T.Q.c (ws i) C.y) = 0 := hψ' _ (Ideal.subset_span ⟨i, rfl⟩)
  have hw2 : wchar (ex (T.Q.Dw j) a n) t ≠ 0 := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
  have e6 : wchar (ex (T.Q.Dw j) a n) t * evR (T.Q.Xo j) T.Q.c (ws i) ((T.U j T.σ₀).un kk x) = 0 := by
    rw [← e2, e3, e4]
  have e5 := (mul_eq_zero.mp e6).resolve_left hw2
  unfold rdU
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2, e5]
  unfold toC
  rfl

end GlobalTheory.FrameZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ScaledFamily
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.ScaledGenerators

theorem span_scaled {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (wL : WeightFamilies.Wt D j)
    (s : 𝓞 B.KO) {N : ℕ} (w0 : Fin N → B.Cusp j wL)
    (h : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL) :
    Submodule.span (𝓞 B.KO) (Set.range fun k => (s : B.KO) • w0 k) = X.WWc s wL := by

  have hfun : (fun k => (s : B.KO) • w0 k) =
      (s • (LinearMap.id : B.Cusp j wL →ₗ[𝓞 B.KO] B.Cusp j wL)) ∘ w0 := by
    funext k
    simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    first
      | rfl
      | exact algebraMap_smul B.KO s (w0 k)
      | simp
  rw [hfun, Set.range_comp, ← Submodule.map_span, h]
  rfl

theorem scaled_family : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (S : Scal B) (N : ℕ) (w0 : Fin N → B.Cusp j wL) (a b G Prw : ℝ), 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (S.sW : B.KO)‖ ≤ a) → Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll wL → (∀ k σ, Real.log (B.supN j wL σ (w0 k)) ≤ b) → a + b ≤ G * wL.size → (∃ Sh : Finset (B.Cusp j wL), Submodule.span (𝓞 B.KO) (Sh : Set (B.Cusp j wL)) = X.WWc S.sW wL ∧ ∃ mx : (B.KO →+* ℂ) → ℝ, (∀ σ, ∀ g ∈ Sh, Real.log (B.supN j wL σ g) ≤ mx σ) ∧ (∑ σ, mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size) ∧ (X.WWc S.sW wL ≤ B.Mlat j wL → Real.log N ≤ Prw * (wL.size - 1) → ∃ Gd : EtaleWeightGaps.GlobalFamilyData X ka wL wF, Gd.TiedW S G Prw) := by
  classical
  intro D B P j X ka wL wF S N w0 a b G Prw ha hb hS hspan hsup hG

  set w : Fin N → B.Cusp j wL := fun k => (S.sW : B.KO) • w0 k with hw
  have hspanw : Submodule.span (𝓞 B.KO) (Set.range w) = X.WWc S.sW wL := span_scaled X wL S.sW w0 hspan

  have hbound : ∀ σ k, Real.log (B.supN j wL σ (w k)) ≤ a + b := by
    intro σ k
    have hmul : B.supN j wL σ (w k) = ‖σ (S.sW : B.KO)‖ * B.supN j wL σ (w0 k) := B.supN_smul j wL σ _ (w0 k)
    rw [hmul]
    by_cases hx : ‖σ (S.sW : B.KO)‖ = 0
    · rw [hx, zero_mul, Real.log_zero]
      linarith
    by_cases hy : B.supN j wL σ (w0 k) = 0
    · rw [hy, mul_zero, Real.log_zero]
      linarith
    rw [Real.log_mul hx hy]
    linarith [hS σ, hsup k σ]

  have hmean : (∑ _σ : B.KO →+* ℂ, (a + b)) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ G * wL.size := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card (B.KO →+* ℂ)) with h0 | h0
    · rw [h0, Nat.cast_zero, zero_mul, zero_div]
      linarith
    · have hc : (Fintype.card (B.KO →+* ℂ) : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel_left₀ _ hc]
      exact hG
  refine ⟨⟨Finset.univ.image w, ?_, fun _ => a + b, ?_, hmean⟩, ?_⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspanw
  · intro σ g hg
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hg
    exact hbound σ k
  · intro hM hN

    refine ⟨{
        N := N
        w := w
        del := 0
        th' := fun i => Fin.elim0 i
        rz := 0
        alz := fun i => Fin.elim0 i
        th0 := fun i => Fin.elim0 i
        zc := fun i => Fin.elim0 i
        rq := 0
        th := fun i => Fin.elim0 i
        iet := 0
        et := 0
        mx := fun _ => a + b }, ?_⟩
    refine ⟨hspanw, ?_, hN, fun σ k => hbound σ k, hmean⟩
    intro k
    apply hM
    rw [← hspanw]
    exact Submodule.subset_span (Set.mem_range_self k)

end GlobalTheory.ScaledGenerators
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexing
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexing
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.UpperRecord

theorem finrank_le_of_parts {Y ι : Type} {Z : ι → Type} (V : Submodule ℂ (Y → ℂ)) (e : Y ≃ Σ k, Z k)
    (d : ι → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (hb : ∀ (k : ι) (m : ℕ) (g : Fin m → V),
      LinearIndependent ℂ (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) → m ≤ d k * C) :
    Module.finrank ℂ V ≤ δ * C := by
  classical
  let ρ : ∀ k, V →ₗ[ℂ] (Z k → ℂ) := fun k =>
    (LinearMap.funLeft ℂ ℂ fun z : Z k => e.symm ⟨k, z⟩).comp V.subtype
  have hr : ∀ k, Module.rank ℂ (LinearMap.range (ρ k)) ≤ (d k * C : ℕ) := fun k => by
    refine rank_le fun s hs => ?_
    have hs' := (hs.comp s.equivFin.symm s.equivFin.symm.injective).map' (LinearMap.range (ρ k)).subtype
      (Submodule.ker_subtype _)
    choose g hg using fun q : Fin s.card => (s.equivFin.symm q).1.2
    refine hb k s.card g ?_
    have heq : (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) = _ := funext hg
    rw [heq]
    exact hs'
  have hfin : ∀ k, Module.Finite ℂ (LinearMap.range (ρ k)) := fun k =>
    Module.rank_lt_aleph0_iff.1 ((hr k).trans_lt (Cardinal.natCast_lt_aleph0))
  have hfr : ∀ k, Module.finrank ℂ (LinearMap.range (ρ k)) ≤ d k * C := fun k =>
    Module.finrank_le_of_rank_le (hr k)
  let s : Finset ι := Finset.univ.image fun q => (en q).1
  have hs : ∀ k, k ∉ s → d k = 0 := fun k hk => by
    by_contra h0
    exact hk (Finset.mem_image.2 ⟨en.symm ⟨k, ⟨0, Nat.pos_of_ne_zero h0⟩⟩, Finset.mem_univ _, by simp⟩)
  let Φ : V →ₗ[ℂ] (∀ k : s, LinearMap.range (ρ k)) := LinearMap.pi fun k => (ρ k).rangeRestrict
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have hk : ∀ k, ρ k g = 0 := fun k => by
      by_cases hk : k ∈ s
      · exact congrArg Subtype.val (congrFun hg ⟨k, hk⟩)
      · have h0 : Module.finrank ℂ (LinearMap.range (ρ k)) = 0 := by
          have := hfr k
          rw [hs k hk] at this
          omega
        have := Submodule.finrank_eq_zero.1 h0
        exact (Submodule.eq_bot_iff _).1 this _ ⟨g, rfl⟩
    ext y
    have := congrFun (hk (e y).1) (e y).2
    simpa [ρ, LinearMap.funLeft_apply] using this
  have hsum : ∑ k : s, d k ≤ δ := by
    have hinj : Function.Injective fun p : Σ k : s, Fin (d k) => en.symm ⟨p.1.1, p.2⟩ := by
      rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, a'⟩ hp
      have := en.symm.injective hp
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 this
      obtain rfl := eq_of_heq h2
      rfl
    simpa using Fintype.card_le_of_injective _ hinj
  calc Module.finrank ℂ V ≤ Module.finrank ℂ (∀ k : s, LinearMap.range (ρ k)) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ k : s, Module.finrank ℂ (LinearMap.range (ρ k)) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ k : s, d k * C := Finset.sum_le_sum fun k _ => hfr k
    _ = (∑ k : s, d k) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ δ * C := Nat.mul_le_mul_right _ hsum

theorem upper : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → Module.finrank ℂ (R.sp (addL wF wL Tn) Set.univ) ≤ δ * (Tn + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j) := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _
  refine finrank_le_of_parts _ e (fun k => (Fl.Fl k).δ) _ δ en fun k m g hg => ?_
  choose f hf hgf using fun q => (GlobalTheory.T.mem_span_cuspReadings_iff_components D T h j hj n R e hR (addL wF wL Tn)).1 (g q).1 (g q).2
  have hw := (GlobalTheory.T.componentModelWeight_dimension_dictionary D T h j hj k).2.2.1 wF wL Tn
  have := GlobalTheory.UpperModel.upper _ _ _ (A.Xa k) (Fl.Fl k) m (fun q => f q k) (fun q => by
    rw [A.hF, A.hL, A.hT, ← hw]
    exact (hf q k).1.1) (fun u hu => by
    funext q
    refine Fintype.linearIndependent_iff.1 hg u ?_ q
    funext z
    have := hu z.1 z.2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hgf q, e.apply_symm_apply])
  rwa [A.hT, A.dim] at this

end GlobalTheory.UpperRecord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexingStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_flat_decomposition_indexing : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → Module.finrank ℂ (R.sp (addL wF wL Tn) Set.univ) ≤ δ * (Tn + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j) := by
  first | exact @GlobalTheory.UpperRecord.upper | exact GlobalTheory.UpperRecord.upper | (intros; apply GlobalTheory.UpperRecord.upper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.LowerBound

theorem le_finrank_of_pieces {K Z : Type} [Fintype K] [DecidableEq K] {Y : K → Type} (dom : ∀ k, Set (Y k))
    (e : Z ≃ Σ k, dom k) (d : K → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (f : ∀ k, Fin (d k * C) → Y k → ℂ)
    (hf : ∀ k (u : Fin (d k * C) → ℂ), (∀ x ∈ dom k, ∑ q, u q * f k q x = 0) → u = 0)
    (S : Submodule ℂ (Z → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k q, (fun z => (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e z).1 (e z).2.1) ∈ S) :
    δ * C ≤ Module.finrank ℂ S := by
  let v : (Σ k, Fin (d k * C)) → S := fun p => ⟨_, hS p.1 p.2⟩
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have key := hf p.1 (fun q => g ⟨p.1, q⟩) fun x hx => by
      have h1 := congrFun (congrArg Subtype.val hg) (e.symm ⟨p.1, x, hx⟩)
      rw [Submodule.coe_sum, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single p.1] at h1
      · refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h1
        show _ = g _ * (Pi.single p.1 (f p.1 q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1
        rw [e.apply_symm_apply]
        simp
      · intro k _ hk
        refine Finset.sum_eq_zero fun q _ => ?_
        show g _ * (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1 = 0
        rw [e.apply_symm_apply]
        simp [Pi.single_eq_of_ne hk.symm]
      · simp
    exact congrFun key p.2
  have h1 := hv.fintype_card_le_finrank
  have h2 := Fintype.card_congr en
  simp only [Fintype.card_sigma, Fintype.card_fin] at h1 h2
  rwa [← Finset.sum_mul, ← h2] at h1

variable {D : D7}

theorem laR_wadd (T : Top D) (j : ℕ) (u v : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wadd u v) k = laR T j u k + laR T j v k := by
  unfold laR
  rw [wtA_wadd]
  exact laU_add (T.U j T.σ₀) (wtA u) (wtA v) u.n v.n u.n_even v.n_even k

theorem laR_wsmul (T : Top D) (j : ℕ) (m : ℕ) (u : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  induction m with
  | zero =>
    funext τ a
    simp [laR, laU, wtA, wsmul, Formalism.L2.Pj.ext0]
  | succ m ih =>
    have e : wsmul (m + 1) u = wadd (wsmul m u) u := by
      simp only [wsmul, wadd, add_mul, one_mul]
    rw [e, laR_wadd, ih, succ_nsmul]

theorem lower_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _ CR c hc hM
  have hex : ∀ k : (T.U j T.σ₀).Comp,
      ∃ f : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ,
        (∀ q, f q ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) ∧
        ∀ u : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → ℂ,
          (∀ x ∈ ((T.U j T.σ₀).X k).dom, ∑ q, u q * f q x = 0) → u = 0 := by
    intro k
    obtain ⟨⟨bb, m, h1, h2, h3⟩, -, h4, h5, h6⟩ := A.mar k
    have hint := interpCStatement_holds _ _ (A.Xa k) (Fl.Fl k) (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
      ⟨bb, m, h1, h2, h3 _ (by simp)⟩ h4 h5 (by simpa using h6 0) (GlobalTheory.ClosedModes.modeHalf_closed _ _)
    have hmany := GlobalTheory.ManyForms.exists_indep_forms _ _ (A.Xa k) (Fl.Fl k) (A.Xa k).Fp Tn (A.Xa k).c1
      (A.Xa k).frame_theta_const_pos.le hint
    rw [A.hF k, A.hL k, A.hc k] at hmany
    rw [← A.dim k, addL, laR_wadd, laR_wsmul]
    exact hmany
  choose f hfm hfi using hex
  haveI := (GlobalTheory.Shares.PolyDict.sp_finrank R (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))).1
  refine le_finrank_of_pieces (fun k => ((T.U j T.σ₀).X k).dom) e (fun k => (Fl.Fl k).δ) _ δ en f hfi _ fun k q => ?_
  obtain ⟨m, a, F, hF, hsum⟩ := hM (Pi.single k (f k q)) fun k' => by
    rw [← hc]
    by_cases hk : k' = k
    · subst hk
      rw [Pi.single_eq_same]
      exact hfm _ q
    · rw [Pi.single_eq_of_ne hk]
      exact (siegelSpaceAlgebra_holds _ _ _ (laR T j (addL wF wL Tn) k') c1).2.2.1.1
  have hE : (fun z => (Pi.single k (f k q) : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (e z).1 (e z).2.1) =
      ∑ i, a i • R.ev ((recPlusN h j hj n).inc _ (F i)) := by
    funext z
    rw [hsum _ _ (e z).2.2, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hE]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.LowerBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeffStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  first | exact @GlobalTheory.LowerBound.lower_bound | exact GlobalTheory.LowerBound.lower_bound | (intros; apply GlobalTheory.LowerBound.lower_bound <;> assumption)
end
end
