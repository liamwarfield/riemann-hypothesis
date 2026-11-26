module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisThetaLaws

theorem heis_theta_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), (∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f)) ∧ (∀ w w' f, heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f) ∧ ∀ g h x y, symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y :=
  fun D ψ hψ S T =>
    ⟨fun w _ hf => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w,
      fun w w' f => GlobalTheory.WeilVacMove.heisO_heisO ψ S T w w' f,
      GlobalTheory.SymplOInv.symplO_actO D S T⟩

end GlobalTheory.HeisThetaLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
open scoped Pointwise

namespace GlobalTheory.TypePlaces

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem not_isConjPl : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Lev.IsConjPl PP PP' := by
  intro D Pb Pg hPg PP hP PP' hP' hc
  obtain ⟨k, hk⟩ := (hPg PP).1 hP
  obtain ⟨k', hk'⟩ := (hPg PP').1 hP'
  have hle : D.host.conj • PP.asIdeal ≤ PP'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • PP.asIdeal).IsMaximal := by
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • PP.asIdeal = PP'.asIdeal := hmax.eq_of_le PP'.isPrime.ne_top hle
  obtain ⟨ho, hm⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP
    (Pb.overP hk)).2.2.2 (Pb.pb k) (Pb.pb_over k) PP' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj PP PP').2 heq)
  have hkk : k ≠ k' := by
    rintro rfl
    exact hm.1 hk hk'
  have ho' := Pb.overP hk'
  have hne : D.host.g k ≠ D.host.g k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hkk
    · exact this
    · exact this.symm
    · exact absurd rfl hkk
  have hco : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hne)
  obtain ⟨a, b, hab⟩ := hco
  apply PP'.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ ho) (Ideal.mul_mem_left _ _ ho')

end GlobalTheory.TypePlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesNotPairwiseConjugateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_not_pairwise_conjugate : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Lev.IsConjPl PP PP' := by
  first | exact @GlobalTheory.TypePlaces.not_isConjPl | exact GlobalTheory.TypePlaces.not_isConjPl | (intros; apply GlobalTheory.TypePlaces.not_isConjPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors

def LiesOver {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b)
    (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre F k g.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A F k) (s' : Fam D.toPre F k) (v : F),
      U.ExpandsF F k w₀ s s' → ValAt s x fr v → SumF I F (coef s' g wk) v

section
open GlobalTheory.UT.PullExp GlobalTheory.FieldBaseChange

theorem coef_twistPull : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end

section
open GlobalTheory.UT.EvalZero GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem sumF_origin : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∃ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen) ∧ (∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ w₀, NormW U.toUnifPre w₀ ρ) ∧ ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (k : ℕ) (t : SecA A F k) s, U.ExpandsF F k w₀ t s → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero → FrmOne w → ∀ c : F, (∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) → SumF I F (coef s g w) c := by
  intro _ R _ _ _ I hI D A G _ _ _ U F _ _
  refine ⟨exists_gen_pt (Y := Spec (CommRingCat.of (FractionRing R))) A.isLB
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
      (fun y => Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _) _ _,
    exists_normW U.toUnifPre, ?_⟩
  rintro w₀ ρ h k t s ⟨σ', hR, n, c, σ, f, hE, hσ, hs⟩ g w hg hw b hb
  choose a ha using fun i α => exists_value D.toPre k α (f i α)
  choose x hx using fun i => exists_coeff (A := R) U.LG.isLB (σ i) (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval (σ i) (r ≫ eSec G) z J = Geo.Tor.cst r z (x i) * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun i Z r z J hJ => (hx i Z r z J hJ).trans (by rw [val_pow])
  rw [value_comb U.toUnifPre F h t σ' hR c σ hσ x hx' b hb,
    funext fun α => coef_comb F s c f α (hs α) (fun i => a i α) (fun i => ha i α) g w hg hw]
  exact sumF_comb hI F _ c _ _ fun i => sumF_map I F (a i) (x i) fun e =>
    value_sub_sum_mem U.toUnifPre e k (σ i) (f i) (hE i e) (x i) (hx' i) (a i) (ha i)

end

end GlobalTheory.Poinc.Tors
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep Topology
open scoped ContDiff

namespace GlobalTheory.ConstTermSmooth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
def invM (y : Lie E a) : Lie E a := toL (Matrix.of y)⁻¹


omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiffOn_invM : ContDiffOn ℝ ∞ (invM (E := E) (a := a)) (invSet E a) := by
  have h1 : ContDiffOn ℝ ∞ (fun y : Lie E a => Ring.inverse (Matrix.of y).det) (invSet E a) := fun y hy => by
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  have h2 : ContDiff ℝ ∞ fun y : Lie E a => (Matrix.of y).adjugate i j := by
    simp only [Matrix.adjugate_apply]
    have h3 : ContDiff ℝ ∞ fun y : Lie E a => (Function.update y j (Pi.single i 1) : Lie E a) := by
      refine contDiff_pi.2 fun k => ?_
      by_cases h : k = j
      · subst h; simpa using contDiff_const
      · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
    exact contDiff_det.comp h3
  exact h1.mul h2.contDiffOn

theorem continuous_infGL : Continuous (infGL E a) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))))

theorem continuousOn_chart {φ : GA E a → ℂ} (hφ : Continuous φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ p.1 p.2) (Set.univ ×ˢ invSet E a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hu : Continuous fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) =>
      (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)) : GL (Fin a) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_snd.comp continuous_subtype_val, ?_⟩
    have := contDiffOn_invM.continuousOn.comp_continuous
      (f := fun p : (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a)) => p.1.2)
      (continuous_snd.comp continuous_subtype_val) fun p => p.2.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  refine (hφ.comp ((continuous_fst.comp continuous_subtype_val).mul (continuous_infGL.comp hu))).congr fun p => ?_
  exact (chart_val φ p.1.1 (IsUnit.unit (p.2.2 : IsUnit (Matrix.of p.1.2)))).symm


omit [_root_.NumberField.IsTotallyComplex E] in
def coef (i : Fin (Module.finrank ℝ (Lie E a))) (y : Lie E a) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L lmul (invM y)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem contDiffOn_coef (i : Fin (Module.finrank ℝ (Lie E a))) : ContDiffOn ℝ ∞ (coef i) (invSet E a) := by
  refine contDiffOn_clm_apply.2 fun Y => ?_
  exact (Complex.ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ (Lie E a)).coord i) ∘L
    rmul Y).contDiff.comp_contDiffOn contDiffOn_invM

theorem fderiv_chart (φ : Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart φ.1 g) y = ∑ i, chart (lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 g y • coef i y := by
  ext Y
  have e : Y = rmul (lmul (invM y) Y) y := by
    change Matrix.of Y = Matrix.of y * ((Matrix.of y)⁻¹ * Matrix.of Y)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hy)]
  have e2 : ∀ X, rmul X y = lmul y X := fun _ => rfl
  conv_lhs => rw [e, e2, ← (Module.finBasis ℝ (Lie E a)).sum_repr (lmul (invM y) Y)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ← e2, ← chart_lieD φ.2 _ g hy, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm,
    Complex.real_smul]
  rfl

def Good (φ : Sm E a) : Prop := (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}

theorem Good.lie {φ : Sm E a} (h : Good φ) (X : Lie E a) : Good (lie E a X φ) := by
  refine ⟨fun γ g => ?_, ?_⟩
  · have e : chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
      funext x; simp only [chart, mul_assoc, h.1]
    simp only [lie_apply, lieD, e]
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)
    have e := LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : rt E a (finGL E a k) φ = φ := hk
    simp only [Module.End.mul_apply, hk'] at e
    exact e.symm


omit [_root_.NumberField.IsTotallyComplex E] in
theorem exists_bound {r : ℕ} {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V} {S : Set (Lie E a)}
    (hS : IsCompact S) (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ S))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) :
    ∃ C, ∀ (x : BlockIx a r → Ad E), ∀ y ∈ S, ‖Ψ (unip x * g) y‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn
    (f := fun p : (BlockIx a r → Ad E) × Lie E a => Ψ (unip p.1 * g) p.2)
    (hc.comp (((CuspidalL2GL.continuous_unip.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun p hp => ⟨trivial, hp.2⟩)
  refine ⟨C, fun x y hy => ?_⟩
  obtain ⟨_, ⟨z, rfl⟩, hk⟩ := hcov x
  have := hC (_, y) ⟨hk, hy⟩
  simp only [unip_add, mul_assoc] at this
  exact (congrArg (fun f => ‖f y‖) ((congrArg (fun u => Ψ (u * _)) (unip_algebraMap z)).trans (hl _ _))).symm.trans_le
    this

theorem Good.chart_left {φ : Sm E a} (h : Good φ) (γ : GL (Fin a) E) (g : GA E a) :
    chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
  funext x; simp only [chart, mul_assoc, h.1]

theorem Good.continuousOn_chart {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => chart φ.1 p.1 p.2) (Set.univ ×ˢ invSet E a) :=
  ConstTermSmooth.continuousOn_chart (ContAut.continuous_of_isOpen_stab E a φ h.2)

theorem Good.continuousOn_fderiv {φ : Sm E a} (h : Good φ) :
    ContinuousOn (fun p : GA E a × Lie E a => fderiv ℝ (chart φ.1 p.1) p.2) (Set.univ ×ˢ invSet E a) := by
  refine ContinuousOn.congr ?_ fun p hp => fderiv_chart φ p.1 hp.2
  exact continuousOn_finsetSum _ fun i _ => (h.lie _).continuousOn_chart.smul
    ((contDiffOn_coef i).continuousOn.comp continuous_snd.continuousOn fun p hp => hp.2)

section Integral

variable {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
  (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν]


omit [_root_.NumberField.IsTotallyComplex E] in
theorem integrable_unip {V : Type} [NormedAddCommGroup V] {Ψ : GA E a → Lie E a → V}
    (hc : ContinuousOn (fun p : GA E a × Lie E a => Ψ p.1 p.2) (Set.univ ×ˢ invSet E a))
    (hl : ∀ γ g, Ψ (ratGL E a γ * g) = Ψ g) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    Integrable (fun x => Ψ (unip x * g) y) ν := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  obtain ⟨C, hC⟩ := exists_bound (r := r) (isCompact_singleton (x := y))
    (hc.mono (Set.prod_mono_right (Set.singleton_subset_iff.2 hy))) hl g
  have hf : Continuous fun x : BlockIx a r → Ad E => Ψ (unip x * g) y :=
    hc.comp_continuous ((CuspidalL2GL.continuous_unip.mul continuous_const).prodMk continuous_const) fun _ => ⟨trivial, hy⟩
  exact Integrable.of_bound hf.aestronglyMeasurable C (.of_forall fun x => hC x y rfl)


omit [BorelSpace (BlockIx a r → Ad E)] [IsFiniteMeasure ν] in
theorem chart_integral (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun g => ∫ x, φ (unip x * g) ∂ν) g = fun y => ∫ x, chart φ (unip x * g) y ∂ν := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, mul_assoc]
  · simp only [chart, dif_neg h, integral_zero]

theorem Good.hasFDerivAt {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    HasFDerivAt (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (∫ x, fderiv ℝ (chart φ.1 (unip x * g)) y ∂ν) y := by
  rw [chart_integral]
  obtain ⟨S, hSy, hSU, hS⟩ := local_compact_nhds (isOpen_invSet.mem_nhds hy)
  have hl : ∀ γ g, (fun y => fderiv ℝ (chart φ.1 (ratGL E a γ * g)) y) = fun y => fderiv ℝ (chart φ.1 g) y :=
    fun γ g => by rw [h.chart_left]
  obtain ⟨C, hC⟩ := exists_bound (r := r) (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) hS
    (h.continuousOn_fderiv.mono (Set.prod_mono_right hSU)) hl g
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C) hSy
    (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) fun z hz =>
      (integrable_unip ν h.continuousOn_chart h.chart_left g hz).1)
    (integrable_unip ν h.continuousOn_chart h.chart_left g hy)
    (integrable_unip ν (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv hl g hy).1
    (.of_forall hC) (integrable_const C) (.of_forall fun x z hz => ?_)
  exact ((contDiffAt_chart φ.2 _ (hSU hz)).differentiableAt (by simp)).hasFDerivAt

theorem Good.fderiv_integral {φ : Sm E a} (h : Good φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) y = ∑ i,
      chart (fun g => ∫ x, (CuspRep.lie E a (Module.finBasis ℝ (Lie E a) i) φ).1 (unip x * g) ∂ν) g y • coef i y := by
  rw [(h.hasFDerivAt ν g hy).fderiv]
  simp only [fderiv_chart φ _ hy, chart_integral]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_unip ν (h.lie _).continuousOn_chart (h.lie _).chart_left g hy).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _

theorem contDiffOn_integral (g : GA E a) (n : ℕ) : ∀ φ : Sm E a, Good φ →
    ContDiffOn ℝ n (chart (fun g => ∫ x, φ.1 (unip x * g) ∂ν) g) (invSet E a) := by
  induction n with
  | zero =>
    intro φ h
    exact contDiffOn_zero.2 fun y hy => (h.hasFDerivAt ν g hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro φ h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (h.hasFDerivAt ν g hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr ?_ fun y hy => h.fderiv_integral ν g hy
    exact ContDiffOn.sum fun i _ => (ih _ (h.lie _)).smul ((contDiffOn_coef i).of_le (by exact_mod_cast le_top))

end Integral

theorem constTerm_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a),
      lieD X (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hl ho
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by simp [h1]⟩
  have h : Good φ := ⟨hl, ho⟩
  refine ⟨fun g => contDiffOn_infty.2 fun n => contDiffOn_integral _ g n φ h, fun X g => ?_⟩
  rw [lieD, (h.hasFDerivAt (μ.restrict 𝓕) g (y := oneL E a) isUnit_one).fderiv, ContinuousLinearMap.integral_apply
    (integrable_unip _ (Ψ := fun g y => fderiv ℝ (chart φ.1 g) y) h.continuousOn_fderiv
      (fun γ g => by rw [h.chart_left]) g (y := oneL E a) isUnit_one)]
  rfl

end GlobalTheory.ConstTermSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegralStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_automorphic_form_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a), lieD X (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.ConstTermSmooth.constTerm_mem_Sm | exact GlobalTheory.ConstTermSmooth.constTerm_mem_Sm | (intros; apply GlobalTheory.ConstTermSmooth.constTerm_mem_Sm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial GlobalTheory.SphPar GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.SphGal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Global

variable {E : Type} [Field E] [NumberField E]

end Global

def spehInf (d : ℕ) (A : Multiset ℂ) : Multiset ℂ :=
  ∑ j : Fin d, A.map (· + (((d : ℂ) - 1) / 2 - (j : ℕ)))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

end GlobalTheory.SphGal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticePointsIntegralIdelesEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticePointsIntegralIdelesEquiv
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LatBij

variable {E : Type} [Field E] [NumberField E]

def diag : Eˣ →* (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom

theorem coe_diag (a : Eˣ) : (diag a : Af E) = algebraMap E (Af E) a := rfl

theorem diag_mem_princ (a : Eˣ) : diag a ∈ (princ : Subgroup (Af E)ˣ) := ⟨a, rfl⟩

theorem diag_unit_mem (c : Ideal (OF E)) (u : (OF E)ˣ) :
    diag (Units.map (algebraMap (OF E) E).toMonoidHom u) ∈ hatOUnits c := by
  rw [mem_hatOUnits, ← map_inv, ← map_inv]
  exact ⟨algebraMap_mem_hatO (algebraMap_mem_orderC c _), algebraMap_mem_hatO (algebraMap_mem_orderC c _)⟩

def rep {c : Ideal (OF E)} {y : (Af E)ˣ} (a : modUnits (lattice c y)) : Eˣ := Units.mk0 a.1.out (out_mem_lattice a).2

def toIdele (c : Ideal (OF E)) (p : Σ q : PicO c, modUnits (lattice c q.out)) :
    {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} :=
  ⟨QuotientGroup.mk (diag (rep p.2) * p.1.out⁻¹), _, rfl, (out_mem_lattice p.2).1⟩

theorem toIdele_surjective (c : Ideal (OF E)) : Function.Surjective (toIdele c) := by
  rintro ⟨_, y, rfl, hy⟩
  let q : PicO c := QuotientGroup.mk y⁻¹
  have hq : (q.out)⁻¹ * y⁻¹ ∈ princ ⊔ hatOUnits c := QuotientGroup.eq.1 (Quotient.out_eq q)
  obtain ⟨_, ⟨α, rfl⟩, u, hu, h⟩ := Subgroup.mem_sup.1 hq
  change diag α * u = _ at h
  have h1 : diag α⁻¹ * q.out⁻¹ = y * u := by
    rw [map_inv, eq_mul_inv_iff_mul_eq.1 h |>.symm, mul_assoc, inv_mul_cancel_left, mul_comm]
  have hx : ((α⁻¹ : Eˣ) : E) ∈ lattice c q.out := by
    rw [mem_lattice, ← coe_diag, ← Units.val_mul, h1, Units.val_mul]
    exact mul_mem hy hu.1
  let a : modUnits (lattice c q.out) := ⟨Quotient.mk _ ((α⁻¹ : Eˣ) : E), _, hx, Units.ne_zero _, rfl⟩
  obtain ⟨w, hw⟩ : (unitRel (E := E)).r ((α⁻¹ : Eˣ) : E) a.1.out := Quotient.exact (Quotient.out_eq a.1).symm
  have hr : rep a = Units.map (algebraMap (OF E) E).toMonoidHom w * α⁻¹ := Units.ext hw
  refine ⟨⟨q, a⟩, Subtype.ext ?_⟩
  refine (QuotientGroup.eq.2 ?_ : (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = _).symm
  change y⁻¹ * (diag (rep a) * q.out⁻¹) ∈ _
  rw [hr, map_mul, mul_assoc, h1, mul_left_comm, inv_mul_cancel_left]
  exact mul_mem (diag_unit_mem c w) hu

theorem toIdele_injective (c : Ideal (OF E)) (hcap : lattice c 1 = (orderC c : Set E))
    (hun : ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u) :
    Function.Injective (toIdele c) := by
  rintro ⟨q, a⟩ ⟨q', a'⟩ h
  have h1 : (diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹) ∈ hatOUnits c :=
    QuotientGroup.eq.1 (congrArg Subtype.val h)
  have hq : q = q' := by
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    refine QuotientGroup.eq.2 ?_
    have : q.out⁻¹ * q'.out = diag ((rep a)⁻¹ * rep a') *
        ((diag (rep a) * q.out⁻¹)⁻¹ * (diag (rep a') * q'.out⁻¹))⁻¹ := by
      rw [map_mul, map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left (diag_mem_princ _)) (Subgroup.mem_sup_right (inv_mem h1))
  subst hq
  have h2 : diag ((rep a)⁻¹ * rep a') ∈ hatOUnits c := by
    convert h1 using 1
    rw [map_mul, map_inv, mul_inv, inv_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
  have key : ∀ b : Eˣ, diag b ∈ hatOUnits c → (b : E) ∈ orderC c := fun b hb => by
    have : (b : E) ∈ lattice c 1 := by
      rw [mem_lattice, inv_one, Units.val_one, mul_one]
      exact hb.1
    rwa [hcap] at this
  obtain ⟨u, hu⟩ := hun _ (Units.ne_zero _) (key _ h2) (by
    rw [← Units.val_inv_eq_inv_val]
    exact key _ (by rw [map_inv]; exact inv_mem h2))
  have h3 : a = a' := by
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq a'.1]
    refine Quotient.sound ⟨u, ?_⟩
    rw [← hu]
    change ((rep a' : Eˣ) : E) = _ * ((rep a : Eˣ) : E)
    rw [← Units.val_mul, mul_comm, mul_inv_cancel_left]
  rw [h3]

theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ →
    ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃
      {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c},
      ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) →
        (e p).1 = QuotientGroup.mk y := by
  intro E _ _ _ 𝔣 c h𝔣 hc hc0
  refine ⟨Equiv.ofBijective (toIdele c) ⟨toIdele_injective c (GlobalTheory.T.idelicRingClassLattice_one_eq_order E c hc0) (GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units E 𝔣 c h𝔣 hc),
    toIdele_surjective c⟩, fun p y hy => ?_⟩
  have : y = diag (rep p.2) * p.1.out⁻¹ := Units.ext hy
  rw [this]
  rfl

end GlobalTheory.CMVal.LatBij
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticePointsIntegralIdelesEquivStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticePoints_integralIdeles_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ → ∃ e : (Σ q : PicO c, modUnits (lattice c q.out)) ≃ {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c}, ∀ p, ∀ y : (Af E)ˣ, (y : Af E) = algebraMap E (Af E) (p.2.1.out) * (((Quotient.out p.1 : (Af E)ˣ)⁻¹ : (Af E)ˣ) : Af E) → (e p).1 = QuotientGroup.mk y := by
  first | exact @GlobalTheory.CMVal.LatBij.exists_equiv | exact GlobalTheory.CMVal.LatBij.exists_equiv | (intros; apply GlobalTheory.CMVal.LatBij.exists_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.ObjModel

namespace GlobalTheory.ToricSumValue

theorem cpow_pos_eq {r : ℝ} (hr : 0 < r) (z : ℂ) : (r : ℂ) ^ z = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le]

theorem term_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s) (σ : ℂ) (k : Eˣ) :
    term φ (2 * s) κ σ k = (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) *
      ((modF (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℝ) : ℂ) ^ ((s : ℂ) + σ) := by
  have hpos : ∀ i, 0 < ‖φ i (k : E)‖ := fun i => by simp
  have hN : 0 < ∏ i, ‖φ i (k : E)‖ ^ 2 := Finset.prod_pos fun i _ => pow_pos (hpos i) 2
  rw [modF_princ k, ← prod_normSq hφ k,
    Complex.cpow_add _ _ (by exact_mod_cast (inv_pos.2 hN).ne'), Complex.cpow_natCast]
  have h1 : term φ (2 * s) κ σ k = term φ (2 * s) κ 0 k * ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    unfold term
    rw [← Finset.prod_mul_distrib]
    simp
  have h2 : ∏ i, ((‖φ i (k : E)‖ : ℝ) : ℂ) ^ (-2 * σ) = (((∏ i, ‖φ i (k : E)‖ ^ 2)⁻¹ : ℝ) : ℂ) ^ σ := by
    rw [cpow_pos_eq (inv_pos.2 hN), Real.log_inv, Real.log_prod (fun i _ => (pow_pos (hpos i) 2).ne')]
    simp only [cpow_pos_eq (hpos _)]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_pow]
    push_cast
    ring
  have h3 := term_mul_inf h k
  have h4 : ∏ i, (φ i k * starRingEnd ℂ (φ i k)) ^ s = (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s := by
    rw [Finset.prod_pow]
    congr 1
    push_cast
    exact Finset.prod_congr rfl fun i _ => Complex.mul_conj' _
  have h5 : (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * (χ.inf k : ℂ) = 1 := by
    rw [← Units.val_mul, finPart_mul_inf, Units.val_one]
  rw [h4] at h3
  have hN' : (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [h1, h2, ← mul_assoc]
  congr 1
  rw [Complex.ofReal_inv, inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hN')]
  linear_combination (finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) : ℂ) * h3 -
    (term φ (2 * s) κ 0 k * (((∏ i, ‖φ i (k : E)‖ ^ 2) : ℝ) : ℂ) ^ s) * h5

def twistFin {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) : (Af E)ˣ →* ℂ where
  toFun y := (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S
  map_one' := by
    have : modF (1 : (Af E)ˣ) = 1 := modF_unit (c := ⊤) (one_mem _)
    simp [this]
  map_mul' y y' := by
    rw [map_mul, modF_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (modF_pos y).le (modF_pos y').le,
      Units.val_mul]
    ring

theorem twistFin_apply {E : Type} [Field E] [NumberField E] (χ : HChar E) (S : ℂ) (y : (Af E)ˣ) :
    twistFin χ S y = (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S := rfl

theorem hasSum_classes {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {χ : HChar E} (h : HasInf χ φ fun i => (κ i : ℤ) + s)
    {𝔣 c : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) (hd : 𝔣 ∣ c) (hc : c ≠ ⊥) (hχ : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    {σ T : ℂ} {S : PicO c → ℂ}
    (hS : ∀ q, HasSum (fun x : modUnits (lattice c q.out) => term φ (2 * s) κ σ x.1.out) (S q))
    (hT : HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits c // ∃ y : (Af E)ˣ,
      (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = z ∧ (y : Af E) ∈ hatO c} => twistFin χ (s + σ) z.1.out) T) :
    HasSum (fun q : PicO c => (twistFin χ (s + σ) q.out)⁻¹ * S q) T := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_latticePoints_integralIdeles_equiv E 𝔣 c h𝔣 hd hc
  rw [← e.hasSum_iff] at hT
  refine HasSum.sigma hT fun q => ?_
  refine ((hS q).mul_left (twistFin χ (s + σ) q.out)⁻¹).congr_fun fun x => ?_
  let k : Eˣ := Units.mk0 x.1.out (out_mem_lattice x).2
  have h1 := he ⟨q, x⟩ (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹) rfl
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (hatOUnits c)
    (Units.map (algebraMap E (Af E)).toMonoidHom k * (q.out)⁻¹)
  have h2 : twistFin χ (s + σ) u = 1 := by
    rw [twistFin_apply, hχ u u.2, modF_unit u.2]; simp
  have h3 : term φ (2 * s) κ σ x.1.out = twistFin χ (s + σ) (Units.map (algebraMap E (Af E)).toMonoidHom k) :=
    term_eq hφ h σ k
  show twistFin χ (s + σ) (e ⟨q, x⟩).1.out = _
  rw [h1, hu, map_mul, map_mul, h2, h3, mul_one, mul_comm, map_inv]

theorem toricSum_eq : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ → open Classical in IsToricSum φ s κ (condQ 𝔣 Q) χ (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ)) := by
  intro hH E _ _ _ I _ φ hφ s κ 𝔣 Q χ Pq Λ hU hs h𝔣 hQ hχ hP hΛ
  classical
  have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hd : 𝔣 ∣ condQ 𝔣 Q := dvd_mul_right _ _
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hU h𝔣 hQ hχ
  have hfin := GlobalTheory.T.finite_ringClassGroup_of_conductor_ne_zero E _ hc
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    GlobalTheory.T.exists_entire_latticeSum_of_heckeL_continuation hH E I φ hφ s κ 𝔣 _ χ hU hs h𝔣 hd hc hχ.1 hχ.2.2.1 htriv q.out
  refine ⟨hfin, S, hS, ?_⟩
  have := Fintype.ofFinite (PicO (condQ 𝔣 Q))
  have key : (fun σ : ℂ => ∑ q : PicO (condQ 𝔣 Q), (twistFin χ (s + σ) q.out)⁻¹ * S q σ) = fun σ : ℂ =>
      Λ (s + σ) * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)),
        ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) *
          (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) +
          ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ))) ^ 2) := by
    refine entire_eq_of_halfPlane ?_ ?_ (1 - s) fun σ hσ => ?_
    · refine Differentiable.fun_sum fun q _ => Differentiable.mul ?_ (hS q).1
      simp only [twistFin_apply, mul_inv, ← Complex.cpow_neg]
      refine Differentiable.const_mul ?_ _
      exact Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (modF_pos _).ne'))
    · refine (hΛ.1.comp (by fun_prop)).mul (Differentiable.fun_finsetProd fun q _ => ?_)
      have h0 : Differentiable ℂ fun σ : ℂ => (Ideal.absNorm q.asIdeal : ℂ) ^ (-(s + σ)) := by
        refine Differentiable.const_cpow (by fun_prop) (Or.inl ?_)
        rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
        exact q.ne_bot
      fun_prop
    · have h1 : 1 < ((s : ℂ) + σ).re := by simp; linarith
      have h2 := GlobalTheory.T.hasSum_integralIdeles_eulerProduct E I φ hφ s κ 𝔣 Q χ Pq (s + σ) _ hU h𝔣 hQ hχ hP h1 (hΛ.2 _ h1)
      exact (hasSum_fintype _).unique (hasSum_classes hφ hχ.2.2.1 h𝔣 hd hc htriv
        (fun q => (hS q).2 σ (by push_cast; linarith)) h2)
  have h0 := congrFun key 0
  simp only [add_zero, twistFin_apply, Complex.cpow_neg, Complex.cpow_natCast] at h0
  rw [finsum_eq_sum_of_fintype]
  simp only [Formalism.PairingDivisionLocalBalance.eq, Complex.ofReal_pow]
  exact h0.symm

end GlobalTheory.ToricSumValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (Λ : ℂ → ℂ), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → IsHeckeL χ Λ → open Classical in IsToricSum φ s κ (condQ 𝔣 Q) χ (Λ s * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), Formalism.PairingDivisionLocalBalance.eq (Ideal.absNorm q.asIdeal) s (val χ (Pq q) : ℂ)) := by
  first | exact @GlobalTheory.ToricSumValue.toricSum_eq | exact GlobalTheory.ToricSumValue.toricSum_eq | (intros; apply GlobalTheory.ToricSumValue.toricSum_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s), ∃ o' : Obj b N (f ≫ s), Nonempty (ObjMap o' o f) := by
  first | exact @GlobalTheory.HTPull.exists_objMap_pull | exact GlobalTheory.HTPull.exists_objMap_pull | (intros; apply GlobalTheory.HTPull.exists_objMap_pull <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev l2 {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (φ₁ φ₂ : X → ℂ) : ℂ := Lift.pet μ 𝓕 φ₁ φ₂

abbrev Upq (W : HSp D) (ρ : D.what₂.Tau) : Type := UpqT (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2

abbrev Frames (W : HSp D) : Type :=
  ∀ ρ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D ρ)).1 ⊕ Fin (W.sig (tauE D ρ)).2) (Fin W.rank) ℂ

def IsFrames (W : HSp D) (A : Frames W) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 * A ρ = gramAt D W ρ

def conjFrame {p q n : ℕ} (Gm : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (b : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Gm⁻¹ * (Aᴴ * Formalism.UG.Jpq p q * b * A : Matrix (Fin n) (Fin n) ℂ)

def realMat (W : HSp D) (A : Frames W) (ρ : D.what₂.Tau) (b : Upq W ρ) : Matrix (Fin W.rank) (Fin W.rank) ℂ :=
  conjFrame (gramAt D W ρ) (A ρ) (UpqT.mat b)

def realElt (θ : Datum.InfFam D) (W : HSp D) (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : GA D W :=
  ((Finset.univ : Finset D.what₂.Tau).toList.map fun ρ => atTau θ W ρ (g ρ)).prod

abbrev FinCos (W : HSp D) (K : Subgroup (GA D W)) : Type := GfC W ⧸ K.subgroupOf (GfC W)

def FinCos.rep {W : HSp D} {K : Subgroup (GA D W)} (c : FinCos W K) : GA D W := (c.out : GfC W)


open Classical in
def quadSign (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ :=
  if (Ideal.primesOver v.asIdeal (𝓞 D.host.E)).ncard = 2 then 1 else -1

def quadTerm (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (i : ℕ) : ℝ :=
  quadSign D v ^ i / (Ideal.absNorm v.asIdeal : ℝ) ^ i

def dLoc (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : ℝ := ∏ i ∈ Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D v i)⁻¹

def dOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ℝ :=
  ∏' p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D p.1.1 p.2.1)⁻¹

def eulerOff (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ) : ℂ :=
  ∏' p : {w : HeightOneSpectrum (𝓞 D.host.E) // OffS D S w} × Fin D.R.r, (1 - x p.1.1 p.2)⁻¹


variable (D) in
def degAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : ℕ :=
  ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) := Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

abbrev levV (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    Subgroup (GL (Fin (Vc D i).rank) (Lev.EAf D)) := lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)

abbrev petW (i : Fin D.R.m) (F₁ F₂ : GA D (Wc D i) → ℂ) : ℂ := l2 (R.νW i) (R.fdW i) F₁ F₂

def upLift (i : Fin D.R.m) (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (F : GA D (Wc D i) → ℂ) (h : GA D (Vc D i)) : ℂ :=
  petW R i (fun g => Datum.thetaKO ω h g φ) F

def IsLiftData (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  R.Char F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io




variable (D) in
def DeltaNorm : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) =
    ∏ ρ : D.what₂.Tau, ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℂ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℂ))




variable (D) in
def MassLower : Prop :=
  ∀ i : Fin D.R.m, (Vc D i).IsPosDef → 1 / ((NumberField.Units.torsionOrder D.host.E : ℝ) ^ D.R.nV * (D.R.nV.factorial : ℝ)) ≤
    GlobalTheory.Mass.unitaryMass D.sp.cm.sig (Vc D i).gram (GlobalTheory.Mass.Levels.latStab (Vc D i))

end GlobalTheory.AdelicScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetOnto

theorem sigR_mem_intAE (D : D7) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha,
      ⟨D.sp.cm.sig x, (x.2 : IsIntegral ℤ (x : D.host.E)).map D.sp.cm.sig.toRingHom.toIntAlgHom⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem sigR_sigR (D : D7) (a : Af D.host.F ⊗[D.host.F] D.host.E) :
    sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig a) = a := by
  induction a using TensorProduct.inductionOn with
  | tmul a b => exact congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_star b)
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem ext_parts (D : D7) {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  exact Prod.ext ((he a).1.trans (h1.trans (he b).1.symm)) ((he a).2.trans (h2.trans (he b).2.symm))

theorem norm_one {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {a b : R} (h : a * b = 1) :
    a * σ b * σ (a * σ b) = 1 := by
  have h' := congrArg σ h
  rw [map_mul, map_one] at h'
  rw [map_mul, hσ]
  linear_combination (σ a * σ b) * h + h'

theorem infPart_det {D : D7} (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) : infPart D (matHom V k).1.det = 1 := by
  have h : infHom V k = 1 := hk
  have h' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  rw [← h', h, Units.val_one, Matrix.det_one]

theorem infPart_sigR (D : D7) (x : AE D) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) :=
  GlobalTheory.DetRootCong.map_sigR _ _ x

end GlobalTheory.DetOnto
end
