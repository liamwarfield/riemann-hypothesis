module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

variable {D : D7}

def leftSub (V : HSp D) {m : ℕ} (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (S : Finset (Fin m)) : Subgroup (GA D V) :=
  unip D.sp.cm.sig V.gram X S ⊔ (GQ V ⊓ levi D.sp.cm.sig V.gram X Y S)

def formsOn (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (S : Finset (Fin m)) (U : Subgroup (GA D V))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) : Set (GA D V → ℂ) :=
  {φ | IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y S : Set (GA D V)) φ ∧ (∀ u ∈ U, u ∈ GfC V → ∀ g, φ (g * u) = φ g) ∧
    (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) ∧ ∀ τ k, gelf θ V τ k φ = c τ k • φ}

section Sub

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {m : ℕ}
  {X Y : Matrix (Fin V.rank) (Fin m) D.host.E} {S : Finset (Fin m)} {U : Subgroup (GA D V)}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
  {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
  {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} {c : D.what₂.Tau → ℕ → ℂ}

theorem isSmModOn_add {Γ : Set (GA D V)} {f g : GA D V → ℂ} (hf : IsSmModOn D.sp.cm.sig V.gram Γ f)
    (hg : IsSmModOn D.sp.cm.sig V.gram Γ g) : IsSmModOn D.sp.cm.sig V.gram Γ (f + g) := by
  have sf : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f := hf.smooth
  have sg : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram g := hg.smooth
  refine ⟨fun γ hγ x => ?_, ?_, hf.cont.add hg.cont, GlobalTheory.UAut.isSm_add sf sg, ?_⟩
  · simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x]
  · obtain ⟨A, hA, eA⟩ := hf.level
    obtain ⟨B, hB, eB⟩ := hg.level
    refine ⟨A ⊓ B, hA.inter hB, fun k hk hk' x => ?_⟩
    simp only [Pi.add_apply, eA k hk.1 hk' x, eB k hk.2 hk' x]
  · obtain ⟨N, hN⟩ := hf.growth
    obtain ⟨M, hM⟩ := hg.growth
    refine ⟨max N M, fun l hl => ?_⟩
    obtain ⟨A, hA⟩ := hN l hl
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max A 0 + max B 0, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) := by
      exact_mod_cast GlobalTheory.AdelicU.one_le_height D.sp.cm.sig V.gram x
    have p1 := pow_le_pow_right₀ h1 (le_max_left N M)
    have p2 := pow_le_pow_right₀ h1 (le_max_right N M)
    have p0 : (0 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) ^ N := by positivity
    have p0' : (0 : ℝ) ≤ (GlobalTheory.AdelicU.height D.sp.cm.sig V.gram x : ℝ) ^ M := by positivity
    rw [GlobalTheory.UAut.foldr_add hl sf sg, Pi.add_apply, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((hA x).trans ?_) ((hB x).trans ?_))
    · exact (mul_le_mul_of_nonneg_right (le_max_left A 0) p0).trans
        (mul_le_mul_of_nonneg_left p1 (le_max_right A 0))
    · exact (mul_le_mul_of_nonneg_right (le_max_left B 0) p0').trans
        (mul_le_mul_of_nonneg_left p2 (le_max_right B 0))

theorem isSmModOn_smul {Γ : Set (GA D V)} (a : ℂ) {f : GA D V → ℂ} (hf : IsSmModOn D.sp.cm.sig V.gram Γ f) :
    IsSmModOn D.sp.cm.sig V.gram Γ (a • f) := by
  have sf : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f := hf.smooth
  refine ⟨fun γ hγ x => ?_, ?_, hf.cont.const_smul a, GlobalTheory.UAut.isSm_smul a sf, ?_⟩
  · simp only [Pi.smul_apply, hf.left γ hγ x]
  · obtain ⟨A, hA, eA⟩ := hf.level
    exact ⟨A, hA, fun k hk hk' x => by simp only [Pi.smul_apply, eA k hk hk' x]⟩
  · obtain ⟨N, hN⟩ := hf.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨A, hA⟩ := hN l hl
    refine ⟨‖a‖ * A, fun x => ?_⟩
    rw [GlobalTheory.UAut.foldr_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA x) (norm_nonneg _)

theorem formsOn_add (hθ : IsInfFam θ) {f g : GA D V → ℂ} (hf : f ∈ formsOn θ V X Y S U ε fr ρ c)
    (hg : g ∈ formsOn θ V X Y S U ε fr ρ c) : f + g ∈ formsOn θ V X Y S U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨isSmModOn_add f1 g1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.add_apply, f2 u hu hu' x, g2 u hu hu' x]
  · exact (AutFin.coeffSpan (ρ τ)).add_mem (f3 τ x) (g3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).add f (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ f1.smooth) g
      (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ g1.smooth), f4, g4, smul_add]

theorem formsOn_smul (a : ℂ) {f : GA D V → ℂ} (hf : f ∈ formsOn θ V X Y S U ε fr ρ c) :
    a • f ∈ formsOn θ V X Y S U ε fr ρ c := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  refine ⟨isSmModOn_smul a f1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
  · simp only [Pi.smul_apply, f2 u hu hu' x]
  · exact (AutFin.coeffSpan (ρ τ)).smul_mem a (f3 τ x)
  · rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul, f4, smul_comm]

theorem zero_mem_formsOn : (0 : GA D V → ℂ) ∈ formsOn θ V X Y S U ε fr ρ c := by
  refine ⟨isSmModOn_const _ _ _ 0, fun _ _ _ _ => rfl, fun τ x => (AutFin.coeffSpan (ρ τ)).zero_mem, fun τ k => ?_⟩
  have := (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 0
  simpa using this

theorem mem_formsOn_of_mem_span (hθ : IsInfFam θ) {f : GA D V → ℂ}
    (hf : f ∈ Submodule.span ℂ (formsOn θ V X Y S U ε fr ρ c)) : f ∈ formsOn θ V X Y S U ε fr ρ c := by
  induction hf using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact zero_mem_formsOn
  | add x y _ _ hx hy => exact formsOn_add hθ hx hy
  | smul a x _ hx => exact formsOn_smul a hx

end Sub

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterTrivialAlmostEverywhere
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterTrivialAlmostEverywhere
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

section FoundMeas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

variable (F : Type) [Field F] [NumberField F]

abbrev ratA : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range

theorem isFD_fundamentalSet (ν : Measure (AdeleRing (𝓞 F) F)) :
    IsAddFundamentalDomain (ratA F) (fundamentalSet F) ν := by
  refine IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet F).nullMeasurableSet fun x ↦ ?_
  obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_fundamentalSet F x
  refine ⟨⟨algebraMap F (AF F) (-k), -k, rfl⟩, ?_, ?_⟩
  · change algebraMap F (AF F) (-k) + x ∈ fundamentalSet F
    rwa [map_neg, neg_add_eq_sub]
  · rintro ⟨_, k', rfl⟩ h
    change algebraMap F (AF F) k' + x ∈ fundamentalSet F at h
    have hk' : -k' = k := huniq (-k') (by
      change x - algebraMap F (AF F) (-k') ∈ fundamentalSet F
      rwa [map_neg, sub_neg_eq_add, add_comm])
    refine Subtype.ext ?_
    change algebraMap F (AF F) k' = algebraMap F (AF F) (-k)
    rw [← hk', neg_neg]

variable {F}

theorem eq_adeleMeasure (db : Measure (AdeleRing (𝓞 F) F)) (hH : db.IsAddHaarMeasure) (D : Set (AF F))
    (hD : IsAddFundamentalDomain (ratA F) D db) (hD1 : db D = 1) : db = adeleMeasure F := by
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := countable_numberField F
  haveI : Countable (ratA F) := (AddMonoidHom.rangeRestrict_surjective _).countable
  have hl : db = Measure.addHaarScalarFactor db (adeleMeasure F) • adeleMeasure F :=
    Measure.isAddLeftInvariant_eq_smul db (adeleMeasure F)
  have h2 : db (fundamentalSet F) = 1 := ((isFD_fundamentalSet F db).measure_eq hD).trans hD1
  rw [hl, Measure.smul_apply, adeleMeasure_fundamentalSet] at h2
  have hc : Measure.addHaarScalarFactor db (adeleMeasure F) = 1 := by
    simpa [ENNReal.smul_def] using h2
  rw [hl, hc, one_smul]

theorem covol_transfer (db : @Measure (AF F) measAF) (hdb : IsCovolOne db)
    [m : MeasurableSpace (AF F)] (hm : m = measAF) :
    ∃ μ : Measure (AF F), (∀ s, μ s = db s) ∧ μ.IsAddHaarMeasure ∧
      ∃ D : Set (AF F), IsAddFundamentalDomain (ratA F) D μ ∧ μ D = 1 := by
  subst hm
  obtain ⟨h1, D, h2, h3⟩ := hdb
  exact ⟨db, fun _ => rfl, h1, D, h2, h3⟩

end FoundMeas

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

theorem prod_congr_inf {F : Type} [Field F] [NumberField F] {m₁ m₂ : MeasurableSpace (Ainf F)} (h : m₁ = m₂)
    (l₁ : @Measure (Ainf F) m₁) (l₂ : @Measure (Ainf F) m₂) (hl : ∀ s, l₁ s = l₂ s) (lf : Measure (Af F))
    (s : Set (Ainf F × Af F)) :
    @Measure.prod (Ainf F) (Af F) m₁ _ l₁ lf s = @Measure.prod (Ainf F) (Af F) m₂ _ l₂ lf s := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

theorem prod_meas_eq (F : Type) [Field F] [NumberField F] :
    (inferInstance : MeasurableSpace (Ainf F × Af F)) = (measAF : MeasurableSpace (AF F)) := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  exact (Prod.borelSpace (α := Ainf F) (β := Af F)).measurable_eq

def pairE (F : Type) [Field F] [NumberField F] : (Ainf F × Af F) ≃ᵐ AF F where
  toEquiv := Equiv.refl _
  measurable_toFun := by
    intro s hs
    rw [← prod_meas_eq F] at hs
    exact hs
  measurable_invFun := by
    intro s hs
    have hs' : @MeasurableSet (AF F) measAF s := by
      rw [← prod_meas_eq F]
      exact hs
    exact hs'

theorem prodM : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)), IsCovolOne db → ∀ laminf : Measure (Ainf F), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 ∧ ∃ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) ∧ MeasurePreserving e (laminf.prod lf) db := by
  intro F _ _ db hdb laminf hinf
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  refine ⟨lf, hlf, h1, pairE F, fun p => rfl, (pairE F).measurable, ?_⟩
  have hA : GroundTheory.Global.measurableSpace_adeleRing F = (measAF : MeasurableSpace (AF F)) :=
    (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq
  have hI : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨μ, hμ, hH, D, hD, hD1⟩ :=
    @covol_transfer F _ _ db hdb (GroundTheory.Global.measurableSpace_adeleRing F) hA
  obtain ⟨l, hl, hlH, E, hE, hE1⟩ :=
    @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hI
  have h2 := eq_adeleMeasure μ hH D hD hD1
  have h3 := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.adele_eq l hlH E hE hE1 lf hlf h1
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (pairE F).measurable hs]
  have e1 : (pairE F) ⁻¹' s = s := rfl
  rw [e1, ← prod_congr_inf hI l laminf hl lf s, ← hμ s]
  have e2 := congrArg (fun ν => ν s) h3
  have e3 := congrArg (fun ν => ν s) h2
  exact e2.trans e3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterTrivialAlmostEverywhereStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_finite_infinite_product : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)), IsCovolOne db → ∀ laminf : Measure (Ainf F), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 ∧ ∃ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) ∧ MeasurePreserving e (laminf.prod lf) db := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM.prodM | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM.prodM | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM.prodM <;> assumption)
end
end
