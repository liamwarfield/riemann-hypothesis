module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.TwGen

variable {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}

def genHom (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n) ⟶ P :=
  GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) ≫
    (GlobalTheory.Twist.twistZAddIso P hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso P hH).inv

def genSub (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) : Subobject P :=
  imageSubobject (genHom hH n b)

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMem
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem sectionHom_app_comp {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G) (s : Γ(F, ⊤)) :
    GlobalTheory.QCoh.sectionHom (φ.app ⊤ s) = GlobalTheory.QCoh.sectionHom s ≫ φ := by
  ext V a
  change (GlobalTheory.QCoh.sectionHom (φ.app ⊤ s)).app V a = φ.app V ((GlobalTheory.QCoh.sectionHom s).app V a)
  rw [GlobalTheory.QCoh.sectionHom_app, GlobalTheory.QCoh.sectionHom_app, Scheme.Modules.Hom.app_smul,
    GlobalTheory.Twist.app_resM]

theorem twistZZeroIso_inv_naturality {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {F G : X.Modules} (u : F ⟶ G) :
    (GlobalTheory.Twist.twistZZeroIso F hH).inv ≫ u =
      GlobalTheory.Twist.map (GlobalTheory.lbZPow H 0) u ≫ (GlobalTheory.Twist.twistZZeroIso G hH).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine GlobalTheory.Twist.zhom_ext fun V t i => ?_
  change GlobalTheory.Twist.zcoord ((GlobalTheory.Twist.twistZZeroIso G hH).hom.app V (u.app V t)) i =
    GlobalTheory.Twist.zcoord ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H 0) u).app V
      ((GlobalTheory.Twist.twistZZeroIso F hH).hom.app V t)) i
  rw [GlobalTheory.Twist.zcoord_twistZZeroIso_hom_app, GlobalTheory.Twist.zcoord_map_app,
    GlobalTheory.Twist.zcoord_twistZZeroIso_hom_app, GlobalTheory.Twist.app_resM]

theorem genHom_map_app {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {F G : X.Modules} (u : F ⟶ G) (n : ℤ) (b : Γ(GlobalTheory.twistZ F H n, ⊤)) :
    genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) u).app ⊤ b) = genHom hH n b ≫ u := by
  simp only [genHom, Category.assoc, twistZZeroIso_inv_naturality hH u]
  rw [sectionHom_app_comp]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (GlobalTheory.Twist.twistZAddIso_naturality_assoc hH
    (add_neg_cancel n) u (GlobalTheory.Twist.twistZZeroIso G hH).inv))
  exact Category.assoc (GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b))
    (GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) u))
    ((GlobalTheory.Twist.twistZAddIso G hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso G hH).inv)

theorem genSub_le : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (S : Subobject P) (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), b ∈ twSecs H n S → genSub hH n b ≤ S := by
  rintro X H hH P S n _ ⟨b', rfl⟩
  exact imageSubobject_le _ (genHom hH n b') (genHom_map_app hH S.arrow n b').symm

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeOfTwistedSectionMemStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules} (S : Subobject P) (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), b ∈ twSecs H n S → genSub hH n b ≤ S := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheaf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheaf
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem le_of_epi_sectionsHom {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules} (S B : Subobject P) (n : ℤ) {k : ℕ}
    (s : Fin k → Γ(GlobalTheory.twistZ (S : X.Modules) H n, ⊤)) (hs : Epi (GlobalTheory.QCoh.sectionsHom s))
    (hB : ∀ i, genSub hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)) ≤ B) : S ≤ B := by
  have hL' := GlobalTheory.Twist.isLB_lbZPow hH (-n)
  have h₁ := (GlobalTheory.Twist.epi_map_iff hL' (GlobalTheory.QCoh.sectionsHom s)).2 hs
  have := GlobalTheory.Twist.preservesColimits_twistFunctor hL'
  let T := GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))
  let E : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (S : X.Modules) :=
    GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫
      (GlobalTheory.Twist.twistZAddIso (S : X.Modules) hH (add_neg_cancel n)).hom ≫
      (GlobalTheory.Twist.twistZZeroIso (S : X.Modules) hH).inv
  haveI hE : Epi E := epi_comp' h₁ inferInstance
  have key : ∀ i, T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) ≫ E =
      genHom hH n (s i) := fun i => by
    have e : Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i ≫ GlobalTheory.QCoh.sectionsHom s =
        GlobalTheory.QCoh.sectionHom (s i) := Sigma.ι_desc _ _
    rw [genHom, ← e]
    change T.map _ ≫ T.map _ ≫ _ = T.map (_ ≫ _) ≫ _
    exact (Category.assoc (T.map _) (T.map _) _).symm
  let g : ∀ i : Fin k, T.obj (GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) := fun i =>
    factorThruImageSubobject (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i))) ≫
      Subobject.ofLE _ _ (hB i)
  have hg : ∀ i, g i ≫ B.arrow = genHom hH n (s i) ≫ S.arrow := fun i => by
    rw [← genHom_map_app hH S.arrow n (s i)]
    exact (Category.assoc _ _ _).trans ((congrArg _ (Subobject.ofLE_arrow _)).trans
      (imageSubobject_arrow_comp
        (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)))))
  let c := PreservesCoproduct.iso T (fun _ : Fin k => GlobalTheory.QCoh.structureModule X)
  let t : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) :=
    c.hom ≫ Sigma.desc g
  have ht : t ≫ B.arrow = E ≫ S.arrow := by
    have hι : ∀ i, Sigma.ι (fun _ : Fin k => T.obj (GlobalTheory.QCoh.structureModule X)) i ≫ c.inv =
        T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) :=
      fun i => ι_comp_sigmaComparison T _ i
    have h₂ : c.inv ≫ t = Sigma.desc g := Iso.inv_hom_id_assoc c _
    have h₃ : c.inv ≫ t ≫ B.arrow = c.inv ≫ E ≫ S.arrow := by
      rw [← Category.assoc, h₂]
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Sigma.ι_desc, hg i, ← key i, ← Category.assoc, ← Category.assoc,
        hι i]
      rfl
    exact (cancel_epi c.inv).1 h₃
  haveI : StrongEpi E := strongEpi_of_epi E
  have sq : CommSq t E B.arrow S.arrow := ⟨ht⟩
  exact Subobject.le_of_comm sq.lift sq.fac_right

theorem le_of_genSub_le : ∀ {X : Scheme.{0}} [IsNoetherian X] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}
    (hA : GlobalTheory.IsAmpleLB H) {P : X.Modules} (S : Subobject P), IsCoherent (S : X.Modules) →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ B : Subobject P,
      (∀ b ∈ twSecs H n S, genSub hA.isLB n b ≤ B) → S ≤ B := by
  intro X _ H hA P S hS
  haveI : GlobalTheory.QCoh.IsFiniteQC (S : X.Modules) := ⟨hS.1, hS.2⟩
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.1
    (hA.eventually_isGloballyGenerated_twistZ (S : X.Modules))
  refine ⟨n₀, fun n hn B hB => ?_⟩
  obtain ⟨k, s, hs⟩ := GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 (h₀ n hn)
  exact le_of_epi_sectionsHom hA.isLB S B n s ((GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs)
    fun i => hB _ ⟨s i, rfl⟩

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_twist_sections_generate_subsheaf : ∀ {X : Scheme.{0}} [IsNoetherian X] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hA : GlobalTheory.IsAmpleLB H) {P : X.Modules} (S : Subobject P), IsCoherent (S : X.Modules) → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ B : Subobject P, (∀ b ∈ twSecs H n S, genSub hA.isLB n b ≤ B) → S ≤ B := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.le_of_genSub_le | exact GlobalTheory.CompanionTheory.GE.TwGen.le_of_genSub_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.le_of_genSub_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPower
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPower
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem mem_twSecs_of_mem_twPow {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (n : ℤ) (m : ℕ) : twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  letI : Algebra A Γ(X, ⊤) := GroundTheory.Arith.SchemeCoh.overAlgebra (CommRingCat.of A)
  have fac : ∀ a ∈ I ^ m, ∃ ψ : P ⟶ GroundTheory.Arith.SchemeCoh.idealPow I P m,
      ψ ≫ GroundTheory.Arith.SchemeCoh.idealPowι I P m = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    intro a ha
    rw [← GroundTheory.Arith.SchemeCoh.span_idealGen (I ^ m)] at ha
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
    let u : P ⟶ ⨁ fun _ : Fin (GroundTheory.Arith.SchemeCoh.idealGenNum (I ^ m)) => P :=
      biproduct.lift fun k => GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c k))
    have hu : u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m) = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      rw [← hc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [u, GroundTheory.Arith.SchemeCoh.idealSumMap, biproduct.lift_desc, GroundTheory.Arith.SchemeCoh.smulHom_comp_smulHom, map_sum, GroundTheory.Arith.SchemeCoh.smulHom_sum,
        smul_eq_mul, map_mul]
    refine ⟨kernel.lift (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))) (u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))
      (by rw [Category.assoc, cokernel.condition, comp_zero]), ?_⟩
    rw [← hu]
    exact kernel.lift_ι _ _ _
  have act : ∀ (r : Γ(X, ⊤)) (s : Γ(GlobalTheory.twistZ P H n, ⊤)),
      ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (GroundTheory.Arith.SchemeCoh.smulHom P r)) ⊤) s
        = GroundTheory.Arith.SchemeCoh.restrictTop ⊤ r • s := by
    intro r s
    rw [GlobalTheory.Twist.sec_ext_iff]
    intro i
    rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]
    congr 1
    exact (GroundTheory.Arith.SchemeCoh.restrictTop_restrict _ r).symm
  have base : ∀ a ∈ I ^ m, ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤ a • s ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)) := by
    intro a ha s
    obtain ⟨ψ, hψ⟩ := fac a ha
    have e : (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (powSub I P m).arrow
        = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      show (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (Subobject.mk (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).arrow = _
      rw [Category.assoc, Subobject.underlyingIso_arrow, hψ]
    refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n)
      (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv)) ⊤) s, ?_⟩
    have h2 := act (algebraMap A Γ(X, ⊤) a) s
    rw [← e] at h2
    erw [GlobalTheory.Twist.map_comp, Scheme.Modules.Hom.comp_app] at h2
    try erw [ConcreteCategory.comp_apply] at h2
    exact h2
  let K : Ideal Γ(X, ⊤) :=
    { carrier := {r | ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), r • s ∈ Set.range
        (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤))}
      add_mem' := by
        intro x y hx hy s
        obtain ⟨u, hu⟩ := hx s
        obtain ⟨v, hv⟩ := hy s
        exact ⟨u + v, by rw [map_add (f := _), hu, hv, add_smul]⟩
      zero_mem' := by
        intro s
        exact ⟨0, by rw [map_zero, zero_smul]⟩
      smul_mem' := by
        intro t x hx s
        obtain ⟨u, hu⟩ := hx (t • s)
        exact ⟨u, by rw [hu, smul_eq_mul, mul_comm, mul_smul]⟩ }
  have hJ : Ideal.map (GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤) (I ^ m) ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact base a ha
  intro c hc
  simp only [twPow, SetLike.mem_coe] at hc
  refine Submodule.smul_induction_on (p := fun x => x ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)))
    hc ?_ ?_
  · intro r hr s _
    exact hJ hr s
  · intro x y hx hy
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]⟩

theorem genSub_le_powSub : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (m : ℕ) (c : Γ(GlobalTheory.twistZ P H n, ⊤)),
    c ∈ twPow I H n P m → genSub hH n c ≤ powSub I P m := by
  intro A _ _ I X _ H hH P _ n m c hc
  exact genSub_le hH (powSub I P m) n c (mem_twSecs_of_mem_twPow I H P n m hc)

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPowerStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_le_ideal_power : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (m : ℕ) (c : Γ(GlobalTheory.twistZ P H n, ⊤)), c ∈ twPow I H n P m → genSub hH n c ≤ powSub I P m := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_le_powSub | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_le_powSub | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_le_powSub <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherent
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem isQuasicoherent_imageSubobject {X : Scheme.{0}} {A B : X.Modules}
    (hA : A.IsQuasicoherent) (hB : B.IsQuasicoherent) (f : A ⟶ B) :
    (imageSubobject f : X.Modules).IsQuasicoherent := by
  haveI := hA
  haveI := hB
  have hK : (kernel (cokernel.π f)).IsQuasicoherent := inferInstance
  exact GlobalTheory.QCoh.isQuasicoherent_of_iso
    (Abelian.imageIsoImage f ≪≫ (imageSubobjectIso f).symm)

theorem isQuasicoherent_genSub : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)),
    (genSub hH n b : X.Modules).IsQuasicoherent := by
  intro X H hH P hP n b
  have hO : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := inferInstance
  have hS : (GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n)).IsQuasicoherent :=
    GlobalTheory.Twist.isQuasicoherent_twist (F := SheafOfModules.unit X.ringCatSheaf)
      (GlobalTheory.Twist.isLB_lbZPow hH (-n))
  exact isQuasicoherent_imageSubobject hS hP _

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafQuasicoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_quasicoherent : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), (genSub hH n b : X.Modules).IsQuasicoherent := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub | exact GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.isQuasicoherent_genSub <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheaf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheaf
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
  GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE

theorem eq_of_le_of_secs_subset {X : Scheme.{0}} {P : X.Modules} {ι : Type*} (𝒰 : ι → X.Opens)
    (hcov : TopologicalSpace.IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i)) {M B : Subobject P}
    (hM : (M : X.Modules).IsQuasicoherent) (hB : (B : X.Modules).IsQuasicoherent) (hle : M ≤ B)
    (h : ∀ i, secs B (𝒰 i) ⊆ secs M (𝒰 i)) : B = M := by
  haveI := hM
  haveI := hB
  have hepi : Epi (Subobject.ofLE M B hle) := by
    refine (GlobalTheory.QCoh.epi_iff_affineCover 𝒰 hcov haff _).2 fun i y ↦ ?_
    obtain ⟨x, hx⟩ := h i ⟨y, rfl⟩
    refine ⟨x, GlobalTheory.QCoh.injective_app_of_mono B.arrow _ ?_⟩
    change (Subobject.ofLE M B hle ≫ B.arrow).app _ x = _
    rw [Subobject.ofLE_arrow]
    exact hx
  haveI hmono : Mono (Subobject.ofLE M B hle) := mono_of_mono_fac (Subobject.ofLE_arrow hle)
  haveI : IsIso (Subobject.ofLE M B hle) := isIso_of_mono_of_epi _
  refine le_antisymm (Subobject.le_of_comm (inv (Subobject.ofLE M B hle)) ?_) hle
  rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]

theorem exists_maximal_qcoh_subobject {X : Scheme.{0}} [IsNoetherian X] {P : X.Modules}
    (hP : IsCoherent P) (F : Set (Subobject P)) (hF : F.Nonempty)
    (hq : ∀ B ∈ F, (B : X.Modules).IsQuasicoherent) :
    ∃ M ∈ F, ∀ B ∈ F, M ≤ B → B = M := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ ((U : X.Opens) : Set X)) (fun U ↦ U.1.isOpen) (fun x _ ↦ by
      obtain ⟨U, ⟨V, hV, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩)
  let 𝒰 : t → X.Opens := fun i ↦ (i.1 : X.Opens)
  have hcov : TopologicalSpace.IsOpenCover 𝒰 := top_le_iff.1 fun x _ ↦ by
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hx⟩
  have haff : ∀ i, IsAffineOpen (𝒰 i) := fun i ↦ i.1.2
  haveI hnoeth : ∀ i : t, IsNoetherianRing Γ(X, 𝒰 i) := fun i ↦
    IsLocallyNoetherian.component_noetherian ⟨𝒰 i, haff i⟩
  haveI hfin : ∀ i : t, Module.Finite Γ(X, 𝒰 i) Γ(P, 𝒰 i) := fun i ↦ hP.2 _ (haff i)
  haveI hwf : ∀ i : t, WellFoundedLT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ := fun i ↦
    inferInstanceAs (WellFoundedGT (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i)))
  let g : Subobject P → ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ :=
    fun B i ↦ OrderDual.toDual (secsSub B (𝒰 i))
  have hmin := (wellFounded_lt (α := ∀ i : t, (Submodule Γ(X, 𝒰 i) Γ(P, 𝒰 i))ᵒᵈ)).has_min
    (g '' F) (hF.image g)
  obtain ⟨_, ⟨M, hM, rfl⟩, hmin⟩ := hmin
  refine ⟨M, hM, fun B hB hle ↦ ?_⟩
  have hle' : g B ≤ g M := fun i ↦ by
    change secsSub M (𝒰 i) ≤ secsSub B (𝒰 i)
    rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.ofLE M B hle).app (𝒰 i) x, ?_⟩
    rw [← Subobject.ofLE_arrow hle]
    rfl
  have heq : g B = g M := by
    by_contra hne
    exact hmin _ ⟨B, hB, rfl⟩ (lt_of_le_of_ne hle' hne)
  refine eq_of_le_of_secs_subset 𝒰 hcov haff (hq M hM) (hq B hB) hle fun i ↦ ?_
  have hi : secsSub B (𝒰 i) = secsSub M (𝒰 i) := congrFun heq i
  intro y hy
  have hy' : y ∈ secsSub B (𝒰 i) := hy
  rw [hi] at hy'
  exact hy'

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheafStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_noetherian_maximal_subsheaf : ∀ {X : Scheme.{0}} [IsNoetherian X] {P : X.Modules}, IsCoherent P → ∀ F : Set (Subobject P), F.Nonempty → (∀ B ∈ F, (B : X.Modules).IsQuasicoherent) → ∃ M ∈ F, ∀ B ∈ F, M ≤ B → B = M := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | exact GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem imageSubobject_add_le {C : Type*} [Category C] [Preadditive C] [HasImages C]
    [HasBinaryCoproducts C] {A B : C} (f g : A ⟶ B) :
    imageSubobject (f + g) ≤ imageSubobject f ⊔ imageSubobject g := by
  have key : ∀ h : A ⟶ B, (imageSubobject h).Factors h := fun h => by
    have := Subobject.factors_comp_arrow (P := imageSubobject h) (factorThruImageSubobject h)
    rwa [imageSubobject_arrow_comp] at this
  have h := Subobject.factors_add f g
    (Subobject.factors_of_le f le_sup_left (key f)) (Subobject.factors_of_le g le_sup_right (key g))
  exact imageSubobject_le (f + g) _ (Subobject.factorThru_arrow _ _ h)

theorem sectionHom_add {X : Scheme.{0}} {F : X.Modules} (b c : Γ(F, ⊤)) :
    GlobalTheory.QCoh.sectionHom (b + c) = GlobalTheory.QCoh.sectionHom b + GlobalTheory.QCoh.sectionHom c := by
  ext V a
  change GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) (b + c) =
    GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) b +
      GlobalTheory.QCoh.structureModuleSectionsEquiv V a • GlobalTheory.Twist.resM F (le_top : V ≤ ⊤) c
  rw [map_add (f := _), smul_add]

theorem genHom_add {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genHom hH n (b + c) = genHom hH n b + genHom hH n c := by
  have h : GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom (b + c)) =
      GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) +
        GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom c) := by
    rw [sectionHom_add]
    exact (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))).map_add
  simp only [genHom, h, Preadditive.add_comp]

theorem genSub_add_le {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  unfold genSub
  simp only [genHom_add]
  exact imageSubobject_add_le _ _

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafAddLeSupStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_subsheaf_add_le_sup : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b c : Γ(GlobalTheory.twistZ P H n, ⊤)), genSub hH n (b + c) ≤ genSub hH n b ⊔ genSub hH n c := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | exact GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.genSub_add_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGenerators
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem exists_alg_of_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  intro A _ _ I X _ _ H hA P hP S hS n₁ W hW hgen
  have hH := hA.isLB
  let F : Set (Subobject P) := {B | (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ≤ S e}
  have h0 : (0 : Γ(GlobalTheory.twistZ P H n₁, ⊤)) ∈ twSecs H n₁ (S 0) := ⟨0, map_zero _⟩
  obtain ⟨b₀, hb₀, -⟩ := hgen n₁ le_rfl 0 0 h0
  have hF : F.Nonempty :=
    ⟨genSub hH n₁ b₀, GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n₁ b₀, fun e => GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n₁ b₀ (hW n₁ e hb₀)⟩
  obtain ⟨M, ⟨hMq, hMS⟩, hMmax⟩ := GlobalTheory.T.coherent_noetherian_maximal_subsheaf hP F hF (fun B hB => hB.1)
  have hgenM : ∀ n, ∀ b ∈ W n, genSub hH n b ≤ M := by
    intro n b hb
    have hmem : M ⊔ genSub hH n b ∈ F :=
      ⟨(GlobalTheory.T.quasicoherent_sup_sections hP.1 M (genSub hH n b) hMq (GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n b)).1,
        fun e => sup_le (hMS e) (GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n b (hW n e hb))⟩
    rw [← hMmax _ hmem le_sup_left]
    exact le_sup_right
  refine ⟨M, hMq, fun e => le_antisymm (sup_le (hMS e) (hS.pow_le e)) ?_⟩
  have hSe : IsCoherent (S e : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.ample_twist_sections_generate_subsheaf hA (S e) hSe
  refine hn₀ (max n₀ n₁) (le_max_left _ _) _ fun x hx => ?_
  obtain ⟨b, hb, hxb⟩ := hgen (max n₀ n₁) (le_max_right _ _) e x hx
  rw [← add_sub_cancel b x]
  exact (GlobalTheory.T.generated_subsheaf_add_le_sup hH _ b (x - b)).trans (sup_le_sup (hgenM _ b hb) (GlobalTheory.T.generated_subsheaf_le_ideal_power I hH hP.1 _ _ _ hxb))

end GlobalTheory.CompanionTheory.GE.TwGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGeneratorsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sections_uniform_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs | exact GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs <;> assumption)
end
