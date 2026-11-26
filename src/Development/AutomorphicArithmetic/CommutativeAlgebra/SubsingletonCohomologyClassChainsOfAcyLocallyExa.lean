module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSuppOfSectionsV
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish :
    ∀ (Q : Scheme.{0} → Prop) (G : Shv ℤ), (∀ U : Scheme.{0}, Q U → Subsingleton (Sec G U)) → ∀ P : PSh, Supp Q P → ∀ n : ℤ, Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) G n) := by
  intro Q G hG P hP n
  apply UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology
  haveI : (res ℤ G).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ G).1
  refine GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support ℤ (disc.obj P) (res ℤ G) ?_ n
  intro U hU m b hb
  have hQ : Q U := hP U hU
  haveI : Subsingleton (Sec G U) := hG U hQ
  obtain ⟨h0, -, h3, hneg⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ G U
  have hz : ∀ (c : Sec ((res ℤ G).X m) U), b = c → c = 0 →
      Loc U fun V g => ∃ a : Sec ((res ℤ G).X (m - 1)) V,
        Sec.map ((res ℤ G).d (m - 1) m) a = Sec.res g b := by
    rintro c rfl rfl
    refine ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => ⟨0, ?_⟩⟩
    simp
  rcases lt_trichotomy m 0 with h | h | h
  · haveI := hneg m h
    exact hz b rfl (Subsingleton.elim _ _)
  · subst h
    obtain ⟨a, rfl⟩ := (h0 b).1 hb
    refine hz _ rfl ?_
    rw [Subsingleton.elim a 0]
    simp
  · exact h3 (m - 1) m (m + 1) h (by omega) b rfl hb
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.HypercohomologyPostClEqClComp
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.hypercohomology_post_cl_eq_cl_comp :
    ∀ {M F G : Shv ℤ} (f : M ⟶ F) (g : F ⟶ G), HK.post ℤ (sgl M) g 0 (cl f) = cl (f ≫ g) := by
  intro M F G f g
  have hg : resAug F ≫ resMap ℤ g = (CochainComplex.singleFunctor (Shv ℤ) 0).map g ≫ resAug G :=
    ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.2.2 G g).1
  have key : ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F) ≫ resMap ℤ g =
      (CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G := by
    rw [Category.assoc, hg, Functor.map_comp, Category.assoc]
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F))
    (Cocycle.ofHom (resMap ℤ g)) (add_zero 0)) = CohomologyClass.mk (Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map (f ≫ g) ≫ resAug G))
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  rw [← key]
  simp [zcomp, Cochain.ofHom_comp]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPrimitiveFreeOfAcyLocallyExact
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyAndLiftOfLocallySurjectiveExact
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToKernelOfShortExactVanishingSecti
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → (∀ U : Scheme.{0}, Q U → Subsingleton (Sec S.X₃ U)) → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₂, ∃ h : (free ℤ).obj P ⟶ S.X₁, h ≫ S.f = f := by
  intro Q S hS hQ P hP f
  have hsub := UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q S.X₃ hQ P hP 0
  have hz : f ≫ S.g = 0 := by
    apply (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1
    exact Subsingleton.elim _ _
  haveI := hS.mono_f
  exact ⟨hS.exact.lift f hz, hS.exact.lift_f f hz⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToMiddleOfShortExactAcy
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_middle_of_shortExact_acy :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₃, ∃ h : (free ℤ).obj P ⟶ S.X₂, h ≫ S.g = f := by
  intro Q S hS hA P hP f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) 0).2.1
  have hsub := hA P hP (0 + 1) (by norm_num)
  have h0 : HK.ext ℤ (sgl ((free ℤ).obj P)) z 0 (0 + 1) rfl (cl f) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (e (cl f)).1 h0
  obtain ⟨h, rfl⟩ := (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).2 y
  refine ⟨h, (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1 ?_⟩
  rw [← UpperTheory.hypercohomology_post_cl_eq_cl_comp]
  exact hy
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.AcyRightOfShortExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.acy_right_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₂ → Acy Q S.X₃ := by
  intro Q S hS h1 h2 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).2.1
  haveI := h1 P hP (n + 1) (by omega)
  haveI := h2 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₃ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem restriction_trans {F : Shv ℤ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

private theorem res_map_of_sheaf_morphism {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U) (b : Sec F U) :
    Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem map_map_eq_zero {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) (h : φ ≫ ψ = 0) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map ψ (Sec.map φ a) = 0 := by
  have h2 := congrArg (fun t : F ⟶ H => (t.hom.app (op U)).hom a) h
  simpa [Sec.map] using h2

private theorem local_bind {U : Scheme.{0}} {P R : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => R W (k ≫ g)) : Loc U R := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose T hT hTR using fun (V : Scheme.{0}) (g : V ⟶ U) (H : S.arrows g) => h V g (hSP V g H)
  refine ⟨Sieve.bind S.arrows fun Y f H => T Y f H, ?_, ?_⟩
  · exact Scheme.etaleTopology.bind_covering hS fun Y f H => hT Y f H
  · rintro W _ ⟨Y, k, g, H, hk, rfl⟩
    exact hTR Y g H W k hk

theorem UpperTheory.acy_and_lift_of_locally_surjective_exact :
    ∀ (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → ∀ (A C₁ Z : Shv ℤ) (i : A ⟶ C₁) (d : C₁ ⟶ Z) (w : i ≫ d = 0), Mono i → (ShortComplex.mk i d w).Exact → (∀ U : Scheme.{0}, Q U → ∀ b : Sec Z U, Loc U fun V g => ∃ a : Sec C₁ V, Sec.map d a = Sec.res g b) → Acy Q A → Acy Q C₁ → Acy Q Z ∧ ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ Z, ∃ h : (free ℤ).obj P ⟶ C₁, h ≫ d = f := by
  intro Q hQ A C₁ Z i d w hi hex hloc hA hC
  have hfac : Abelian.factorThruImage d ≫ Abelian.image.ι d = d := Abelian.image.fac d
  have w1 : i ≫ Abelian.factorThruImage d = 0 := by
    rw [← cancel_mono (Abelian.image.ι d), Category.assoc, hfac, w, zero_comp]
  let S1 := ShortComplex.mk i (Abelian.factorThruImage d) w1
  have hS1ex : S1.Exact := by
    let φ : S1 ⟶ ShortComplex.mk i d w :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι d
        comm₁₂ := by simp [S1]
        comm₂₃ := by simp [S1, hfac] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex
  have hS1 : S1.ShortExact := { exact := hS1ex, mono_f := hi, epi_g := by dsimp [S1]; infer_instance }
  have w2 : Abelian.image.ι d ≫ cokernel.π d = 0 := by
    rw [← cancel_epi (Abelian.factorThruImage d), ← Category.assoc, hfac, cokernel.condition, comp_zero]
  let S2 := ShortComplex.mk (Abelian.image.ι d) (cokernel.π d) w2
  have hS2 : S2.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := by dsimp [S2]; infer_instance
      epi_g := by dsimp [S2]; infer_instance }
  have hsub : ∀ U : Scheme.{0}, Q U → Subsingleton (Sec (cokernel d) U) := by
    intro U hU
    refine ⟨fun s t => ?_⟩
    have hz : ∀ s : Sec (cokernel d) U, s = 0 := by
      intro s
      have hl := ((GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (cokernel.π d)).2.2.1.1 inferInstance) U s
      have hl2 : Loc U fun W k => Sec.res k s = Sec.res k (0 : Sec (cokernel d) U) := by
        refine local_bind hl ?_
        rintro V g ⟨z, hz⟩
        obtain ⟨T, hT, hTz⟩ := hloc V (hQ g hU) z
        refine ⟨T, hT, ?_⟩
        rintro W k hk
        obtain ⟨a, ha⟩ := hTz W k hk
        rw [restriction_trans, ← hz, res_map_of_sheaf_morphism, ← ha, map_map_eq_zero d (cokernel.π d) (cokernel.condition d)]
        simp [Sec.res]
      exact (GlobalTheory.T.etaleSheafSections_ext_and_glue ℤ (cokernel d) U).1 s 0 hl2
    rw [hz s, hz t]
  have hI : Acy Q (Abelian.image d) := UpperTheory.acy_right_of_shortExact Q S1 hS1 hA hC
  have hK : Acy Q (cokernel d) := fun P hP n _ => UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q _ hsub P hP n
  refine ⟨UpperTheory.acy_middle_of_shortExact Q S2 hS2 hI hK, ?_⟩
  intro P hP f
  obtain ⟨h1, hh1⟩ := UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections Q S2 hS2 hsub P hP f
  obtain ⟨h2, hh2⟩ := UpperTheory.exists_lift_free_to_middle_of_shortExact_acy Q S1 hS1 hA P hP h1
  refine ⟨h2, ?_⟩
  dsimp [S1, S2] at hh1 hh2
  rw [← hfac, ← Category.assoc, hh2, hh1]
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem sec_comp {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem sec_zero {F G : Shv ℤ} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private theorem UpperTheory.sec_map_res_comm {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) =
    (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem UpperTheory.injective_sec_map_of_mono {F G : Shv ℤ} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

private theorem UpperTheory.acy_of_isZero (Q : Scheme.{0} → Prop) (G : Shv ℤ) (hG : IsZero G) :
    Acy Q G := by
  intro P hP n _
  have hid : (𝟙 G : G ⟶ G) = 0 := hG.eq_of_src _ _
  have hsub : ∀ {U : Scheme.{0}} (x : Sec G U), x = 0 := fun {U} x => by
    calc x = Sec.map (𝟙 G) x := rfl
      _ = 0 := by rw [hid, sec_zero]
  exact UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q G (fun U _ => ⟨fun x y => by rw [hsub x, hsub y]⟩) P hP n

theorem UpperTheory.exists_primitive_free_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → (∀ s, Acy Q (C.X s)) → (∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ P : PSh, Supp Q P → ∀ (j : ℤ) (f : (free ℤ).obj P ⟶ C.X j), f ≫ C.d j (j + 1) = 0 → ∃ g : (free ℤ).obj P ⟶ C.X (j - 1), g ≫ C.d (j - 1) j = f := by
  intro C a _ Q hQ hacy hexact P hP j f hf
  have step : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) →
      Acy Q (kernel (C.d (i + 1) (i + 1 + 1))) ∧ ∀ P : PSh, Supp Q P →
        ∀ f : (free ℤ).obj P ⟶ kernel (C.d (i + 1) (i + 1 + 1)),
          ∃ h, h ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
            (C.d_comp_d _ _ _) = f := by
    intro i hi
    have w : kernel.ι (C.d i (i + 1)) ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
        (C.d_comp_d _ _ _) = 0 := by
      rw [← cancel_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))), Category.assoc, kernel.lift_ι,
        kernel.condition, zero_comp]
    have hex : (ShortComplex.mk (kernel.ι (C.d i (i + 1)))
        (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _)) w).Exact := by
      apply ShortComplex.exact_of_f_is_kernel
      refine KernelFork.IsLimit.ofι _ _
        (fun g' hg' => kernel.lift (C.d i (i + 1)) g' (by
          rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
            ← Category.assoc, hg', zero_comp]))
        (fun g' hg' => kernel.lift_ι _ _ _)
        (fun g' hg' m hm => by
          rw [← cancel_mono (kernel.ι (C.d i (i + 1))), kernel.lift_ι]
          exact hm)
    have hloc : ∀ U : Scheme.{0}, Q U → ∀ b : Sec (kernel (C.d (i + 1) (i + 1 + 1))) U,
        Loc U fun V g => ∃ c, Sec.map (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
          (C.d_comp_d _ _ _)) c = Sec.res g b := by
      intro U hU b
      have hb : Sec.map (C.d (i + 1) (i + 1 + 1))
          (Sec.map (kernel.ι (C.d (i + 1) (i + 1 + 1))) b) = 0 := by
        rw [← sec_comp, kernel.condition, sec_zero]
      have h1 := hexact U hU (i + 1) _ hb
      rw [show i + 1 - 1 = i by omega] at h1
      obtain ⟨S, hS, hSp⟩ := h1
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨c, hc⟩ := hSp V g hg
      refine ⟨c, UpperTheory.injective_sec_map_of_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))) V ?_⟩
      show Sec.map _ (Sec.map _ c) = Sec.map _ (Sec.res g b)
      rw [← sec_comp, kernel.lift_ι, hc, UpperTheory.sec_map_res_comm]
    exact UpperTheory.acy_and_lift_of_locally_surjective_exact Q @hQ _ _ _ _ _ w inferInstance hex hloc hi (hacy i)
  have hAcy : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) := by
    intro i
    have below (n : ℤ) (hn : n < a) : Acy Q (kernel (C.d n (n + 1))) :=
      UpperTheory.acy_of_isZero Q _
        (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a n hn))
    refine Int.inductionOn' (motive := fun n => Acy Q (kernel (C.d n (n + 1)))) i (a - 1)
      (below (a - 1) (by omega)) (fun n _ ih => (step n ih).1) ?_
    intro n hn _
    exact below (n - 1) (by omega)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show i + 1 - 1 = i by omega]
  obtain ⟨h, hh⟩ := (step i (hAcy i)).2 P hP (kernel.lift _ f hf)
  refine ⟨h, ?_⟩
  rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
    ← Category.assoc, hh, kernel.lift_ι]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonCohomologyClassOfBoundedOfCyclesLift
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory

set_option backward.isDefEq.respectTransparency false in
private theorem hb_step {C : Type*} [Category C] [Preadditive C] (K D : CochainComplex C ℤ)
    (H : ∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 →
      ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f)
    (n p₀ : ℤ) (z : Cochain K D n) (hz : δ n (n + 1) z = 0)
    (hv : ∀ (p q : ℤ) (hpq : p + n = q), p₀ < p → z.v p q hpq = 0) :
    ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q), p₀ ≤ p →
      (z - δ (n - 1) n γ).v p q hpq = 0 := by
  have hf : z.v p₀ (p₀ + n) rfl ≫ D.d (p₀ + n) (p₀ + n + 1) = 0 := by
    have h0 := congrArg (fun c => Cochain.v c p₀ (p₀ + n + 1) (by omega)) hz
    simp only [Cochain.zero_v] at h0
    rw [δ_v n (n + 1) rfl z p₀ (p₀ + n + 1) (by omega) (p₀ + n) (p₀ + 1) (by omega) rfl,
      hv (p₀ + 1) (p₀ + n + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at h0
    exact h0
  obtain ⟨g, hg⟩ := H p₀ (p₀ + n) (z.v p₀ (p₀ + n) rfl) hf
  refine ⟨Cochain.single g (n - 1), ?_⟩
  intro p q hpq hp
  rw [Cochain.sub_v, δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
    Cochain.single_v_eq_zero g (n - 1) (p + 1) q (by omega) (by omega), comp_zero, smul_zero, add_zero]
  rcases hp.lt_or_eq with hlt | rfl
  · rw [hv p q hpq hlt, Cochain.single_v_eq_zero g (n - 1) p (q - 1) (by omega) (by omega), zero_comp,
      sub_zero]
  · subst hpq
    rw [Cochain.single_v, hg, sub_self]

end UpperTheory

theorem UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift :
    ∀ (K D : Cx ℤ) [K.IsStrictlyLE 0] (a : ℤ) [D.IsStrictlyGE a], (∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 → ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f) → ∀ n : ℤ, Subsingleton (CohomologyClass K D n) := by
  intro K D _ a _ H n
  have hz0 : ∀ (z : Cocycle K D n) (k : ℕ), ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q),
      -(k : ℤ) < p → ((z : Cochain K D n) - δ (n - 1) n γ).v p q hpq = 0 := by
    intro z k
    induction k with
    | zero =>
      refine ⟨0, fun p q hpq hp => ?_⟩
      exact (K.isZero_of_isStrictlyLE 0 p (by simpa using hp)).eq_of_src _ _
    | succ k ih =>
      obtain ⟨γ, hγ⟩ := ih
      obtain ⟨γ', hγ'⟩ := UpperTheory.hb_step K D H n (-(k : ℤ)) ((z : Cochain K D n) - δ (n - 1) n γ)
        (by rw [δ_sub, z.δ_eq_zero, δ_δ, sub_zero]) (fun p q hpq hp => hγ p q hpq hp)
      refine ⟨γ + γ', fun p q hpq hp => ?_⟩
      rw [δ_add, ← sub_sub]
      exact hγ' p q hpq (by push_cast at hp; omega)
  have all : ∀ z : Cocycle K D n, CohomologyClass.mk z = 0 := by
    intro z
    obtain ⟨γ, hγ⟩ := hz0 z (n - a + 1).toNat
    have hk := Int.self_le_toNat (n - a + 1)
    have hzero : (z : Cochain K D n) - δ (n - 1) n γ = 0 := by
      apply Cochain.ext
      intro p q hpq
      rw [Cochain.zero_v]
      by_cases hp : -((n - a + 1).toNat : ℤ) < p
      · exact hγ p q hpq hp
      · exact (D.isZero_of_isStrictlyGE a q (by omega)).eq_of_tgt _ _
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, γ, (sub_eq_zero.mp hzero).symm⟩
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  rw [all x, all y]
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_cohomologyClass_chains_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (E : Spc), (∀ s, Acy (fun U => Nonempty (Sx E 0 U)) (C.X s)) → (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ n : ℤ, Subsingleton (CohomologyClass ((chains ℤ).obj E) C n) := by
  intro C a _ E hAcy hLoc n
  haveI : IsStrictlyLE ((chains ℤ).obj E) 0 := (GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta ℤ).1 E
  refine UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift ((chains ℤ).obj E) C a ?_ n
  intro p j f hf
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hp
    have hmono : ∀ {V U : Scheme.{0}} (g : V ⟶ U), Nonempty (Sx E 0 U) → Nonempty (Sx E 0 V) := by
      intro V U g hx
      obtain ⟨x⟩ := hx
      exact ⟨((E.obj (op (SimplexCategory.mk 0))).map g.op) x⟩
    have hsupp : Supp (fun U => Nonempty (Sx E 0 U)) (E.obj (op (SimplexCategory.mk m))) := by
      intro U hx
      obtain ⟨x⟩ := hx
      exact ⟨((E.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m) 0).op).app (op U)) x⟩
    have hf' : ((chainsXIso ℤ E m).inv ≫ f) ≫ C.d j (j + 1) = 0 := by
      rw [Category.assoc, hf, comp_zero]
    obtain ⟨g, hg⟩ := UpperTheory.exists_primitive_free_of_acy_locally_exact C a (fun U => Nonempty (Sx E 0 U)) hmono hAcy hLoc
      (E.obj (op (SimplexCategory.mk m))) hsupp j _ hf'
    refine ⟨(chainsXIso ℤ E m).hom ≫ g, ?_⟩
    rw [Category.assoc, hg, Iso.hom_inv_id_assoc]
  · refine ⟨0, ?_⟩
    have hz : IsZero (((chains ℤ).obj E).X p) :=
      ((chains ℤ).obj E).isZero_of_isStrictlyLE 0 p hp
    rw [zero_comp]
    exact (hz.eq_of_src _ _).symm
