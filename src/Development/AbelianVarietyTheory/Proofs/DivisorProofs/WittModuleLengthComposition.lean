module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianSStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGenerat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColengthLemmas

variable {R : Type} [CommRing R]

theorem length_comp_range {A B C : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (u : B →ₗ[R] A) (v : C →ₗ[R] B) (hu : Function.Injective u) :
    Module.length R (A ⧸ LinearMap.range (u ∘ₗ v)) =
      Module.length R (A ⧸ LinearMap.range u) + Module.length R (B ⧸ LinearMap.range v) := by
  have hle : LinearMap.range v ≤ (LinearMap.range (u ∘ₗ v)).comap u := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hle2 : LinearMap.range (u ∘ₗ v) ≤ LinearMap.range u := LinearMap.range_comp_le_range v u
  let f := (LinearMap.range v).mapQ (LinearMap.range (u ∘ₗ v)) u hle
  let g := Submodule.factor hle2
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨c, hu hc⟩
  have hg : Function.Surjective g := Submodule.factor_surjective hle2
  have hex : Function.Exact f g := by
    intro x
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    constructor
    · intro h
      have h' : a ∈ LinearMap.range u := by
        simpa [g, Submodule.factor_mk, Submodule.Quotient.mk_eq_zero] using h
      obtain ⟨b, rfl⟩ := h'
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [← hy]
      show g (Submodule.Quotient.mk (u b)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem eq_of_le_of_length_eq {A : Type} [AddCommGroup A] [Module R A] (L L' : Submodule R A)
    (h : L ≤ L') (hl : Module.length R (A ⧸ L) = Module.length R (A ⧸ L'))
    (ht : Module.length R (A ⧸ L) ≠ ⊤) : L = L' := by
  let g := Submodule.factor h
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (LinearMap.ker g).injective_subtype (Submodule.factor_surjective h)
    (LinearMap.exact_subtype_ker_map g)
  have h0 : Module.length R (LinearMap.ker g) = 0 := by
    rw [← hl] at e
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 ht
    rw [← hn] at e
    generalize Module.length R (LinearMap.ker g) = b at e ⊢
    induction b using ENat.recTopCoe with
    | top => simp at e
    | coe b =>
      norm_cast at e ⊢
      omega
  rw [Module.length_eq_zero_iff] at h0
  refine le_antisymm h fun x hx => ?_
  have hmem : (Submodule.Quotient.mk x : A ⧸ L) ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have h1 : (⟨Submodule.Quotient.mk x, hmem⟩ : LinearMap.ker g) = 0 := Subsingleton.elim _ _
  have h2 : (Submodule.Quotient.mk x : A ⧸ L) = 0 := congrArg Subtype.val h1
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem length_quot_smul_range_free (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (a : O) :
    Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) =
      (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem length_quot_p_pow (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (n : ℕ) : Module.length (WittVector p k) (WittVector p k ⧸ Ideal.span {(p : WittVector p k) ^ n}) = n := by
  rw [← Ideal.span_singleton_pow, ← (WittVector.irreducible p).maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal _ n

end GlobalTheory.Dieu.ColengthLemmas

namespace GlobalTheory.Dieu

open GlobalTheory.Dieu.ColengthLemmas in
theorem colength_add_and_pow_and_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B C : Type) [AddCommGroup A] [Module (WittVector p k) A] [AddCommGroup B] [Module (WittVector p k) B] [AddCommGroup C] [Module (WittVector p k) C], (∀ (u : B →ₗ[(WittVector p k)] A) (v : C →ₗ[(WittVector p k)] B), Function.Injective u → Module.length (WittVector p k) (A ⧸ LinearMap.range (u ∘ₗ v)) = Module.length (WittVector p k) (A ⧸ LinearMap.range u) + Module.length (WittVector p k) (B ⧸ LinearMap.range v)) ∧ (Module.Free (WittVector p k) A → Module.Finite (WittVector p k) A → ∀ (n : ℕ) (u : A →ₗ[(WittVector p k)] A), (∀ a, u a = p ^ n • a) → Module.length (WittVector p k) (A ⧸ LinearMap.range u) = (n * Module.finrank (WittVector p k) A : ℕ)) ∧ ∀ L L' : Submodule (WittVector p k) A, L ≤ L' → Module.length (WittVector p k) (A ⧸ L) = Module.length (WittVector p k) (A ⧸ L') → Module.length (WittVector p k) (A ⧸ L) ≠ ⊤ → L = L' := by
  intro p _ k _ _ _ A B C _ _ _ _ _ _
  refine ⟨fun u v hu => length_comp_range u v hu, fun _ _ n u hu => ?_,
    fun L L' h hl ht => eq_of_le_of_length_eq L L' h hl ht⟩
  have hu' : u = ((p : WittVector p k) ^ n) • (LinearMap.id : A →ₗ[WittVector p k] A) := by
    ext a
    rw [hu a, LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [hu', length_quot_smul_range_free, length_quot_p_pow]
  push_cast
  ring

end GlobalTheory.Dieu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthCompositionStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_module_length_composition : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B C : Type) [AddCommGroup A] [Module (WittVector p k) A] [AddCommGroup B] [Module (WittVector p k) B] [AddCommGroup C] [Module (WittVector p k) C], (∀ (u : B →ₗ[(WittVector p k)] A) (v : C →ₗ[(WittVector p k)] B), Function.Injective u → Module.length (WittVector p k) (A ⧸ LinearMap.range (u ∘ₗ v)) = Module.length (WittVector p k) (A ⧸ LinearMap.range u) + Module.length (WittVector p k) (B ⧸ LinearMap.range v)) ∧ (Module.Free (WittVector p k) A → Module.Finite (WittVector p k) A → ∀ (n : ℕ) (u : A →ₗ[(WittVector p k)] A), (∀ a, u a = p ^ n • a) → Module.length (WittVector p k) (A ⧸ LinearMap.range u) = (n * Module.finrank (WittVector p k) A : ℕ)) ∧ ∀ L L' : Submodule (WittVector p k) A, L ≤ L' → Module.length (WittVector p k) (A ⧸ L) = Module.length (WittVector p k) (A ⧸ L') → Module.length (WittVector p k) (A ⧸ L) ≠ ⊤ → L = L' := by
  first | exact @GlobalTheory.Dieu.colength_add_and_pow_and_eq | exact GlobalTheory.Dieu.colength_add_and_pow_and_eq | (intros; apply GlobalTheory.Dieu.colength_add_and_pow_and_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHodgeFiltrationFunctionalExtends
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHodgeFiltrationFunctionalExtends
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem exists_extend_hodgeFiltration_functional_split {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hO : Function.Injective (cmpO s)) (h1 : Function.Surjective (cmp1 s))
    (hsurj : Function.Surjective (toHO1 s)) [Module.Projective R (HO1 s)]
    (ψ : F1 s →ₗ[R] R) : ∃ H : FirstDeRham s →ₗ[R] R, ∀ c : F1 s, H c = ψ c := by
  let f : FirstDeRham s →ₗ[R] HO1 s := (toHO1 s).comp (cmp1 s)
  have hf : Function.Surjective f := hsurj.comp h1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hker : ∀ c : FirstDeRham s, f c = 0 ↔ c ∈ F1 s := fun c ↦ by
    change toHO1 s (cmp1 s c) = 0 ↔ toH1O s c = 0
    rw [structureSheaf_comparison_comm]
    exact ⟨fun h ↦ hO (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  let p : FirstDeRham s →ₗ[R] F1 s := LinearMap.codRestrict (F1 s) (LinearMap.id - σ.comp f) fun c ↦ by
    rw [← hker]
    have : f (σ (f c)) = f c := LinearMap.congr_fun hσ (f c)
    simp [this]
  refine ⟨ψ.comp p, fun c ↦ ?_⟩
  have hc : f c = 0 := (hker c).2 c.2
  have : p c = c := Subtype.ext (by simp [p, hc])
  simp [this]

end GlobalTheory.CechDR

namespace GlobalTheory.AbelianExtend

open GlobalTheory.CechDR

theorem abelianScheme_hodgeFiltration_functional_extends' : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R,
      ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  intro hC hH R _ A _ g hab hdim ψ
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hsurj⟩, -⟩ := hH R A g hab hdim
  haveI := hab.smooth
  haveI := hab.proper
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have h1 := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left (A.hom ≫ 𝟙 (Sp R)) hsm hsep hqc).1.2
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 (Sp R))
  have hs' : Function.Surjective (toHO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hsurj
  haveI : Module.Projective R (HO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hproj
  exact GlobalTheory.CechDR.exists_extend_hodgeFiltration_functional_split _ hO h1 hs' ψ

end GlobalTheory.AbelianExtend
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHodgeFiltrationFunctionalExtendsStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hodgeFiltration_functional_extends : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  first | exact @GlobalTheory.AbelianExtend.abelianScheme_hodgeFiltration_functional_extends' | exact GlobalTheory.AbelianExtend.abelianScheme_hodgeFiltration_functional_extends' | (intros; apply GlobalTheory.AbelianExtend.abelianScheme_hodgeFiltration_functional_extends' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianScheme
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieHodge

theorem lieExact_of_crystallineLift_hodgeDeRham : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LieExact A := by
  intro hC hH R _ A _ g hab hdim
  have hP : AllPrim (dp0 R) (𝟙 _) A :=
    (GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison hC hH) R A g hab hdim).1
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.smooth; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by haveI := hab.proper; infer_instance
  have hcmp : Function.Injective (GlobalTheory.CechDR.cmp1 (A.hom ≫ 𝟙 (Sp R))) :=
    (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left _ hsm hsep hqc).1.1
  have hcl : Function.Injective (GlobalTheory.CechDR.clForm (A.hom ≫ 𝟙 (Sp R))) :=
    (hH R A g hab hdim).2.2.2.2.1.2.1
  have hcf : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)),
      Form.cl _ f = 0 ↔ GlobalTheory.CechDR.cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 := fun f ↦
    ⟨fun h ↦ hcl (by rw [← GlobalTheory.CechDR.comparison_formClass, h, map_zero, map_zero]),
      fun h ↦ hcmp (by rw [GlobalTheory.CechDR.comparison_formClass, h, map_zero, map_zero])⟩
  have hmem : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f ∈ primDR A := fun f ↦ by
    have : primDR A = ⊤ := hP
    rw [this]; exact Submodule.mem_top
  let F : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] primDR A := (Form.cl _).codRestrict _ hmem
  refine ⟨fun h ↦ ?_, fun v hv ↦ ?_⟩
  · obtain ⟨v, hv, hvf⟩ := GlobalTheory.T.exists_tangentVector_functional_globalForms_abelianScheme hC hH R A g hab hdim (h ∘ₗ F) (fun f hf ↦ by
      have e : F f = 0 := Subtype.ext ((hcf f).2 hf)
      rw [LinearMap.comp_apply, e, map_zero])
    refine ⟨v, ⟨hv, fun f hf ↦ (hvf f).symm⟩, fun w hw ↦ GlobalTheory.T.abelianScheme_tangent_eq_of_crystallineValues_eq hC hH R A g hab hdim w v hw.1 hv
      fun f ↦ ((hw.2 f (hmem f)).symm.trans (hvf f).symm)⟩
  · have hfac : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f = 0 → tanVal v f = 0 :=
      fun f h0 ↦ GlobalTheory.T.formValueOnTangentVector_eq_zero_of_globalForm_zero R A v f ((hcf f).1 h0)
    have hF1 : ∀ f : Form (A.hom ≫ 𝟙 (Sp R)), Form.cl _ f ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := fun f ↦ by
      rw [hodgeFiltration_eq_range]; exact ⟨f, rfl⟩
    let c1 : Form (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] F1 (A.hom ≫ 𝟙 (Sp R)) := (Form.cl _).codRestrict _ hF1
    have hc1 : Function.Surjective c1 := by
      rintro ⟨c, hc⟩
      rw [hodgeFiltration_eq_range] at hc
      obtain ⟨f, rfl⟩ := hc
      exact ⟨f, rfl⟩
    let e := c1.quotKerEquivOfSurjective hc1
    have hker : LinearMap.ker c1 ≤ LinearMap.ker (tanVal v) :=
      fun f hf ↦ hfac f (congrArg Subtype.val hf)
    let ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R :=
      (LinearMap.ker c1).liftQ (tanVal v) hker ∘ₗ e.symm.toLinearMap
    have hψ : ∀ f, ψ (c1 f) = tanVal v f := fun f ↦ by
      have : e.symm (c1 f) = Submodule.Quotient.mk f := e.symm_apply_eq.2 rfl
      change (LinearMap.ker c1).liftQ (tanVal v) hker (e.symm (c1 f)) = _
      rw [this]; rfl
    obtain ⟨H, hH'⟩ := GlobalTheory.T.abelianScheme_hodgeFiltration_functional_extends hC hH R A g hab hdim ψ
    exact ⟨H ∘ₗ (primDR A).subtype, hv, fun f hf ↦ (hH' (c1 f)).trans (hψ f)⟩

end GlobalTheory.LieHodge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieSequenceExactAbelianSchemeStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLieSequence_exact_abelianScheme : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LieExact A := by
  first | exact @GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham | exact GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham | (intros; apply GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompact
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.FinChart

namespace GlobalTheory.Mix

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem maDens_locPot_eq_dens (L : Fin D → MLine p σ) (c : AlgChart p σ D) {z : Fin D → ℂ}
    (hz : z ∈ c.finChart.target) :
    maDens (fun i y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      dens L c (c.finChart.symm z) := by
  have hr : c.e (c.finChart.symm z) = toV D z := c.e.right_inv hz
  have hH (i) : hessC (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) z =
      ((2⁻¹ : ℝ) : ℂ) • c.hess (L i).φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) := by
    have hd := (L i).cInf.contDiffAt c (c.finChart.map_target hz)
      (mem_pick (L i).φ.isLB (c.finChart.symm z))
    rw [hr] at hd
    have e : (fun y => (L i).φ.locPot.φ (c.finChart.symm z) (c.finChart.symm y)) = fun y => 2⁻¹ *
        ((fun v => (L i).φ.φ (pick (L i).φ.isLB (c.finChart.symm z)) (c.e.symm v)) ∘ toV D) y :=
      funext fun _ => div_eq_inv_mul _ _
    rw [e, hessC_const_mul', AlgChart.hess, hr, cHess_eq_hessC hd]
  have hτ (τ : Equiv.Perm (Fin D)) : (Matrix.of fun j l => (((2⁻¹ : ℝ) : ℂ) •
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z)) j l).det =
      (((2⁻¹ : ℝ) ^ D : ℝ) : ℂ) * (Matrix.of fun j l =>
      c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l).det := by
    refine (Matrix.det_smul (Matrix.of fun j l => c.hess (L (τ l)).φ
      (pick (L (τ l)).φ.isLB (c.finChart.symm z)) (c.finChart.symm z) j l) ((2⁻¹ : ℝ) : ℂ)).trans ?_
    rw [Fintype.card_fin, Complex.ofReal_pow]
  have hf : (1 / (D.factorial : ℂ)) = ((1 / (D.factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  have h0 : (D.factorial : ℝ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have h2 : (2 / Real.pi) ^ D * (2⁻¹ : ℝ) ^ D = (Real.pi ^ D)⁻¹ := by
    rw [← mul_pow, ← inv_pow]
    congr 1
    ring
  simp only [maDens, hH, ReciprocityTheory.AnForm.A.mdisc_eq_sum_perm, hτ, dens]
  rw [← Finset.mul_sum, hf, Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← h2]
  field_simp

variable {A : FinHolAtlas D (CxPts p σ)}

theorem locDens_locPot_eq_dens (L : Fin D → MLine p σ) (hA : IsAlgAtlas A) (j : Fin A.n)
    {z : Fin D → ℂ} (hz : z ∈ (A.chart j).target) : locDens A (fun i => (L i).φ.locPot) j z =
      dens L (hA.anRead.chart j) ((A.chart j).symm z) := by
  unfold locDens
  rw [hA.chart_eq j] at hz ⊢
  exact maDens_locPot_eq_dens L _ hz

theorem part_eq_lintegral_locDens [SecondCountableTopology (CxPts p σ)] (L : Fin D → MLine p σ)
    (hA : IsAlgAtlas A) (ε : ℤˣ) (j : Fin A.n) (S : Set (CxPts p σ)) (hS : MeasurableSet S)
    (hs : S ⊆ (A.chart j).source) : part L ε S =
      ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' S,
        ENNReal.ofReal (max ((ε : ℤ) * locDens A (fun i => (L i).φ.locPot) j y) 0) := by
  have hl (y) := locDens_locPot_eq_dens L hA j (z := y)
  generalize locDens A (fun i => (L i).φ.locPot) j = d at hl ⊢
  rw [hA.chart_eq j] at hs hl ⊢
  set c := hA.anRead.chart j
  have hm := measurableSet_image c.e hS hs
  rw [GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D L ε c S hS hs,
    ← measurePreserving_toV.setLIntegral_comp_preimage_emb (toV D).toHomeomorph.measurableEmbedding]
  have e : c.e '' S = c.e.target ∩ c.e.symm ⁻¹' S := by
    rw [← c.e.image_source_inter_eq', inter_eq_right.2 (show S ⊆ c.e.source from hs)]
  rw [e] at hm ⊢
  refine setLIntegral_congr_fun (hm.preimage (toV D).continuous.measurable) fun y hy => ?_
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_le, max_eq_left, hl y hy.1]
  rfl

theorem int_eq_mInt (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (D : ℕ)
    (A : FinHolAtlas D (CxPts p σ)) (hA : IsAlgAtlas A) (L : Fin D → MLine p σ)
    (g : CxPts p σ → ℝ) (hg : Measurable g) :
    (Intg L g ↔ MIntegrable A (fun i => (L i).φ.locPot) g) ∧
      (Intg L g → Mix.int L g = mInt A (fun i => (L i).φ.locPot) g) := by
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set P := hne.some
  set d := locDens A fun i => (L i).φ.locPot with hd
  have hdc (j) : ContinuousOn (d j) (A.chart j).target := locDensCont A _
    (fun i => ((Weight.isCInf_iff_isSmooth hA.anRead).1 (L i).cInf).isPotential hA) j
  let w (ε : ℤˣ) (j) (y) : ℝ := max ((ε : ℤ) * d j y) 0
  have hw (ε j) : ContinuousOn (w ε j) (A.chart j).target :=
    (continuous_id.max continuous_const).comp_continuousOn (continuousOn_const.mul (hdc j))
  have hw0 (ε j) : ∀ y ∈ (A.chart j).target, 0 ≤ w ε j y := fun _ _ => le_max_right _ _
  have hsub (j y) : w 1 j y - w (-1) j y = d j y := by
    simpa [w] using max_zero_sub_max_neg_zero_eq_self (d j y)
  have habs (ε j y) : |w ε j y| ≤ |d j y| := by
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ((le_abs_self _).trans_eq ?_) (abs_nonneg _)
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have back (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε j) : IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * w ε j y)
      (A.chart j).target := by
    obtain ⟨hKc, hKs⟩ := image_closed_compact (A.chart j) (isClosed_tsupport (P.χ j))
      (P.tsupport_subset j)
    refine integrableOn_target_of_closed (A.chart j) (Z := tsupport (P.χ j))
      (fun y _ hy => by simp [image_eq_zero_of_notMem_tsupport hy]) ?_
    have hcc := (chi_comp_continuousOn P j).mono hKs
    refine Integrable.mono ((hm j _ hKs hKc).continuousOn_mul hcc hKc) ?_ (.of_forall fun y => ?_)
    · exact (((hcc.aemeasurable hKc.measurableSet).mul (hg.comp_aemeasurable
        (((A.chart j).continuousOn_symm.mono hKs).aemeasurable hKc.measurableSet))).mul
        (((hw ε j).mono hKs).aemeasurable hKc.measurableSet)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (habs ε j y) (by positivity)
  have pieces (hm : MIntegrable A (fun i => (L i).φ.locPot) g) (ε) :=
    integrable_of_pieces A P (hw ε) (hw0 ε) (part_eq_lintegral_locDens L hA ε) hg (back hm ε)
  have fwd (hi : Intg L g) : MIntegrable A (fun i => (L i).φ.locPot) g :=
    fun j K hK _ => by
    have key (ε) := (integrableOn_source_iff_of_density (A.chart j) (hw ε j) (hw0 ε j)
      (part_eq_lintegral_locDens L hA ε j) hg).1.1
    refine IntegrableOn.mono_set ?_ hK
    refine (Integrable.sub (key 1 hi.1.integrableOn) (key (-1) hi.2.integrableOn)).congr
      (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, ← mul_sub, hsub, hd]
  refine ⟨⟨fwd, fun hm => ⟨(pieces hm 1).1, (pieces hm (-1)).1⟩⟩, fun hi => ?_⟩
  have hm := fwd hi
  have hmi : mInt A (fun i => (L i).φ.locPot) g = integralWith A hne.some (fun i => (L i).φ.locPot) g := by
    unfold mInt
    rw [dite_eq_left hne]
  rw [Mix.int, (pieces hm 1).2, (pieces hm (-1)).2,
    hmi, integralWith, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_sub (back hm 1 j) (back hm (-1) j)]
  simp only [← mul_sub, hsub, hd, P]

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)] (D : ℕ) (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (L : Fin D → MLine p σ) (g : CxPts p σ → ℝ), Measurable g → (Intg L g ↔ MIntegrable A (fun i => (L i).φ.locPot) g) ∧ (Intg L g → Mix.int L g = mInt A (fun i => (L i).φ.locPot) g) := by
  first | exact @GlobalTheory.Mix.int_eq_mInt | exact GlobalTheory.Mix.int_eq_mInt | (intros; apply GlobalTheory.Mix.int_eq_mInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwise
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.SumFE

open GlobalTheory.IndivisibleSection (smulSec)

theorem sval_smulSec {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (smulSec a s) r z J = gs r z ⊤ a * sval s r z J := by
  have hm := hJ.mem φ r
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem app_eq_of_sval {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) (j) :
    (h.app _).hom (s.f j) = (h.app _).hom (s'.f j) := by
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ (𝟙 Y' ≫ h)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)

theorem sec_eq_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval s (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J = sval s' (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) z J) → s = s' := by
  intro R _ _ _ hB D K _ φ ε s s' H
  have := hB.1
  have := hB.2.2.2
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine DVR.SecOps.sec_ext fun j => sub_eq_zero.1 ?_
  refine (GlobalTheory.sec_eq_zero_and_hom_eq_of_thickenings R _ (IsAdicComplete.le_jacobson_bot (maximalIdeal R)) D.toPre.P.A).1 _
    (DVR.linComb_isLB _ D.toPre.P.isLB φ ε) ⟨fun i => s.f i - s'.f i, fun i j => by
      simp only [map_sub, s.compat, s'.compat, mul_sub]⟩ (fun e i => ?_) j
  exact (map_sub _ _ _).trans (sub_eq_zero.2 (app_eq_of_sval D.toPre.P.isLB (fun y J hJ => H e _ (𝟙 _) y J hJ) i))

theorem sec_eq_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (K : Type) [Fintype K] (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (s s' : LB.Sec (LB.LinComb D.P.L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J → sval s (x ≫ (DegPre.prB D (FractionRing R)).left) z J = sval s' (x ≫ (DegPre.prB D (FractionRing R)).left) z J) → s = s' := by
  intro R _ _ D K _ φ ε s s' H
  have := D.P.isAb.smooth
  have : IsDominant (TF (R := R) (FractionRing R)).hom := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)) ∘
      PrimeSpectrum.comap (algebraMap (FractionRing R) (FractionRing R)))
    rw [Algebra.algebraMap_self, PrimeSpectrum.comap_id]
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have : QuasiCompact (TF (R := R) (FractionRing R)).hom :=
    have : IsAffine (TF (R := R) (FractionRing R)).left := inferInstanceAs (IsAffine (Spec _))
    quasiCompact_of_compactSpace _
  have := IsSchemeTheoreticallyDominant.of_isDominant (X := Spec (CommRingCat.of (FractionRing R)))
    (TF (R := R) (FractionRing R)).hom
  have : IsSchemeTheoreticallyDominant (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback _ D.P.A.hom)
  have : QuasiCompact (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom) := inferInstance
  exact DVR.SecOps.sec_ext fun j => (pullback.snd (TF (R := R) (FractionRing R)).hom D.P.A.hom).app_injective _
    (app_eq_of_sval D.P.isLB (fun y J hJ => H _ (𝟙 _) y J hJ) j)

theorem trF_prB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (mu : D.X), (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left = (DegPre.prB D (FractionRing R)).left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c mu)).left := by
  intro R _ _ D mu
  rw [← Over.comp_left, ← Over.comp_left, DegPre.trF, lift_snd, padd, padd, comp_lift_assoc, Category.comp_id,
    comp_toUnit_assoc]

theorem gs_scal_generic {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Z : Scheme.{0}}
    (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R) :
    gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) =
      gs x z ⊤ (scal ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) r)) := by
  have e := congrArg (fun h => h.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have w : (DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom =
      ((fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
        (DegPre.BF D (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
    refine (Over.w _).trans ((Over.w (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_)
    congr 1
    change Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) ≫ jK R = jK R
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  refine (gs_pull x _ z ⊤ trivial _).symm.trans (congrArg (gs x z ⊤) ?_)
  change scal ((DegPre.prB D (FractionRing R)).left ≫ D.P.A.hom) r = _
  rw [w, scal, scal, e]
  rfl

theorem scal_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (r : R), (r ≠ 0 → IsUnit (gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r))) ∧ ∀ (c : FractionRing R) (r' : R), c * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) r' → gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r) * gs x z ⊤ (scal (fst _ _ : DegPre.BF D (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left c) = gs (x ≫ (DegPre.prB D (FractionRing R)).left) z ⊤ (scal D.P.A.hom r') := by
  intro R _ _ D Z x z r
  refine ⟨fun hr => ?_, fun c r' hc => ?_⟩
  · have hu : IsUnit (algebraMap R (FractionRing R) r) :=
      IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    rw [gs_scal_generic, gs_eq _ z ⊤ trivial]
    exact ((((hu.map _).map _).map _).map _)
  · rw [gs_scal_generic, gs_scal_generic, ← hc, ← gs_mul x z ⊤ trivial, mul_comm c]
    simp only [scal, map_mul]

theorem tfe_of_isSum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β) (σ : D.toPre.X → Ix ≃ Ix), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → (∀ mu i, w (σ mu i) = w i + shift h h' n j mu) → (∀ mu i, TRel h mu (s i) (s (σ mu i))) → TFE h h' F := by
  intro R _ _ _ hB D a a' h h' hE n j Ix w s F σ hs hF hw hrel mu β
  generalize hβ' : β + shift h h' n j mu = β'
  intro u hu
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hB D a a' h h' hE n j mu β β' hβ'.symm
  obtain ⟨c, hc⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hB D a h hE.1 hE.2.2.2.1 n j mu β β' u₀ hu₀).2.2 u hu.1
  obtain ⟨⟨r', r⟩, hrc⟩ := IsLocalization.surj (nonZeroDivisors R) c
  have hTw : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ D.toPre.P.A.hom = D.toPre.P.A.hom := Over.w _
  have hT := trF_prB R D.toPre mu
  generalize hTe : (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left = T at hTw hT
  have mkG : ∀ t : SecT D.toPre a n j β, ∃ G : SecT D.toPre a n j β', ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left)
      (z : Z) (J), Good D.toPre.P.L z J → sval G y z J = sval t (y ≫ T) z J * (val u₀ y z J).val := by
    intro t
    obtain ⟨G, hG⟩ := exists_sec hL (φ' := tφ D.toPre a β') (ε' := tε n j) (fun U _ g => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, dε, zpow_neg, Finset.prod_inv_distrib, hTe]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]) (pullMulSec t T u₀ hu₀)
    exact ⟨G, fun Z y z J hJ => (hG Z y z J hJ).trans (sval_pullMulSec t T u₀ hu₀ y z hJ)⟩
  have key : ∀ (b b' : D.toPre.X) (t : SecT D.toPre a n j b) (t' : SecT D.toPre a n j b'), b = β → b' = β' →
      TRel h mu t t' → ∀ (Z : Scheme.{0}) (y : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J →
      gs y z ⊤ (scal D.toPre.P.A.hom r.1) * sval t' y z J =
        gs y z ⊤ (scal D.toPre.P.A.hom r') * (sval t (y ≫ T) z J * (val u₀ y z J).val) := by
    intro b b' t t' h1 h2 hR Z y z J hJ
    subst h1 h2
    obtain ⟨G, hG⟩ := mkG t
    have e : smulSec (scal D.toPre.P.A.hom r.1) t' = smulSec (scal D.toPre.P.A.hom r') G :=
      sec_eq_of_generic R D.toPre (Fin 5) _ _ _ _ fun Z x z J hJ => by
        rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hR u hu Z x z J hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT,
          ← (scal_generic R D.toPre Z x z r.1).2 c r' hrc, Category.assoc]
        ring
    rw [← hG _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, ← sval_smulSec _ _ _ _ hJ, e]
  obtain ⟨G, hG⟩ := mkG (F β)
  have eB : smulSec (scal D.toPre.P.A.hom r.1) (F β') = smulSec (scal D.toPre.P.A.hom r') G := by
    refine sec_eq_of_thick R hB D (Fin 5) _ _ _ _ fun e Z x z J hJ => ?_
    rw [sval_smulSec _ _ _ _ hJ, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ]
    obtain ⟨x', hx'⟩ : ∃ x' : Z ⟶ (thickObj R (maximalIdeal R) e D.toPre.P.A).left,
        x' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
          (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ T :=
      ⟨pullback.lift _ (x ≫ pullback.snd _ _) (by
        rw [Category.assoc, hTw]
        exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)),
        pullback.lift_fst _ _ _⟩
    classical
    have hS : ∀ i ∉ (hs e).toFinset, Van (maximalIdeal R) (s i) e := fun i hi =>
      by_contra fun hc => hi ((hs e).mem_toFinset.2 hc)
    generalize (hs e).toFinset = S at hS
    have e₁ := hF e ((S ∪ S.image (σ mu).symm).image (σ mu)) (fun i hi => hS i fun m => hi (Finset.mem_image.2
      ⟨(σ mu).symm i, Finset.mem_union_right _ (Finset.mem_image_of_mem _ m), (σ mu).apply_symm_apply i⟩)) β' Z x z J hJ
    have e₂ := hF e (S ∪ S.image (σ mu).symm) (fun i hi => hS i fun m => hi (Finset.mem_union_left _ m)) β Z x' z J hJ
    rw [hx'] at e₂
    rw [e₁, e₂, Finset.sum_filter, Finset.sum_filter, Finset.sum_image (σ mu).injective.injOn, Finset.sum_mul,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : w i = β
    · have hi' : w (σ mu i) = β' := by rw [hw, hi, hβ']
      rw [if_pos hi, if_pos hi']
      exact key _ _ _ _ hi hi' (hrel mu i) _ _ z J hJ
    · have hi' : ¬ w (σ mu i) = β' := fun h2 => hi (add_right_cancel ((hw mu i).symm.trans (h2.trans hβ'.symm)))
      rw [if_neg hi, if_neg hi', zero_mul, mul_zero, mul_zero]
  intro Z x z J hJ
  obtain ⟨hunit, hmul⟩ := scal_generic R D.toPre Z x z r.1
  refine (hunit (nonZeroDivisors.ne_zero r.2)).mul_left_cancel ?_
  rw [← sval_smulSec _ _ _ _ hJ, eB, sval_smulSec _ _ _ _ hJ, hG _ _ _ _ hJ, hc Z x z J hJ, hT, ← hmul c r' hrc,
    Category.assoc]
  ring

end GlobalTheory.TwFam.SumFE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwiseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β) (σ : D.toPre.X → Ix ≃ Ix), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → (∀ mu i, w (σ mu i) = w i + shift h h' n j mu) → (∀ mu i, TRel h mu (s i) (s (σ mu i))) → TFE h h' F := by
  first | exact @GlobalTheory.TwFam.SumFE.tfe_of_isSum | exact GlobalTheory.TwFam.SumFE.tfe_of_isSum | (intros; apply GlobalTheory.TwFam.SumFE.tfe_of_isSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.TorPt


open GlobalTheory.ZH.TorusPerp in
theorem torus_label_over : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ b mu, 𝔪.YY b mu → (χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val))))) → ∀ (q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N)) (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), q.y = 0 → IsTor χ q.g → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q y → y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ χ hχ1 hlab q y hqy hqτ hq
  haveI : CharZero V := 𝔪.cn.2.2.2
  have : IsDomain X₁.o₁ := X₁.ar.inj.isDomain _
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos

  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let yb : X₁.S.R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit hkpos.ne').unit
  let ω : (AlgebraicClosure (FractionRing V))ˣ := Units.map yb.toMonoidHom c₀
  have hωv : (ω : AlgebraicClosure (FractionRing V)) = yb (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω : IsPrimitiveRoot ω (X₁.S.r * X₁.S.N) := by
    have : NeZero ((X₁.S.r * X₁.S.N : ℕ) : AlgebraicClosure (FractionRing V)) := ⟨Nat.cast_ne_zero.2 hkpos.ne'⟩
    apply (IsPrimitiveRoot.coe_units_iff).1
    rw [hωv, ← (Polynomial.isRoot_cyclotomic_iff (R := AlgebraicClosure (FractionRing V))),
      ← Polynomial.map_cyclotomic _ (yb.comp (algebraMap X₁.o₁ X₁.S.R))]
    exact (hζ.isRoot_cyclotomic hkpos).map (yb.comp (algebraMap X₁.o₁ X₁.S.R))

  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK = spMap yb := (Spec.map_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap yb := hy
  let Φ := ptHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
  have hΦ : ∀ b, Φ (x b) = h ≫ X₁.ρ.pt b := fun b => Over.OverMorphism.ext ((hx b).trans (by rw [← hh]; rfl))
  have weil : ∀ b b', WeilIs 𝔪.A.A 𝔪.A.L (X₁.S.r * X₁.S.N : ℕ) (x b) (x b') (unitOn (ω ^ (eStd X₁.S.g _ b b').val)) :=
    fun b b' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h (X₁.ρ.weil b b' (c₀ ^ (eStd X₁.S.g _ b b').val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← hΦ, ← hΦ] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ _ _ _ _
      (Φ (x b)) (Φ (x b')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  have pt_nsmul : ∀ (n : ℕ) b, x (n • b) = x b ^ n := fun n b =>
    map_pow (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _) (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q', f q' = x b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (X₁.S.r * X₁.S.N)), ZMod.natCast_self, zero_smul]
    exact (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _).map_one)
  have hyf : y = f q := (f₁ q y).1 hq
  have hq1 : y ^ (X₁.S.r * X₁.S.N) = 1 := by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (hq w hw).1
  obtain ⟨a', rfl⟩ := xonto y hq1
  have haa : a' = τ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hqy hqτ)
    rw [← hyf, hq'] at w₁
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB (weil a' b) w₁)
    have hYY : 𝔪.YY b (𝔪.e₈.symm q'.y) := ⟨q', x b, by simp, (f₁ _ _).2 hq'.symm, hx b⟩
    have e₂ := hlab b _ hYY
    rw [AddEquiv.apply_symm_apply] at e₂
    have e₃ : ω ^ (eStd X₁.S.g _ a' b).val = ω ^ (eStd X₁.S.g _ τ b).val := by
      rw [e₁]
      ext1
      rw [e₂, Units.val_pow_eq_pow_val, hωv, pow_mul, map_pow, map_pow, map_pow]
      rfl
    have e₄ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₃)
    have e₅ := eStd_add_left X₁.S.g _ (a' - τ) τ b
    rw [sub_add_cancel, e₄] at e₅
    exact left_eq_add.1 (e₅.trans (add_comm _ _))
  subst haa
  exact hx a'

theorem labels_hom : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range, Function.Surjective yy ∧ ∀ a mu, 𝔪.YY a mu ↔ yy a = QuotientAddGroup.mk (𝔪.e₈ mu) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  choose mu hmu using h1
  have key : ∀ a nu, 𝔪.YY a nu ↔
      (QuotientAddGroup.mk (𝔪.e₈ (mu a)) : 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range) =
        QuotientAddGroup.mk (𝔪.e₈ nu) := by
    intro a nu
    rw [h3 a (mu a) nu (hmu a), QuotientAddGroup.eq]
    constructor
    · intro hc
      choose w hw using hc
      refine ⟨𝔪.e₈ w, ?_⟩
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • w := funext fun v => by simpa using hw v
      rw [nsmulAddMonoidHom_apply, e, map_add (f := _), map_nsmul]
      abel
    · rintro ⟨z, hz⟩
      rw [nsmulAddMonoidHom_apply] at hz
      intro v
      refine ⟨𝔪.e₈.symm z v, ?_⟩
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, hz]
        abel)
      rw [e]
      rfl
  let yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range :=
    AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (𝔪.e₈ (mu a))) fun a b => by
      have h := (key (a + b) (mu a + mu b)).1 (h4 a b (mu a) (mu b) (hmu a) (hmu b))
      refine h.trans ?_
      rw [map_add (f := _), QuotientAddGroup.mk_add]
  refine ⟨yy, fun c => ?_, fun a nu => (key a nu)⟩
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    obtain ⟨a, ha⟩ := h2 (𝔪.e₈.symm α)
    refine ⟨a, ?_⟩
    have := (key a _).1 ha
    rw [AddEquiv.apply_symm_apply] at this
    exact this


open GlobalTheory.ZH.TorusPerp GlobalTheory.ZH.PerpTorus GlobalTheory.TorusExt GlobalTheory.TorsionExt in
attribute [local instance] gtGroup in
theorem exists_torus_char : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ hτ
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hB := 𝔪.D.tau_bimult
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨yy, yyonto, hyy⟩ := labels_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have hker : τ ∈ X₁.S.perp yy.ker := fun h hh => by
    have h0 : 𝔪.YY h 0 := (hyy h 0).2 (by rw [(AddMonoidHom.mem_ker).1 hh, map_zero]; rfl)
    exact hτ h ((GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V ev X m t δ 𝔪 h).2 h0)
  obtain ⟨mf, hmf⟩ := exists_form X₁.S yy yyonto τ hker
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) := X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let ω : (FractionRing V)ˣ := Units.map (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R)).toMonoidHom (hζ.isUnit hkpos.ne').unit
  have hωv : (ω : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω1 : ω ^ (X₁.S.r * X₁.S.N) = 1 := by
    ext1
    rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, hζ.pow_eq_one, map_one, map_one, Units.val_one]
  let χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ :=
    (AddChar.zmodChar (X₁.S.r * X₁.S.N) hω1).toMonoidHom.comp mf.toMultiplicative
  have hχ : ∀ α, χ (Multiplicative.ofAdd α) = ω ^ (mf α).val := fun _ => rfl
  have hχ1 : χ ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (mf α.toAdd).val) ^ (X₁.S.r * X₁.S.N) = 1
    rw [pow_right_comm, hω1, one_pow]
  refine ⟨χ, hχ1, fun g₀ hg₀ => ?_⟩

  obtain ⟨q, hqy, hqg⟩ := GlobalTheory.ZH.ClassWeight.exists_qkPt_tor hg₀ hχ1
  have hsq : (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) ≫ X₁.ρ.P.A.hom = 𝟙 _ ≫ spMap 𝔪.yK := by
    rw [Category.assoc, Over.w]; simp
  let ℓ := 𝔪.cart.1.lift (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) (𝟙 _) hsq
  have hℓ : ℓ ≫ 𝔪.A.A.hom = (TFK (R := V) (FractionRing V)).hom := by
    rw [𝔪.cart.1.lift_snd]
    show _ = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V)))
    rw [Algebra.algebraMap_self]
    exact (Spec.map_id _).symm
  let xF : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A := Over.homMk ℓ hℓ
  have hxF : xF.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left := 𝔪.cart.1.lift_fst _ _ _
  refine ⟨q, xF, hqy, hqg, ?_, hxF⟩
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    ext; simp
  obtain ⟨qb, hqb, -⟩ := existsUnique_qkExt (F' := AlgebraicClosure (FractionRing V)) hB
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf q
  rw [qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow 𝔪.U hkpos hqb xF]
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  obtain ⟨f, f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos
  have hqbf := (f₁ qb (f qb)).2 rfl
  let χb : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ
  have hχb1 : χb ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show Units.map _ (χ α) ^ _ = 1
    rw [← map_pow, ← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply, map_one]
  have hqbt : IsTor χb qb.g := by
    have e1 : q.g = torusPt _ _ (Additive.ofMul χ) := (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 (hqg ▸ hg₀))
    have hg : qb.g = gtExt _ _ hf q.g := (eq_gtExt_iff _ hf _ _).2 hqb.2
    rw [hg]
    rw [e1, GlobalTheory.QkNumberField.gtExt_torusPt, isTor_iff]
    exact isTorusPtF_torusPt _
  have hlab : ∀ b mu, 𝔪.YY b mu → (χb (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))
        (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val)))) := by
    intro b mu h
    show algebraMap _ _ ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : FractionRing V)) = _
    rw [hχ, hmf b _ ((hyy b mu).1 h), Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul]
  have hover := torus_label_over g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ χb hχb1 hlab qb (f qb) (hqb.1.trans hqy) hqbt hqbf
  have heq : fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ xF = f qb := by
    refine Over.OverMorphism.ext (𝔪.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hover, Over.comp_left, Category.assoc, hxF, ← Category.assoc]
    congr 1
    exact (Spec.map_comp _ _).symm
  rw [heq]
  exact hqbf

end GlobalTheory.Poinc.Sep.TorPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  first | exact @GlobalTheory.Poinc.Sep.TorPt.exists_torus_char | exact GlobalTheory.Poinc.Sep.TorPt.exists_torus_char | (intros; apply GlobalTheory.Poinc.Sep.TorPt.exists_torus_char <;> assumption)
end
end
