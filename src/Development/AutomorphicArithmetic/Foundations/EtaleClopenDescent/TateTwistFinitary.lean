module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistFinitary
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem UpperTheory.Cb.tateTwist_finitary :
    ∀ (q : ℕ) (i : ℤ), Finitary (R := ZMod q) (tw q i) := by
  intro q i
  exact GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleMayerVietorisLongExact
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.BiprodCls

namespace UpperTheory.Cb.EtaleMayerVietoris

variable {R : Type} [CommRing R]

private theorem cpull_lift_neg {N K L : Cx R} (a : N ⟶ K) (b : N ⟶ L) (I : Cx R) (n : ℤ)
    (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a (-b)) I n y =
      cpull a I n (cpull biprod.inl I n y) - cpull b I n (cpull biprod.inr I n y) := by
  have hl : biprod.lift a (-b) = a ≫ biprod.inl + (-b) ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp
  have h0 : ∀ {P Q : Cx R} (x : CohomologyClass Q I n), cpull (0 : P ⟶ Q) I n x = 0 := by
    intro P Q x
    have h := cpull_add (0 : P ⟶ Q) 0 I n x
    rw [add_zero] at h
    simpa using h
  have hn : ∀ {P Q : Cx R} (f : P ⟶ Q) (x : CohomologyClass Q I n),
      cpull (-f) I n x = -cpull f I n x := by
    intro P Q f x
    have h := cpull_add f (-f) I n x
    rw [add_neg_cancel, h0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hl, cpull_add, ← cpull_cpull, ← cpull_cpull, hn, sub_eq_add_neg]

private theorem cpull_inl_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inl I n (cpull (biprod.desc c e) I n z) = cpull c I n z := by
  rw [cpull_cpull, biprod.inl_desc]

private theorem cpull_inr_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inr I n (cpull (biprod.desc c e) I n z) = cpull e I n z := by
  rw [cpull_cpull, biprod.inr_desc]

end UpperTheory.Cb.EtaleMayerVietoris

set_option maxHeartbeats 800000 in
open UpperTheory.Cb.EtaleMayerVietoris in
theorem UpperTheory.Cb.etale_mayer_vietoris_long_exact :
    LateralTheory.E.MayerVietorisSequence.LES := by
  intro R _ F
  obtain ⟨d0, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  refine ⟨fun a b c e w hS n => d0 _ hS n, ?_, ?_⟩
  · intro N K L M a b c e w hS n
    have hE := hex _ hS n
    obtain ⟨hinj, hsurj⟩ := cpull_biprod_bijective R K L (res R F) n
    have back : ∀ (z : CohomologyClass M (res R F) n) (u : CohomologyClass (K ⊞ L) (res R F) n),
        cpull biprod.inl (res R F) n u = cpull c (res R F) n z →
        cpull biprod.inr (res R F) n u = cpull e (res R F) n z →
        cpull (biprod.desc c e) (res R F) n z = u := by
      intro z u h1 h2
      refine hinj (Prod.ext ?_ ?_)
      · change cpull biprod.inl _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inl _ n u
        rw [cpull_inl_desc, h1]
      · change cpull biprod.inr _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inr _ n u
        rw [cpull_inr_desc, h2]
    refine ⟨fun x y => ?_, fun t => ?_, fun z => ?_⟩
    · obtain ⟨u, hu⟩ := hsurj (x, y)
      simp only [Prod.mk.injEq] at hu
      obtain ⟨hx, hy⟩ := hu
      have key : HK.pull R a F n x = HK.pull R b F n y ↔
          cpull (biprod.lift a (-b)) (res R F) n u = 0 := by
        rw [cpull_lift_neg, hx, hy, sub_eq_zero]
        rfl
      refine key.trans ((hE.1 u).trans ?_)
      constructor
      · rintro ⟨z, hz⟩
        have hz' : cpull (biprod.desc c e) (res R F) n z = u := hz
        refine ⟨z, ?_, ?_⟩
        · change cpull c (res R F) n z = x
          rw [← hx, ← hz', cpull_inl_desc]
        · change cpull e (res R F) n z = y
          rw [← hy, ← hz', cpull_inr_desc]
      · rintro ⟨z, hzx, hzy⟩
        exact ⟨z, back z u (hx.trans hzx.symm) (hy.trans hzy.symm)⟩
    · refine (hE.2.1 t).trans ?_
      constructor
      · rintro ⟨u, hu⟩
        have hu' : cpull (biprod.lift a (-b)) (res R F) n u = t := hu
        refine ⟨cpull biprod.inl (res R F) n u, cpull biprod.inr (res R F) n u, ?_⟩
        rw [← hu', cpull_lift_neg]
        rfl
      · rintro ⟨x, y, rfl⟩
        obtain ⟨u, hu⟩ := hsurj (x, y)
        simp only [Prod.mk.injEq] at hu
        obtain ⟨hx, hy⟩ := hu
        refine ⟨u, ?_⟩
        change cpull (biprod.lift a (-b)) (res R F) n u = _
        rw [cpull_lift_neg, hx, hy]
        rfl
    · obtain ⟨hinj1, -⟩ := cpull_biprod_bijective R K L (res R F) (n + 1)
      refine Iff.trans ?_ (hE.2.2 z)
      change _ ↔ cpull (biprod.desc c e) (res R F) (n + 1) z = 0
      constructor
      · rintro ⟨h1, h2⟩
        refine hinj1 (Prod.ext ?_ ?_)
        · change cpull biprod.inl _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inl _ _ 0
          rw [cpull_inl_desc, map_zero]
          exact h1
        · change cpull biprod.inr _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inr _ _ 0
          rw [cpull_inr_desc, map_zero]
          exact h2
      · intro h
        constructor
        · change cpull c (res R F) (n + 1) z = 0
          rw [← cpull_inl_desc c e, h, map_zero]
        · change cpull e (res R F) (n + 1) z = 0
          rw [← cpull_inr_desc c e, h, map_zero]
  · intro N K L M N' K' L' M' a b c e a' b' c' e' w w' hS hS' φN φK φL φM h1 h2 h3 h4 n t
    let φ : ShortComplex.mk (biprod.lift a (-b)) (biprod.desc c e) w ⟶
        ShortComplex.mk (biprod.lift a' (-b')) (biprod.desc c' e') w' :=
      { τ₁ := φN
        τ₂ := biprod.map φK φL
        τ₃ := φM
        comm₁₂ := by
          apply biprod.hom_ext <;> simp [h1, h2]
        comm₂₃ := by
          apply biprod.hom_ext' <;> simp [h3, h4] }
    exact hnat _ _ hS hS' φ n t
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistSectionsLocallyGenerated
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.TwSec

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (y : Sec F U) : Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

private noncomputable def gsec {q : ℕ} (i : ℤ) (U : Scheme.{0}) :
    (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] Sec (tw q i) U :=
  ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom ∘ₗ (twRel q i Γ(U, ⊤)).mkQ

private theorem gsec_one {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    gsec i U (Finsupp.single ζ 1) = twGen i ζ := rfl

end UpperTheory.Cb.TwSec

private theorem twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow {q : ℕ} (i : ℤ) {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      (ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single_one, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩

private theorem ulift_zmod_smul_eq_val_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (s : ULift.{1} (ZMod q)) (x : M) : s • x = s.down.val • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

private theorem exists_twRel_mk_eq_nsmul_mk_single_of_support_pow {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] (ζ : Prim q A)
    (f : Prim q A →₀ ULift.{1} (ZMod q)) (hf : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ c : ℕ, (Submodule.Quotient.mk f : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      c • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  have key : ∀ ξ, ∃ c : ℕ, (Submodule.Quotient.mk (Finsupp.single ξ (f ξ)) :
      (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = c • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
    intro ξ
    by_cases hξ : f ξ = 0
    · refine ⟨0, ?_⟩
      rw [hξ, Finsupp.single_zero, zero_smul]
      exact Submodule.Quotient.mk_zero _
    · obtain ⟨a, ha⟩ := hf ξ (Finsupp.mem_support_iff.mpr hξ)
      refine ⟨(f ξ * ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q))).down.val, ?_⟩
      rw [← ulift_zmod_smul_eq_val_nsmul, mul_smul, ← twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow i ζ ξ a ha, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]
  choose c hc using key
  refine ⟨∑ ξ ∈ f.support, c ξ, ?_⟩
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, Finset.sum_smul, ← Finset.sum_congr rfl (fun ξ _ => hc ξ)]
  exact map_sum (twRel q i A).mkQ _ _

private theorem sec_res_gsec_eq_gsec_mapDomain {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) :
    Sec.res g (UpperTheory.Cb.TwSec.gsec i U f) = UpperTheory.Cb.TwSec.gsec i V (Finsupp.mapDomain (Prim.map g.appTop.hom) f) := by
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk f : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  exact h.symm

private theorem gsec_single_eq_zpow_smul_gsec_single_of_eq_pow {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    UpperTheory.Cb.TwSec.gsec i U (Finsupp.single ξ 1) =
      (ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • UpperTheory.Cb.TwSec.gsec i U (Finsupp.single ζ 1) := by
  rw [← map_smul]
  have e : (twRel q i Γ(U, ⊤)).mkQ (Finsupp.single ξ 1) =
      (twRel q i Γ(U, ⊤)).mkQ ((ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • Finsupp.single ζ 1) := by
    rw [map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow i ζ ξ a h
  exact congrArg (fun t => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom t) e

private theorem exists_gsec_eq_nsmul_twGen_of_support_pow {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) (hf : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ c : ℕ, UpperTheory.Cb.TwSec.gsec i U f = c • twGen i ζ := by
  obtain ⟨c, hc⟩ := exists_twRel_mk_eq_nsmul_mk_single_of_support_pow i ζ f hf
  refine ⟨c, ?_⟩
  rw [← UpperTheory.Cb.TwSec.gsec_one, ← map_nsmul]
  have e : (twRel q i Γ(U, ⊤)).mkQ f = (twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1) := by
    rw [map_nsmul]
    exact hc
  exact congrArg (fun t => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom t) e

theorem UpperTheory.Cb.tateTwist_sections_locally_generated :
    ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  intro q _ i
  have h4 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
      Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    intro V U g ζ
    rw [← UpperTheory.Cb.TwSec.gsec_one, ← UpperTheory.Cb.TwSec.gsec_one, sec_res_gsec_eq_gsec_mapDomain, Finsupp.mapDomain_single]
  have h5 : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ := by
    intro U ζ ξ a h
    rw [← UpperTheory.Cb.TwSec.gsec_one, ← UpperTheory.Cb.TwSec.gsec_one, gsec_single_eq_zpow_smul_gsec_single_of_eq_pow i ζ ξ a h, ulift_zmod_smul_eq_val_nsmul]
  have L := GlobalTheory.T.etaleLocal_property_calculus_rules
  have S := GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (Scheme.Γ ⋙ twF q i)
  have h2 : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
      Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom) := by
    classical
    intro U ζ y
    apply L.2.2.2.2.1
    refine L.2.1 U _ _ (S.1 U y) ?_
    rintro V g ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : Sec.res g y = UpperTheory.Cb.TwSec.gsec i V f := hx.symm
    have hl := L.2.2.2.2.2.1 V (↥f.support) _ (fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (ζ.map g.appTop.hom) ξ.1)
    refine L.2.1 V _ _ hl ?_
    intro W k hk
    obtain ⟨c, hc⟩ := exists_gsec_eq_nsmul_twGen_of_support_pow i ((ζ.map g.appTop.hom).map k.appTop.hom)
      (Finsupp.mapDomain (Prim.map k.appTop.hom) f) (by
        intro ξ' hξ'
        obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hξ')
        obtain ⟨a, ha⟩ := hk ⟨ξ, hξ⟩
        exact ⟨a, ha⟩)
    refine ⟨c, ?_⟩
    have e : twGen i ((ζ.map g.appTop.hom).map k.appTop.hom) = twGen i (ζ.map (k ≫ g).appTop.hom) := by
      calc twGen i ((ζ.map g.appTop.hom).map k.appTop.hom) = Sec.res k (Sec.res g (twGen i ζ)) := by
            rw [h4, h4]
        _ = twGen i (ζ.map (k ≫ g).appTop.hom) := by
            rw [← UpperTheory.Cb.TwSec.res_comp, h4]
    rw [e] at hc
    rw [UpperTheory.Cb.TwSec.res_comp, hx']
    exact (sec_res_gsec_eq_gsec_mapDomain i k f).trans hc
  have h1 : ∀ (U : Scheme.{0}) (y : Sec (tw q i) U),
      Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
    intro U y
    apply L.2.2.2.2.1
    refine L.2.1 U _ _ (S.1 U y) ?_
    rintro V g ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : Sec.res g y = UpperTheory.Cb.TwSec.gsec i V f := hx.symm
    by_cases hP : Nonempty (Prim q Γ(V, ⊤))
    · obtain ⟨ζ⟩ := hP
      refine L.2.1 V _ _ (h2 V ζ (Sec.res g y)) ?_
      rintro W k ⟨c, hc⟩
      exact Or.inr ⟨_, c, by rw [UpperTheory.Cb.TwSec.res_comp]; exact hc⟩
    · apply L.1
      intro W k
      left
      have hf : f = 0 := by
        ext ξ
        exact (hP ⟨ξ⟩).elim
      rw [UpperTheory.Cb.TwSec.res_comp, hx', hf]
      exact (congrArg (Sec.res k) (map_zero (UpperTheory.Cb.TwSec.gsec i V))).trans (map_zero ((tw q i).obj.map k.op).hom)
  have h3 : ∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c := by
    intro U _ ζ c h
    have hz : UpperTheory.Cb.TwSec.gsec i U (c • Finsupp.single ζ 1) = 0 := by
      rw [map_nsmul, UpperTheory.Cb.TwSec.gsec_one]
      exact h
    have hl := S.2.1 U ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) hz
    obtain ⟨u⟩ := ‹Nonempty U›
    have hmono : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
        ((Scheme.Γ ⋙ twF q i).map g.op).hom ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) = 0 →
        ((Scheme.Γ ⋙ twF q i).map (k ≫ g).op).hom ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) = 0 := by
      intro V W g k hg
      change ((Scheme.Γ ⋙ twF q i).map (g.op ≫ k.op)).hom _ = 0
      rw [Functor.map_comp, ModuleCat.hom_comp]
      exact (congrArg (ModuleCat.Hom.hom ((Scheme.Γ ⋙ twF q i).map k.op)) hg).trans (map_zero _)
    obtain ⟨V, g, -, -, ⟨v, -⟩, hV⟩ := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hmono).mp hl u
    have hV' : (c • Submodule.Quotient.mk (Finsupp.single (ζ.map g.appTop.hom) 1) :
        (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(V, ⊤)) = 0 := by
      refine Eq.trans ?_ hV
      change _ = Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (c • Finsupp.single ζ 1))
      rw [Finsupp.smul_single, Finsupp.mapDomain_single, ← Finsupp.smul_single, Submodule.Quotient.mk_smul]
    haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
    haveI : Nontrivial Γ(V, ⊤) := Scheme.component_nontrivial V ⊤
    obtain ⟨φ, hφ⟩ := (GlobalTheory.T.tateTwistModule_free_and_generator_summand q i Γ(V, ⊤)).2 (ζ.map g.appTop.hom)
    have hc := congrArg φ hV'
    rw [map_nsmul, hφ, map_zero, nsmul_eq_mul, mul_one] at hc
    have hd := congrArg ULift.down hc
    rw [ULift.down_natCast] at hd
    exact (ZMod.natCast_eq_zero_iff c q).mp hd
  have h6 : ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U),
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) →
      (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
        e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) →
      ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
    intro M e hnat hrel
    let lin : ∀ U : Scheme.{0}, (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] M.obj.obj (op U) :=
      fun U => Finsupp.linearCombination (ULift.{1} (ZMod q)) (e U)
    have lin_single : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), lin U (Finsupp.single ζ 1) = e U ζ := by
      intro U ζ
      simp only [lin, Finsupp.linearCombination_single, one_smul]
    have hker : ∀ U : Scheme.{0}, twRel q i Γ(U, ⊤) ≤ LinearMap.ker (lin U) := by
      intro U
      refine Submodule.span_le.mpr ?_
      rintro x ⟨ζ, ξ, a, h, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin_single, ← Finsupp.smul_single_one, map_smul, lin_single,
        hrel U ζ ξ a h, ulift_zmod_smul_eq_val_nsmul, sub_self]
    let φ0 : Scheme.Γ ⋙ twF q i ⟶ M.obj :=
      { app := fun X => ModuleCat.ofHom ((twRel q i Γ(X.unop, ⊤)).liftQ (lin X.unop) (hker X.unop))
        naturality := by
          intro X Y f
          apply ModuleCat.hom_ext
          apply Submodule.linearMap_qext
          apply Finsupp.lhom_ext'
          intro ξ
          apply LinearMap.ext_ring
          change lin Y.unop (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ξ 1)) =
            (M.obj.map f).hom (lin X.unop (Finsupp.single ξ 1))
          erw [Finsupp.mapDomain_single]
          rw [lin_single]
          exact ((congrArg (M.obj.map f).hom (lin_single X.unop ξ)).trans (hnat Y.unop X.unop f.unop ξ)).symm }
    obtain ⟨ψ, hψ, huniq⟩ := S.2.2 M φ0
    refine ⟨ψ, fun U ζ => ?_, fun φ' hφ' => huniq φ' ?_⟩
    · have := congrArg (fun t => (t.app (op U)).hom
        (Submodule.Quotient.mk (p := twRel q i Γ(U, ⊤)) (Finsupp.single ζ 1))) hψ
      exact this.trans (lin_single U ζ)
    · apply NatTrans.ext
      funext X
      apply ModuleCat.hom_ext
      apply Submodule.linearMap_qext
      apply Finsupp.lhom_ext'
      intro ξ
      apply LinearMap.ext_ring
      exact (hφ' X.unop ξ).trans (lin_single X.unop ξ).symm
  exact ⟨h1, h2, h3, h4, h5, h6⟩
end
