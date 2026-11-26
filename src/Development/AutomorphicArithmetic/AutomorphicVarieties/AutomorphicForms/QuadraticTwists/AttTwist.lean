module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.KstarRam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem sat_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (P : CuspSub K n)
    {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (h : (CG.mk P).HasSat w B) {κ : HChar K} (hκ : κ.UnrAt w) :
    (CG.mk (P.twist κ)).HasSat w (B.map (· * κ.val w)) := by
  rw [CG.hasSat_mk] at h ⊢
  exact GlobalTheory.SphGal.hasSatGL_twist K n P κ w B hκ h

theorem UpperTheory.V.Af.Cq.attTwist :
    ∀ (K Ω : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
        (R : G K Ω →* GL (Fin n) (Qbar l)) (P : CuspSub K n), AttC ι R P → ∀ (art : Ideles K →* Gab K Ω) (κ : HChar K) (m : (K →+* ℂ) → ℤ)
        (μ : G K Ω →* (Qbar l)ˣ), IsGlobalArtin art → IsLAdicOf art ι κ m μ → AttC ι (tw R μ) (P.twist κ) := by
  intro K Ω _ _ _ _ _ _ l _ ι n R P hA art κ m μ ha h
  refine ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G K Ω) _ n R).2.2 μ hA.1, ?_⟩
  filter_upwards [hA.2, Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified κ), ev_notMem (K := K) l]
    with w ⟨B, hB, hE⟩ hu hl
  refine ⟨_, sat_twist P hB hu, ?_⟩
  have hc : UpperTheory.V.Af.Bc.CharEig ι μ w (κ.val w : ℂ) := by
    refine fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
    rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
  have h4 := UpperTheory.frobenius_eigenvalues_twist K Ω l ι n R μ w _ _ hE hc
  convert h4 using 1
  simp only [algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.ContraPair in
private theorem paired_twist {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {π π' : CuspSub E n}
    (h : Paired π π' conjOp) (α ξ : HChar E)
    (hf : ∀ k : GL (Fin n) (Af E), opMul α (.fin k) * opMul ξ (conjOp (.fin k)) = 1)
    (hk : ∀ k : Kinf E n, opMul α (.cpt k) * opMul ξ (conjOp (.cpt k)) = 1)
    (hl : ∀ X : Lie E n, opAdd α (.lie X) + opAdd ξ (conjOp (.lie X)) = 0) :
    Paired (π.twist α) (π'.twist ξ) conjOp := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  let T := π.toTwist α
  let S := π'.toTwist ξ
  refine ⟨B.compl₁₂ T.symm.toLinearMap S.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact T.symm.map_eq_zero_iff.1 (h1 _ fun ψ => by simpa using h (S ψ))
  · exact S.symm.map_eq_zero_iff.1 (h2 _ fun φ => by simpa using h (T φ))
  all_goals
    obtain ⟨φ, rfl⟩ := T.surjective φ
    obtain ⟨ψ, rfl⟩ := S.surjective ψ
    simp only [T, S, CuspSub.op_toTwist, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · have e := h3 k φ ψ
    have e' := congrArg Units.val (hf k)
    simp only [conjOp, Units.val_mul, Units.val_one] at e e' ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    linear_combination (B φ ψ) * e'
  · have e := h4 k φ ψ
    have e' := congrArg Units.val (hk k)
    simp only [conjOp, Units.val_mul, Units.val_one] at e e' ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_eq_mul]
    linear_combination (B φ ψ) * e'
  · have e := h5 X φ ψ
    have e' := hl X
    have e3 : opMul ξ (conjOp (.lie X)) = 1 := rfl
    have e4 : opMul α (.lie X) = 1 := rfl
    rw [e3, e4]
    simp only [Units.val_one, one_smul, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination e + (B φ ψ) * e'

private theorem chiDet_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (χ : HChar E) (g : GA E n) :
    chiDet n (GlobalTheory.ThetaPull.thetaChar χ) g = chiDet n χ (GlobalTheory.ThetaPull.thetaA E n g) :=
  ((congrArg χ.1 (det_thetaGL _ g)).trans (map_inv χ.1 _)).symm

theorem UpperTheory.V.Af.Cq.csdTwist :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (ψ ξ : HChar E), GlobalTheory.ContraPair.DualIsConjBy P ψ →
        compNorm E (GlobalTheory.HeightCounting.Blocks.resReal ξ) = ψ⁻¹ → GlobalTheory.ContraPair.DualIsConj (P.twist ξ) := by
  intro E _ _ _ n P ψ ξ h e
  have e1 := GlobalTheory.HeightCounting.Blocks.mul_inv_compNorm ξ
  have e2 : ψ⁻¹ * GlobalTheory.ThetaPull.thetaChar ξ = ξ := by
    rw [← e1, e, mul_comm ξ, mul_inv_cancel_left]
  have h' := paired_twist h (GlobalTheory.ThetaPull.thetaChar ξ) ξ (fun k => ?_) (fun k => ?_) (fun X => ?_)
  · rwa [← CuspSub.twist_mul, e2] at h'
  · have a := GlobalTheory.ContraPair.Model.sc_fin ξ k
    apply Units.ext
    simp only [thetaOp, GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_one, add_zero] at a
    simp only [opMul, chiDet_theta, GlobalTheory.ThetaPull.thetaA_finGL, Units.val_mul, Units.val_one]
    exact a
  · have a := GlobalTheory.ContraPair.Model.sc_cpt ξ k
    apply Units.ext
    simp only [thetaOp, GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_one, add_zero] at a
    simp only [opMul, chiDet_theta, GlobalTheory.ThetaPull.thetaA_infGL, Units.val_mul, Units.val_one,
      ← toUnits_conj_PhiK]
    exact a
  · have a := GlobalTheory.ContraPair.Model.dualIsConjBy_resReal ξ
    rw [GlobalTheory.ContraPair.DualIsConjBy, ← CuspSub.twist_mul, e1] at a
    have b := ((GlobalTheory.ContraPair.Model.paired_line_iff _ _ _ _).1 a).2.2 (fun _ _ => (Matrix.of X).trace)
    simp only [GlobalTheory.ContraPair.conjOp, GlobalTheory.ContraPair.Model.sc, opTriv, opAdd, mul_zero, zero_add] at b ⊢
    simpa [Matrix.trace, star_sum] using b
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.exBridge :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) →
        ∃ Bw' : LocBridge l K Ω (Dec (F := K) A) O, Bw'.Kw = Bw.Kw ∧ Bw'.j = Bw.j ∧ Bw'.LL = Bw.LL := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw hK
  haveI : IsGalois K Ω := {}
  haveI : IsGalois F Ω := {}
  haveI : T2Space (G F Ω) := krullTopology_t2
  let r : G K Ω →* G F Ω := AlgEquiv.restrictScalarsHom F
  have hr : Continuous r := continuous_restrictScalarsHom F K Ω
  have hinj : Function.Injective r := fun a b h => AlgEquiv.ext fun x => congrArg (fun g : G F Ω => g x) h
  have hind : Topology.IsInducing r := (hr.isClosedEmbedding hinj).isInducing
  have hmem : ∀ σ : G K Ω, σ ∈ Dec (F := K) A ↔ r σ ∈ Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  have hfix : ∀ (g : ↥(Dec (F := F) A)) (x : K), (g : G F Ω) (algebraMap K Ω x) = algebraMap K Ω x := fun g x => by
    apply Bw.j.injective
    rw [← Bw.e_comm]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (Bw.e g).2 _ (hK x)
  let f : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A) :=
    (r.comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), fun g => ?_⟩
    let σ : G K Ω := AlgEquiv.ofRingEquiv (f := (g : G F Ω).toRingEquiv) (hfix g)
    have hσ : r σ = g := AlgEquiv.ext fun _ => rfl
    exact ⟨⟨σ, (hmem σ).2 (hσ ▸ g.2)⟩, Subtype.ext hσ⟩
  let φ : ↥(Dec (F := K) A) ≃* ↥(Dec (F := F) A) := MulEquiv.ofBijective f hf
  have hφ : Continuous φ := (hr.comp continuous_subtype_val).subtype_mk _
  have hφs : Continuous φ.symm := by
    rw [(hind.comp Topology.IsInducing.subtypeVal).continuous_iff]
    exact continuous_subtype_val.congr fun g => (congrArg Subtype.val (φ.apply_symm_apply g)).symm
  refine ⟨{ Kw := Bw.Kw, j := Bw.j, j_E := hK, j_dense := ?_, e := φ.trans Bw.e
            e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
            e_comm := fun g x => Bw.e_comm (φ g) x
            LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
            eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }, rfl, rfl, rfl⟩
  refine Bw.j_dense.trans (closure_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨algebraMap F K x, by simp only [← IsScalarTower.algebraMap_apply]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.recTransport :
    GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
                 [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v)
                 (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) j i →
                 ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V),
                   (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → ∀ rc rc', IsRec h rc → IsRec h' rc' →
                   ∀ y : WD h, WDRel (RingEquiv.refl Ω) y (rc' (algNorm σ')) → y = rc (algNorm σ) := by
  intro hL F K Ω _ _ _ _ _ _ _ _ _ A v w h h' j i P n σ σ' e he rc rc' hrc hrc' y hy
  obtain ⟨S, hS, -, -, -, -, hSt, -⟩ := GlobalTheory.WDTransport.exists_equiv_wd F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i P
  have hF := hL.2 F Ω A v h K Ω A w h' rc rc' hrc hrc' (RingEquiv.refl Ω) j i P.mem P.ext P.cont P.loc n
    { V := σ.V, ρ := σ.ρ, smooth := σ.smooth, irr := σ.irred }
    { V := σ'.V, ρ := σ'.ρ, smooth := σ'.smooth, irr := σ'.irred } e he
  have h1 : S (rc (IrrGL.of σ.ρ σ.smooth σ.irred)) = rc' (IrrGL.of σ'.ρ σ'.smooth σ'.irred) :=
    (hS _ _).1 ⟨n, hF⟩
  apply S.injective
  rw [(hS _ _).1 hy, rec_algNorm hrc, rec_algNorm hrc', hSt, h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

private theorem dense_of_approx {F K : Type} [Field F] [Field K] [NumberField K] (f : F →+* K)
    (w : HeightOneSpectrum (𝓞 K))
    (H : ∀ k a : K, a ≠ 0 → ∃ x : F, w.valuation K ((f x - k) / a) ≤ 1) :
    DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap K w
  refine Dense.of_closure (hd.mono ?_)
  rintro _ ⟨k, rfl⟩
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := by simp [c]
  obtain ⟨a, ha⟩ := w.valuation_surjective K (c * WithZero.exp (-1 : ℤ))
  have ha1 : w.valuation K a ≠ 0 := by rw [ha]; exact mul_ne_zero hc0 WithZero.exp_ne_zero
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha1
  obtain ⟨x, hx⟩ := H k a ha0
  refine ⟨_, hγ ?_, x, rfl⟩
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ha1), ha] at hx
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc, ← map_sub]
  have h1 : (Valued.v (algebraMap K (w.adicCompletion K) (f x - k)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x - k) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  rw [h1]
  refine hx.trans_lt ?_
  refine mul_lt_of_lt_one_right (zero_lt_iff.2 hc0) ?_
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

private theorem surj_of_dense {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] (f : F →+* K)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (hv : ∀ x : F, w.valuation K (f x) ≤ 1 → v.valuation F x ≤ 1)
    (hd : DenseRange fun x : F => algebraMap K (w.adicCompletion K) (f x))
    (κ : v.adicCompletion F →+* w.adicCompletion K) (hc : Continuous κ)
    (hκ : ∀ x, κ (algebraMap F _ x) = algebraMap K _ (f x)) : Function.Surjective κ := by
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (v.adicCompletionIntegers F)))
  have hcl := (hcomp.image hc).isClosed
  have ho : IsOpen (w.adicCompletionIntegers K : Set (w.adicCompletion K)) := Valued.isOpen_valuationSubring _
  have key : (w.adicCompletionIntegers K : Set (w.adicCompletion K)) ⊆ κ '' (v.adicCompletionIntegers F) := by
    refine (Dense.open_subset_closure_inter hd ho).trans (closure_minimal ?_ hcl)
    rintro _ ⟨h1, x, rfl⟩
    refine ⟨algebraMap F _ x, ?_, hκ x⟩
    have h2 : (Valued.v (algebraMap K (w.adicCompletion K) (f x)) : WithZero (Multiplicative ℤ)) =
      w.valuation K (f x) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : (Valued.v (algebraMap F (v.adicCompletion F) x) : WithZero (Multiplicative ℤ)) =
      v.valuation F x := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [h3]
    exact hv x (h2 ▸ h1)
  intro y
  rcases (w.adicCompletionIntegers K).mem_or_inv_mem y with h | h
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x, hx⟩
  · obtain ⟨x, -, hx⟩ := key h
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩

theorem UpperTheory.V.Af.Cq.exPlaceIso :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O),
        Induces Bw → (∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1) → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : IsPlaceOver A w)
          (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A v h O _ _ _ Bw hj hK
  obtain ⟨w, hw⟩ := place_between (L := K) h
  obtain ⟨κ, hκc, hκ⟩ := GlobalTheory.CompositumCompletion.exists_completion_map (algebraMap F K) v w (fun x => by
    rw [← hw, ← h x]
    show A.valuation (algebraMap K Ω (algebraMap F K x)) < 1 ↔ _
    rw [← IsScalarTower.algebraMap_apply])
  have hd := dense_of_approx (algebraMap F K) w (fun k a ha => by
    have hpos : 0 < ‖Bw.j (algebraMap K Ω a)‖ := by simpa using ha
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense (hK k)) _ hpos
    refine ⟨x, ?_⟩
    rw [← TraceCompl.algebraMap_mem_iff hw, hj, map_div₀, map_div₀, norm_div, div_le_one hpos, map_sub, map_sub,
      ← IsScalarTower.algebraMap_apply, ← dist_eq_norm, dist_comm]
    exact hx.le)
  have hs := surj_of_dense (algebraMap F K) v w (fun x hx => by
    rw [← TraceCompl.algebraMap_mem_iff hw, ← IsScalarTower.algebraMap_apply,
      TraceCompl.algebraMap_mem_iff h] at hx
    exact hx) hd κ hκc hκ
  exact ⟨w, hw, RingEquiv.ofBijective κ ⟨κ.injective, hs⟩, fun _ => Iff.rfl,
    fun x => IsScalarTower.algebraMap_apply F K Ω x, hκc, hκ⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.embPadic :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], Nonempty (K →+* ℚ_[l]) → ∀ (j : K →+* Om l) (x : K),
        j x ∈ Set.range (algebraMap ℚ_[l] (Om l)) := by
  intro K _ _ hK l _ hι j x
  obtain ⟨ι⟩ := hι
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmon : (minpoly ℚ x).Monic := minpoly.monic hint
  have hdle : (minpoly ℚ x).natDegree ≤ 2 := hK ▸ minpoly.natDegree_le x
  have hdpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
  have hroot : ∀ f : K →+* Om l, Polynomial.aeval (f x) (minpoly ℚ x) = 0 := by
    intro f
    rw [show f x = f.toRatAlgHom x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hy := hroot j
  have hw := hroot ((algebraMap ℚ_[l] (Om l)).comp ι)
  have hlead : (minpoly ℚ x).coeff (minpoly ℚ x).natDegree = 1 := hmon
  rw [Polynomial.aeval_eq_sum_range] at hy hw
  obtain hd | hd : (minpoly ℚ x).natDegree = 1 ∨ (minpoly ℚ x).natDegree = 2 := by omega
  · rw [hd] at hy hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul] at hy
    refine ⟨-((minpoly ℚ x).coeff 0 : ℚ_[l]), ?_⟩
    rw [map_neg, map_ratCast]
    linear_combination -hy
  · rw [hd] at hy hw hlead
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Rat.smul_def, pow_zero, pow_one,
      mul_one, zero_add, hlead, Rat.cast_one, one_mul, RingHom.comp_apply] at hy hw
    have hfac : (j x - algebraMap ℚ_[l] (Om l) (ι x)) *
        (j x + algebraMap ℚ_[l] (Om l) (ι x) + ((minpoly ℚ x).coeff 1 : Om l)) = 0 := by
      linear_combination hy - hw
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨ι x, (sub_eq_zero.1 h).symm⟩
    · refine ⟨-(ι x) - ((minpoly ℚ x).coeff 1 : ℚ_[l]), ?_⟩
      rw [map_sub, map_neg, map_ratCast]
      linear_combination -h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_valuationSubring_valuation_prime_lt_one (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let R : Subring Ω := (Int.castRingHom Ω).range
  have hpR : (p : Ω) ∈ R := ⟨p, by simp⟩
  let x : R := ⟨p, hpR⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    intro h
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton'] at h
    obtain ⟨⟨r, n, rfl⟩, hr⟩ := h
    have h1 : ((n * p : ℤ) : Ω) = 1 := by
      have := congrArg Subtype.val hr
      simpa [x] using this
    have h2 : n * (p : ℤ) = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) := ⟨n, by push_cast; linarith⟩
    have h4 : p ∣ 1 := Int.natCast_dvd_natCast.mp h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (B.mem_nonunits_iff).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

private theorem ringOfIntegers_rat_exists_int_eq (x : 𝓞 ℚ) : ∃ n : ℤ, x = (n : 𝓞 ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv x, ?_⟩
  have := eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x)
  exact (Rat.ringOfIntegersEquiv.symm_apply_apply x).symm.trans this

private theorem exists_isPlaceOver_natCast_mem_of_valuation_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (p : ℕ)
    (hp0 : p ≠ 0) (h : A.valuation (p : Ω) < 1) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v ∧ (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have hmem : ∀ x : 𝓞 ℚ, ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) x ∈ A := by
    intro x
    obtain ⟨n, rfl⟩ := ringOfIntegers_rat_exists_int_eq x
    simpa using A.intCast_mem n
  let f : 𝓞 ℚ →+* A := RingHom.codRestrict ((algebraMap ℚ Ω).comp (algebraMap (𝓞 ℚ) ℚ)) A hmem
  let I : Ideal (𝓞 ℚ) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x, x ∈ I ↔ A.valuation ((algebraMap ℚ Ω) (x : ℚ)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  have hpI : (p : 𝓞 ℚ) ∈ I := by
    rw [hI]
    simpa using h
  refine ⟨⟨I, Ideal.comap_isPrime f _, ?_⟩, fun x => (hI x).symm, hpI⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hpI
  exact hp0 (by exact_mod_cast hpI)

private theorem false_of_distinct_primes_mem_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hqv : (q : 𝓞 ℚ) ∈ v.asIdeal) : False := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have h1 : (p : ℤ) * p.gcdA q + (q : ℤ) * p.gcdB q = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    rfl
  have h2 : (((p : ℤ) * p.gcdA q + (q : ℤ) * p.gcdB q : ℤ) : 𝓞 ℚ) = 1 := by
    rw [h1]
    simp
  have h3 : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [← h2]
    push_cast
    exact add_mem (Ideal.mul_mem_right _ _ hpv) (Ideal.mul_mem_right _ _ hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h3)

private theorem exists_padicInt_sq_eq_neg_of_dvd_one_add (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (p : ℕ) (hdiv : (l : ℤ) ∣ 1 + p) :
    ∃ s : ℤ_[l], s ^ 2 = -(p : ℤ_[l]) := by
  let F : Polynomial ℤ := X ^ 2 + C (p : ℤ)
  have h2 : ‖((2 : ℤ) : ℤ_[l])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro hd
    have h' : l ∣ 2 := by exact_mod_cast hd
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have ha : (aeval (1 : ℤ_[l])) F = ((1 + p : ℤ) : ℤ_[l]) := by simp [F]
  have hd : (aeval (1 : ℤ_[l])) (derivative F) = ((2 : ℤ) : ℤ_[l]) := by
    simp [F]
    exact map_ofNat _ 2
  have hlt : ‖(aeval (1 : ℤ_[l])) F‖ < ‖(aeval (1 : ℤ_[l])) (derivative F)‖ ^ 2 := by
    rw [ha, hd, h2, one_pow, PadicInt.norm_int_lt_one_iff_dvd]
    exact hdiv
  obtain ⟨z, hz, -⟩ := hensels_lemma hlt
  refine ⟨z, ?_⟩
  have hz' : z ^ 2 + (p : ℤ_[l]) = 0 := by simpa [F] using hz
  linear_combination hz'

private theorem nonempty_ringHom_Kstar_of_sq_eq_neg (l : ℕ) [Fact l.Prime] (p : ℕ) (s : ℚ_[l]) (hs : s ^ 2 = -(p : ℚ_[l])) :
    Nonempty (Kstar p →+* ℚ_[l]) := by
  have hf : (map (algebraMap ℚ ℚ_[l]) (X ^ 2 + C (p : ℚ))) = (X - C s) * (X - C (-s)) := by
    have h' : C s ^ 2 = -C (p : ℚ_[l]) := by rw [← C_pow, hs, C_neg]
    rw [map_natCast] at h'
    simp only [Polynomial.map_add (f := _), Polynomial.map_pow, map_X, map_C, map_natCast, Polynomial.map_natCast, C_neg]
    linear_combination h'
  have hsp : (map (algebraMap ℚ ℚ_[l]) (X ^ 2 + C (p : ℚ))).Splits := by
    rw [hf]
    exact (Splits.X_sub_C s).mul (Splits.X_sub_C _)
  exact ⟨(SplittingField.lift _ hsp).toRingHom⟩

theorem UpperTheory.V.Af.Cq.exQuad :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (S : HeightOneSpectrum (𝓞 ℚ) → Prop), (∀ᶠ v in Filter.cofinite, S v) →
        ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (_ : IsAlgClosure K Ω),
          Module.finrank ℚ K = 2 ∧ Nonempty (K →+* ℚ_[l]) ∧ ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), S v ∧ IsPlaceOver A v ∧
            ∃ s ∈ Ine (F := ℚ) A, s ∉ (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω).range := by
  intro Ω _ instA _ l hl hl2 S hS
  haveI hc : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have e : instA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst e
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let P : Set ℕ := {p | p.Prime ∧ 4 * l ∣ p + 1}
  haveI hl0 : NeZero (4 * l) := ⟨by have := hl.out.pos; omega⟩
  have hPinf : P.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun n => ?_
    obtain ⟨p, hpn, hp, hpm⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * l) (a := -1) isUnit_one.neg n
    refine ⟨p, ⟨hp, ?_⟩, hpn⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hpm]
    ring
  haveI : Infinite P := hPinf.to_subtype
  have hA : ∀ p : P, ∃ A : ValuationSubring Ω, A.valuation ((p : ℕ) : Ω) < 1 :=
    fun p => exists_valuationSubring_valuation_prime_lt_one Ω p p.2.1
  choose Af hAf using hA
  have hv : ∀ p : P, ∃ v : HeightOneSpectrum (𝓞 ℚ),
      IsPlaceOver (Af p) v ∧ ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
    fun p => exists_isPlaceOver_natCast_mem_of_valuation_lt_one (Af p) p p.2.1.ne_zero (hAf p)
  choose vf hvf1 hvf2 using hv
  have hinj : Function.Injective vf := by
    intro p q hpq
    by_contra hne
    exact false_of_distinct_primes_mem_asIdeal (vf p) p q p.2.1 q.2.1 (fun h => hne (Subtype.ext h)) (hvf2 p) (hpq ▸ hvf2 q)
  have hfin : (vf ⁻¹' {v | ¬ S v}).Finite :=
    (Filter.eventually_cofinite.mp hS).preimage hinj.injOn
  obtain ⟨p, hpS⟩ := hfin.infinite_compl.nonempty
  have hSv : S (vf p) := by simpa using hpS
  obtain ⟨hp, hdvd⟩ := p.2
  have h4 : 4 ∣ (p : ℕ) + 1 := dvd_trans (Dvd.intro l rfl) hdvd
  have hp4 : (p : ℕ) % 4 = 3 := by omega
  have hl' : l ∣ (p : ℕ) + 1 := dvd_trans (Dvd.intro_left 4 rfl) hdvd
  have hdiv : (l : ℤ) ∣ 1 + ((p : ℕ) : ℤ) := by
    have := Int.natCast_dvd_natCast.mpr hl'
    push_cast at this
    rwa [add_comm] at this
  obtain ⟨s, hs⟩ := exists_padicInt_sq_eq_neg_of_dvd_one_add l hl2 p hdiv
  have hs' : (s : ℚ_[l]) ^ 2 = -((p : ℕ) : ℚ_[l]) := by
    have := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) hs
    push_cast at this
    exact this
  obtain ⟨ι⟩ := nonempty_ringHom_Kstar_of_sq_eq_neg l p s hs'
  obtain ⟨-, htc, hfr, -⟩ := HV.kstar p hp hp4
  let φ : Kstar p →ₐ[ℚ] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI alg : Algebra (Kstar p) Ω := φ.toRingHom.toAlgebra
  haveI tower : IsScalarTower ℚ (Kstar p) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  haveI : Algebra.IsAlgebraic (Kstar p) Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) (Kstar p)
  haveI hac : IsAlgClosure (Kstar p) Ω := ⟨inferInstance, inferInstance⟩
  haveI := htc
  haveI : Algebra.IsQuadraticExtension ℚ (Kstar p) := ⟨hfr⟩
  have hram := HV.kstarRam p hp hp4 Ω (Af p) (hAf p)
  obtain ⟨σ, hσI, hσG⟩ := SetLike.not_le_iff_exists.mp hram
  refine ⟨Kstar p, inferInstance, inferInstance, IsCMField.ofCMExtension ℚ (Kstar p), alg, tower, hac,
    hfr, ⟨ι⟩, vf p, Af p, hSv, hvf1 p, σ, hσI, ?_⟩
  rintro ⟨τ, rfl⟩
  apply hσG
  intro x
  exact τ.commutes x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Af.Cq.pstRes :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O),
        Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
        IsPstAt (Loc.PP l) Bw' ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)).comp (Dec (F := K) A).subtype) := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj hL n r hr
  obtain ⟨Kw', j', jE', jd', e', ec', esc', ecomm', LL0', hs', eO', h1', h2', h3'⟩ := Bw'
  dsimp only at hK hj hL
  subst hK hj hL
  obtain ⟨LL', r', ⟨hle, hmap⟩, hpst⟩ := hr
  refine ⟨LL', r'.comp (e'.trans Bw.e.symm).toMonoidHom, ⟨hle, ?_⟩, ?_⟩
  · refine MonoidHom.ext fun g => ?_
    have h1 := DFunLike.congr_fun hmap (Bw.e.symm (e' g))
    have h2 : ((Bw.e.symm (e' g) : ↥(Dec (F := F) A)) : Ω ≃ₐ[F] Ω) =
        AlgEquiv.restrictScalarsHom F (g : Ω ≃ₐ[K] Ω) := by
      refine AlgEquiv.ext fun x => Bw.j.injective ?_
      rw [← Bw.e_comm, MulEquiv.apply_symm_apply, ecomm']
      rfl
    refine h1.trans ?_
    exact congrArg r h2
  · convert hpst using 1
    refine MonoidHom.ext fun g => ?_
    simp [LocBridge.repE]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {ρ' : Weil h' → Module.End ℂ V} {N : Module.End ℂ V}
    {a : WDRep h V} {b : WDRep h' V} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N b)
    (hρ : ∀ σ σ', WeilRel φ σ σ' → ρ σ = ρ' σ') : WDRel φ (WD.mk a) (WD.mk b) := by
  let e := (Module.finBasis ℂ V).equivFun
  refine ⟨_, a.transport e, b.transport e, WD.sound (a.iso_transport e).symm, WD.sound (b.iso_transport e).symm,
    ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ a.N = e.conjAlgEquiv ℂ b.N
    rw [ha.1, hb.1]
  · show e.conjAlgEquiv ℂ (a.ρ σ) = e.conjAlgEquiv ℂ (b.ρ σ')
    have h1 := hρ σ σ' hσ
    have h2 := hb.2 σ'
    rw [← h1] at h2
    rw [(Module.End.isNilpotent_isSemisimple_unique (ha.2 σ).2 (a.semisimple σ) h2.2 (b.semisimple σ')
      ((ha.2 σ).1.symm.sub_left (Commute.refl _)) (h2.1.symm.sub_left (Commute.refl _))
      (by simp)).2]

set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Af.Cq.wdRelRes :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O),
        Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
        ∀ (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (hj : Induces Bw) (hj' : Induces Bw')
          (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i →
          WDRel (RingEquiv.refl Ω) (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype))
            (wdAt (Loc.PP l) ι Bw' h' hj' ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)).comp (Dec (F := K) A).subtype)) := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hJ hL n r hr ι v w h h' hj hj' i hP
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  obtain ⟨L, r', hm, hV⟩ := hr
  have key : ∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  let r'' : ↥(Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)).comp (Dec (F := K) A).subtype)
      L r'' := by
    refine ⟨hm.1, MonoidHom.ext fun g => ?_⟩
    have h1 := DFunLike.congr_fun hm.2 (Bw.e.symm (e g))
    refine h1.trans (congrArg r (AlgEquiv.ext (key g)))
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst (Loc.PP l) (Bw'.repE L r'') := by rw [hrep]; exact hV
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  obtain ⟨c, hc, hdeg, hq, -⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, ← (hc σ σ').1 hσ, hdeg, resDeg, resDeg, hq]
  have h4 : weilD Bw h (Loc.PP l) ρ σ = weilD Bw' h' (Loc.PP l) ρ σ' :=
    (weilD_apply Bw h (Loc.PP l) ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD (Loc.PP l) ρ g *
      Units.val (phiU (Loc.PP l) ρ ^ (-m)))
      h1 h3).trans (weilD_apply Bw' h' (Loc.PP l) ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk (Loc.PP l) ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk (Loc.PP l) ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk (Loc.PP l) ι Bw' h' hj' ρ σ' x).symm)
end
