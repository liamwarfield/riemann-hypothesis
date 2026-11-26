module

public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HeckeCharacterEqOfCofinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasSatOfFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormLocalCompatibility

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsPlaceCompletionIso
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_completion_iso : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → Dec (F := F) A ≤ (res F Ω K).range → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  first | exact @GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range | exact GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range | (intros; apply GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.HasFixedOfHasSat
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalGlobalCompatibilityReal
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_compatibility_real : AdmissibleReal → LocCompR := by
  first | exact @GlobalTheory.RealGal.locCompR_of_admissibleReal | exact GlobalTheory.RealGal.locCompR_of_admissibleReal | (intros; apply GlobalTheory.RealGal.locCompR_of_admissibleReal <;> assumption)
end

noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.TwistUnr

section Loc

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

theorem isLocComp_twist {π : TR.CuspSub F a} {η : HChar F} (hT : IsoTwist π η) {u : HeightOneSpectrum (𝓞 F)}
    {σ : SmIrr (GL (Fin a) (u.adicCompletion F))} (hσ : π.IsLocComp u σ) :
    π.IsLocComp u (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)) := by
  obtain ⟨T, hT1, -, -⟩ := hT
  obtain ⟨f, hf0, hf⟩ := hσ
  have key : ∀ g x, π.locRep u g (T.symm x) =
      ((GlobalTheory.CuspRep.CuspSub.locDet a η u g : ℂˣ) : ℂ) • T.symm (π.locRep u g x) := by
    intro g x
    have h1 := hT1 (locGL F a u g) (T.symm x)
    rw [LinearEquiv.apply_symm_apply, TR.CuspSub.chiDet_locGL] at h1
    apply T.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact h1
  refine ⟨T.symm.toLinearMap ∘ₗ f, fun h => hf0 (LinearMap.ext fun v => T.symm.injective ?_), fun g v => ?_⟩
  · have h2 := LinearMap.congr_fun h v
    rw [LinearMap.zero_apply, map_zero]
    exact h2
  · change T.symm (f (((GlobalTheory.CuspRep.CuspSub.locDet a η u g : ℂˣ) : ℂ) • σ.ρ g v)) = π.locRep u g (T.symm (f v))
    rw [key, LinearMap.map_smul, LinearEquiv.map_smul]
    congr 2
    exact hf g v

theorem hasFixed_of_hasSat (hL : LocCompR) {π : TR.CuspSub F a} {u : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ}
    (hB : π.HasSat u B) {σ : SmIrr (GL (Fin a) (u.adicCompletion F))} (hσ : π.IsLocComp u σ) :
    HasFixed σ.ρ (GlobalTheory.LFun.KGL u (n := a)) := by
  refine ((hL F a π u).2 σ hσ).hasFixed (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL u a).2 ?_
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 hB.1
  exact ⟨x, h0, fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k hk⟩

end Loc

section Par

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem unr_of_hasFixed {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hf : HasFixed σ.ρ (GlobalTheory.LFun.KGL w (n := n))) :
    (rc (cls (ParLaws.toRep σ))).unr := by
  refine (ParLaws.unr_iff H _).2 ?_
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  obtain ⟨v, h0, hv⟩ := hf
  exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 hv, h0⟩

theorem ine_trivial {x : WD h} (hx : x.unr) (hd : 1 ≤ x.lpDim) {ξ : Weil h →* ℂˣ} (hξ : IsSmooth ξ)
    (ht : (x.lpChar (WD.lpOfChar h ξ hξ)).unr) (s : Ine (F := E) A) : ξ (ineIncl h s) = 1 := by
  rw [lpChar_lpOfChar] at ht
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTwist_mk, WD.unr_mk] at ht
  rw [WD.unr_mk] at hx
  rw [WD.lpDim_mk] at hd
  have h1 := ht.2 s
  change ((ξ (ineIncl h s) : ℂ) • b.ρ (ineIncl h s)) = 1 at h1
  rw [hx.2 s] at h1
  have hn : 1 ≤ n := by simpa using hd
  have h3 := congrFun (LinearMap.congr_fun h1 (fun _ => 1)) ⟨0, hn⟩
  simpa using h3

end Par

end GlobalTheory.RealGal.TwistUnr


open GlobalTheory.RealGal.TwistUnr in
theorem GlobalTheory.RealGal.unrAt_of_isoTwist : GlobalTheory.Mem.LiteralAutomorphy.LitN → AdmissibleReal → ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F), IsoTwist π η →
    ∀ (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ), π.HasSat u B → η.UnrAt u := by
  intro LN hA F _ _ _ a ha π η hT u B hB
  have hL := GlobalTheory.T.local_global_compatibility_real hA
  have L := LN.loc
  obtain ⟨σ, hσ⟩ := (hL F a π u).1
  have hσ' := isLocComp_twist hT hσ
  obtain ⟨A, hAu⟩ := exists_isPlaceOver (AlgebraicClosure F) u
  obtain ⟨rc, hrc⟩ := L.llc F (AlgebraicClosure F) A u hAu
  have H : IsRec hAu rc := GlobalTheory.LocLanglands.isRec_of_isRecLit L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz
    F (AlgebraicClosure F) A u hAu rc hrc
  have u1 := unr_of_hasFixed H σ (hasFixed_of_hasSat hL hB hσ)
  have u2 := unr_of_hasFixed H _ (hasFixed_of_hasSat hL hB hσ')
  obtain ⟨ar, har, ε, -, LL⟩ := H
  have hs := GlobalTheory.HeckeComp.smooth_loc η u
  have e : rc (cls (ParLaws.toRep (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a η u) (TR.CuspSub.isOpen_ker_locDet η u)))) =
      (rc (cls (ParLaws.toRep σ))).lpChar (rc (.ofChar (η.loc u) hs)) := by
    rw [← LL.twist]
    exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm
  rw [e, LL.one] at u2
  have hd : 1 ≤ (rc (cls (ParLaws.toRep σ))).lpDim := by rw [LL.dim]; exact ha
  have hi := ine_trivial u1 hd _ u2
  have hU : (WD.lpOfChar hAu ((η.loc u).comp ar) (har.smooth hs)).unr := by
    rw [WD.lpOfChar, WD.unr_mk]
    refine ⟨rfl, fun s => LinearMap.ext fun v => funext fun i => ?_⟩
    have := hi s
    simp [this]
  have hU' := (GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff har hs).1 hU
  intro x hx
  refine hU' x ?_
  have h0 : Valued.v (x : u.adicCompletion F) ≠ 0 := by simp
  rw [← GlobalTheory.SmGL.ord_eq_zero_iff, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero]
  unfold IsUnitAt at hx
  rw [hx, WithZero.log_one]
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AuxStatement23
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement_23 : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i → ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin a) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V), (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (v.adicCompletion F) (Fin a)) ≠ ⊥ → GlobalTheory.PRep.fixed σ'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin a)) ≠ ⊥) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ → GlobalTheory.SmGL.IsSpherical σ'.ρ) := by
  first | exact @GlobalTheory.CompletionIso.iwahori_spherical_transfer | exact GlobalTheory.CompletionIso.iwahori_spherical_transfer | (intros; apply GlobalTheory.CompletionIso.iwahori_spherical_transfer <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalEmbeddingRestrictExtension
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_restrict_extension : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), IsPstAt P Bw (r.comp (Dec (F := F) A).subtype) → ∀ (ι : Qbar l ≃+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i → WDRel (RingEquiv.refl Ω) (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)) (wdAt P ι Bw' h' hj' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype)) := by
  first | exact @GlobalTheory.RealGal.wdRelRes_gen | exact GlobalTheory.RealGal.wdRelRes_gen | (intros; apply GlobalTheory.RealGal.wdRelRes_gen <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalEmbeddingCompatibleExtension
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_compatible_extension : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (a : ℕ) (r : G F Ω →* GL (Fin a) (Qbar l)), (IsdRAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsdRAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsSstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsSstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsCrysAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ (IsPstAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) → IsPstAt P Bw (r.comp (Dec (F := F) A).subtype)) ∧ ∀ (τ : K →+* Qbar l) (J : Multiset ℤ), IsJumpsAt P Bw' ((r.comp (res F Ω K)).comp (Dec (F := K) A).subtype) τ J → IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) (τ.comp (algebraMap F K)) J := by
  first | exact @GlobalTheory.RealGal.dRSstCrysPstJumps_descend | exact GlobalTheory.RealGal.dRSstCrysPstJumps_descend | (intros; apply GlobalTheory.RealGal.dRSstCrysPstJumps_descend <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalEmbeddingAgree
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_agree : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∃ (τK : K →+* Qbar l) (τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), τK.comp (algebraMap F K) = τ ∧ IsInduced Bw' τK τ'' := by
  first | exact @GlobalTheory.induced_embedding_extends | exact GlobalTheory.induced_embedding_extends | (intros; apply GlobalTheory.induced_embedding_extends <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocalFieldEmbeddingMem
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_field_embedding_mem : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O), Dec (F := F) A ≤ (res F Ω K).range → ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := by
  first | exact @GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le | exact GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le | (intros; apply GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InertiaLeRangeOfUnramified
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.QuadraticCharacterUnramified

theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

theorem good {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {η : HChar F}
    (hq : IsQuadCharOf K η) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 F) = v ∧
      η.UnrAt v ∧ ((η.val v : ℂˣ) : ℂ) = if normV w = normV v then 1 else -1 := by
  filter_upwards [eventually_under (F := F) hq] with v hv
  obtain ⟨w, rfl, hw⟩ := hv
  obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
  refine ⟨w, rfl, h1, (congrArg Units.val h3).trans ?_⟩
  split_ifs <;> simp

theorem orderDvd_two {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {η : HChar F}
    (hq : IsQuadCharOf K η) : η.OrderDvd 2 := by
  show η ^ 2 = 1
  apply GlobalTheory.T.hecke_character_eq_of_cofinite F (η ^ 2) 1
  filter_upwards [good hq] with v hv
  obtain ⟨w, -, hu, hval⟩ := hv
  refine ⟨fun x hx => ?_, fun x _ => rfl, ?_⟩
  · rw [pow_two]
    change η.loc v x * η.loc v x = 1
    rw [hu x hx, one_mul]
  · have e1 : (1 : HChar F).val v = 1 := rfl
    rw [pow_two, HChar.val_mul, e1]
    apply Units.ext
    rw [Units.val_mul, hval, Units.val_one]
    split_ifs <;> norm_num

end GlobalTheory.QuadraticCharacterUnramified
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SatakeParametersLocal
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameters_local : SatLoc := by
  first | exact @GlobalTheory.RealGal.SatLocProof.main | exact GlobalTheory.RealGal.SatLocProof.main | (intros; apply GlobalTheory.RealGal.SatLocProof.main <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsNormVEqPow
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IsomorphismOfFrobeniusTraces
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isomorphism_of_frobenius_traces : IsoOfFrob := by
  first | exact @GlobalTheory.IsoOfFrobFree.main | exact GlobalTheory.IsoOfFrobFree.main | (intros; apply GlobalTheory.IsoOfFrobFree.main <;> assumption)
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AttUniq

theorem exists_normV_eq_pow (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (w : HeightOneSpectrum (𝓞 L)) : ∃ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f := by
  haveI := w.isMaximal
  refine ⟨w.asIdeal.inertiaDeg (𝓞 F), ?_⟩
  have h := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 F)).asIdeal (w.under (𝓞 F)).isPrime
      (w.under (𝓞 F)).ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at h
  simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

theorem main_of_isoOfFrob (hI : IsoOfFrob) : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r r' : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι K r → AttRes π ι K r' → RepIso r r' := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ l _ ι a π r r' hc hc' hs hs' h h'
  refine hI K Ω l ι a r r' hc hc' hs hs' ?_
  filter_upwards [h, h'] with w hw hw'
  obtain ⟨f, hf⟩ := exists_normV_eq_pow F K w
  obtain ⟨B, hB, hr⟩ := hw f hf
  obtain ⟨B', hB', hr'⟩ := hw' f hf
  obtain rfl := hB.unique hB'
  exact ⟨_, hr, hr'⟩

end GlobalTheory.AttUniq

theorem GlobalTheory.AttUniq.attRes_repIso : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r r' : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι K r → AttRes π ι K r' → RepIso r r' :=
  GlobalTheory.AttUniq.main_of_isoOfFrob GlobalTheory.T.isomorphism_of_frobenius_traces
end
