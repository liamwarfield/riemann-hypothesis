module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAUpDownOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdThruL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdCoreH

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAAcrossOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.V.Af.Bc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
private theorem mem_dec_of {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {s : G F Ω}
    (h : ∀ x, s x ∈ A ↔ x ∈ A) : s ∈ Dec (F := F) A := by
  refine mem_Dec.2 (ValuationSubring.ext _ _ fun x => ?_)
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h ((s⁻¹ : G F Ω) • x), AlgEquiv.smul_def, mul_inv_apply]
private theorem keeps_of_split {K₁ K₂ M Ω : Type} [Field K₁] [Field K₂] [NumberField K₂] [Field M] [NumberField M] [Field Ω] [Algebra ℚ Ω]
    [Algebra K₁ Ω] [Algebra K₂ Ω] [Algebra K₂ M] [Algebra M Ω] [IsScalarTower K₂ M Ω] [IsScalarTower ℚ K₂ Ω] [Algebra ℚ K₁] [IsScalarTower ℚ K₁ Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (hS : SplitIn l K₁ Ω)
    (hM : ∀ s : G K₂ Ω, resG ℚ K₂ Ω s ∈ (resG ℚ K₁ Ω).range → s ∈ (resG K₂ M Ω).range)
    (r : G K₂ Ω →* GL (Fin n) (Qbar l)) : Keeps r M := by
  intro w hw hU A hA
  have hA' : IsPlaceOver A (w.under (𝓞 K₂)) := fun x => by
    rw [IsScalarTower.algebraMap_apply K₂ M Ω]
    exact hA (algebraMap (𝓞 K₂) (𝓞 M) x)
  have hl : A.valuation (l : Ω) < 1 := by
    have h := (hA ((l : ℕ) : 𝓞 M)).2 hw
    simpa using h
  obtain ⟨κ, ⟨g, hg⟩, hne⟩ := hU A hA'
  let ρ : ↥(Dec (F := M) A) →* ↥(Dec (F := K₂) A) :=
    ((AlgEquiv.restrictScalarsHom K₂ : G M Ω →* G K₂ Ω).comp (Dec (F := M) A).subtype).codRestrict _ fun s =>
      mem_dec_of fun x => apply_mem_iff_of_mem_Dec s.2 x
  have hρ : Function.Surjective ρ := by
    intro s
    have hs0 : resG ℚ K₂ Ω s.1 ∈ (resG ℚ K₁ Ω).range := by
      have hd : resG ℚ K₂ Ω s.1 ∈ Dec (F := ℚ) A := mem_dec_of fun x => apply_mem_iff_of_mem_Dec s.2 x
      have hfix := hS A hl _ hd
      exact ⟨AlgEquiv.ofRingEquiv (f := (resG ℚ K₂ Ω s.1).toRingEquiv) hfix, AlgEquiv.ext fun x => rfl⟩
    obtain ⟨t, ht⟩ := hM s.1 hs0
    have hx : ∀ x, t x = s.1 x := fun x => DFunLike.congr_fun ht x
    refine ⟨⟨t, mem_dec_of fun x => ?_⟩, Subtype.ext ht⟩
    rw [hx]
    exact apply_mem_iff_of_mem_Dec s.2 x
  refine ⟨fun i => (κ i).comp ρ, ⟨g, fun s => hg (ρ s)⟩, fun i j e => hne i j (MonoidHom.ext fun s => ?_)⟩
  obtain ⟨t, rfl⟩ := hρ s
  exact DFunLike.congr_fun e t
private theorem step (hFL : FlagLaws) (hUD : _root_.UpperTheory.V.Z.Win.AUpDownAlt) (hP : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K]
    [Field K'] [NumberField K'] [IsCMField K'] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    (hK : Module.finrank ℚ K = 2) (hK' : Module.finrank ℚ K' = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hS : SplitIn l K Ω) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (hc : Continuous r) (hA : IsAutomorphicOverImagQuad ι r)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (hθ : IsAlgChar ι θ) (hd : DualTw r θ) (hI : IneAb r) (hF : Flagged r)
    (hi : IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K' Ω).range).subtype))
    (hW : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) :
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K' Ω →* G ℚ Ω)) := by
  obtain ⟨M, _, _, _, iK, iK', iM, tK, tK', gK, gK', hs, hs', hM, hM'⟩ := UpperTheory.V.Z.Bc.biQuad K K' Ω hK hK'
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have : IsAlgClosure K' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K'⟩
  have : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) M⟩
  have hconj : ∃ c : G ℚ Ω, IsConjEl c := by
    let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
    let : Algebra Ω ℂ := j.toRingHom.toAlgebra
    have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
    have : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
    let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
    exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
  obtain ⟨c, hcc⟩ := hconj
  have irrOfRange {Δ Δ' : Type} [Group Δ] [Group Δ']
      (f : Δ →* G ℚ Ω) (f' : Δ' →* G ℚ Ω) (h : ∀ s, ∃ t, f' t = f s)
      (hf : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
    refine ⟨hf.1, fun _ _ _ => trivial, fun W hW hInv => hf.2.2 W hW fun s v hv => ?_⟩
    obtain ⟨t, ht⟩ := h s
    simpa only [MonoidHom.comp_apply, ht] using hInv t v hv
  have pairing {F : Type} [Field F] [CharZero F] [Algebra F Ω] :
      ∃ P, IsPairing c (r.comp (resG ℚ F Ω)) (θ.comp (resG ℚ F Ω)) P := by
    obtain ⟨J, hJ⟩ := hd
    refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
    change resG ℚ F Ω s' = c * resG ℚ F Ω s * c⁻¹ at h
    have e : r c⁻¹ * r (resG ℚ F Ω s') = r (resG ℚ F Ω s) * r c⁻¹ := by
      rw [h, ← map_mul, ← map_mul]
      congr 1
      group
    have e' := congrArg Units.val e
    simp only [Units.val_mul] at e'
    simp only [MonoidHom.comp_apply]
    rw [Units.val_mul, ← Matrix.smul_mul, ← hJ (resG ℚ F Ω s)]
    simp only [Matrix.mul_assoc, e']
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have hiM : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine irrOfRange _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hi
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  have hiM' : IsIrr ((r.comp (resG ℚ K' Ω)).comp (resG K' M Ω)) := he ▸ hiM
  have hiK : IsIrr (r.comp (resG ℚ K Ω)) :=
    irrOfRange ((resG ℚ K Ω).comp (resG K M Ω)) (resG ℚ K Ω) (fun s => ⟨resG K M Ω s, rfl⟩) hiM
  have hiK' : IsIrr (r.comp (resG ℚ K' Ω)) :=
    irrOfRange ((resG ℚ K' Ω).comp (resG K' M Ω)) (resG ℚ K' Ω) (fun s => ⟨resG K' M Ω s, rfl⟩) hiM'
  obtain ⟨P, hPa⟩ := pairing (F := K)
  obtain ⟨P', hPa'⟩ := pairing (F := K')
  have pol : Sol.Pol ι (r.comp (resG ℚ K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P, hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa⟩
  have pol' : Sol.Pol ι (r.comp (resG ℚ K' Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      θ, c, P', hθ, UpperTheory.V.Ws.auSign θ, hcc, hPa'⟩
  have up := (hUD hP hR K M Ω hs l ι n hn (r.comp (resG ℚ K Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K Ω)) hiM pol
    (hA hc K hK hiK) (((hFL ℚ Ω l n r).2.2.2 K).2.1 hF)).1 hW
  rw [he] at up
  exact (hUD hP hR K' M Ω hs' l ι n hn (r.comp (resG ℚ K' Ω)) (hc.comp (continuous_restrictScalarsHom ℚ K' Ω)) hiM' pol'
    (hA hc K' hK' hiK') (((hFL ℚ Ω l n r).2.2.2 K').2.1 hF)).2 (((hFL ℚ Ω l n r).2.2.2 K').1 hI)
    (keeps_of_split hS (fun s h => (hM' s).2 h) _) up
end UpperTheory.V.Z.Win
theorem UpperTheory.V.Z.Win.a_across_of_statement :
    _root_.UpperTheory.V.Z.Win.AAcrossOfAlt := by
  intro hFL hUD _ hP hR K Ω _ _ _ _ _ _ _ hK l _ ι n hn hS r hc hA ⟨θ, hθ, hd⟩ hI hF hirr hW K' _ _ _ inst _ _ hK' hirr'
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨K'', _, _, _, _, _, hK'', hS'', h1, h2⟩ := UpperTheory.V.Z.Win.thirdSplit K K' Ω hK hK' l n r hirr hirr'
  have h3 := UpperTheory.V.Z.Win.step hFL hUD hP hR K K'' Ω hK hK'' l ι n hn hS r hc hA θ hθ hd hI hF h1 hW
  rw [inf_comm] at h2
  exact UpperTheory.V.Z.Win.step hFL hUD hP hR K'' K' Ω hK'' hK' l ι n hn hS'' r hc hA θ hθ hd hI hF h2 h3
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.GalN.V UpperTheory.V.Z.Win
set_option linter.unusedVariables false
namespace UpperTheory.V.Z.Win.Dn
theorem isoTw_alt : _root_.UpperTheory.V.Z.Win.AIsoTwAlt := _root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws ImaginaryQuadraticEtaCharacter.winTw
theorem aUpDown_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Win.AUpDownAlt :=
  _root_.UpperTheory.V.Z.Win.aUpDownOf_alt weakOfAtt flagLaws (thruAway plainRec) (_root_.UpperTheory.V.Z.Ord.thruL_alt H.toClassicalTheorems plainRec) ImaginaryQuadraticEtaCharacter.winUpDown ImaginaryQuadraticEtaCharacter.winOf
theorem aAcross_alt (H : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Win.AAcrossAlt := _root_.UpperTheory.V.Z.Win.a_across_of_statement flagLaws (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H) _root_.UpperTheory.V.Z.Win.Dn.isoTw_alt
theorem ends_rank_three_of_local (H : _root_.UpperTheory.V.Af.HypothesesH') : RowT := _root_.UpperTheory.Gal.SV.rowOf' H.litN.aut.gal
local instance  (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}
  (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsGalois F K]
theorem automorphy_up_base_change (H : _root_.UpperTheory.V.Af.HypothesesH') (hs : Group.IsSolvable (K ≃ₐ[F] K)) (hn : 1 ≤ n) (hc : Continuous r)
    (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) (hp : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hF : Flagged r)
    (h : WitA ι r) : WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
  (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) F K Ω hs l ι n hn r hc hi hp ha hF).1 h
theorem down'_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hs : Group.IsSolvable (K ≃ₐ[F] K)) (hn : 1 ≤ n) (hc : Continuous r)
    (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) (hp : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hF : Flagged r)
    (hI : IneAb r) (hK : Keeps r K) (h : WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) : WitA ι r :=
  (_root_.UpperTheory.V.Z.Win.Dn.aUpDown_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) F K Ω hs l ι n hn r hc hi hp ha hF).2 hI hK h
end
theorem across'_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hs : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x)
    {r : G ℚ Ω →* GL (Fin n) (Qbar l)} (hc : Continuous r) (ha : IsAutomorphicOverImagQuad ι r) (hd : ∃ θ, IsAlgChar ι θ ∧ DualTw r θ) (hI : IneAb r)
    (hF : Flagged r) (hi : IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)))
    (h : WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) : WitAQ ι r :=
  _root_.UpperTheory.V.Z.Win.Dn.aAcross_alt H H (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local H) K Ω hK l ι n hn hs r hc ha hd hI hF hi h
theorem twist'_alt (P : _root_.UpperTheory.V.Af.Hypotheses') {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {μ : G F Ω →* (Qbar l)ˣ} (hμ : IsAlgChar ι μ)
    (hc : Continuous μ) (h : WitA ι r) : WitA ι (tw r μ) :=
  (_root_.UpperTheory.V.Z.Win.Dn.isoTw_alt P F Ω l ι n r h).2 μ hμ
def DownCsdKAlt : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    [Group.IsSolvable (L ≃ₐ[K] L)] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (σ : G ℚ Ω), Sd.IsCC σ → Continuous r →
    (∃ P, Sd.IsPair σ r (cycBar K Ω l ^ (1 - (n : ℤ))) P) → IsIrr (r.comp (galEmb K L Ω)) →
    IneAb r → Flagged r → Keeps r L → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (r.comp (galEmb K L Ω)) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r
end UpperTheory.V.Z.Win.Dn
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthAwChain
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.ConjugateSelfDual ReciprocityTheory.Gal
private theorem contTwist {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [TopologicalSpace k]
    [IsTopologicalRing k] {n : ℕ} {r : Γ →* GL (Fin n) k} {χ : Γ →* kˣ} (hr : Continuous r) (hχ : Continuous χ) :
    Continuous (tw r χ) := by
  have h : Continuous fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  have e : (fun s => (((tw r χ s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      (fun s => ((tw r χ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) ∘ fun s => s⁻¹ := by
    funext s
    simp only [Function.comp_apply, map_inv]
  rw [e]
  exact h.comp continuous_inv
theorem UpperTheory.V.Z.Win.Birth.awChain_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Win.Birth.AwChain := by
  intro hH F E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE l _ ι r κ hr hPR hκ hirr
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  haveI : Fact ((2 : ℕ) = 2) := ⟨rfl⟩
  have hirrE : IsIrr (r.comp (galEmb F E Ω)) :=
    ⟨hirr.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => hirr.2.2 W hW fun g v hv => hI (galEmb E M Ω g) v hv⟩
  have hW := UpperTheory.V.Z.Win.Birth.awReal F E Ω hE l ι r hr hirrE hPR
  have hcE : Continuous (r.comp (galEmb F E Ω)) := hr.comp (continuous_restrictScalarsHom F E Ω)
  obtain ⟨π, hreg, hatt, -⟩ := hPR
  have hAut : IsAutC ι (r.comp (galEmb F E Ω)) :=
    _root_.UpperTheory.V.Sd.up_quad_of_printed_results hH.toClassicalTheorems F E Ω l ι hE 2 one_le_two r hr ⟨π, hreg, hatt⟩ hirrE
  have hTw := UpperTheory.V.Z.Win.Birth.awTw E Ω l 2 le_rfl ι _ κ hκ hAut hW
  have hAutT := _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems E Ω l ι 2 _ κ hκ hAut
  have e2 : (tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω) =
      tw ((r.comp (galEmb F E Ω)).comp (galEmb E M Ω)) (κ.comp (galEmb E M Ω)) := rfl
  have hirrT : IsIrr ((tw (r.comp (galEmb F E Ω)) κ).comp (galEmb E M Ω)) :=
    e2 ▸ (shapeFacts l _ 2 _ _).2.2.2.2.2 hirr
  exact UpperTheory.V.Z.Win.Birth.awUp (_root_.UpperTheory.V.Z.Bc.upCyc_of_alt hH.toClassicalTheorems hH.cyc) E M Ω l ι 2 le_rfl _
    (contTwist hcE hκ.1) hAutT hirrT hTw
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
section Abstract
open UpperTheory.V.W
private theorem jr_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem jr_isTeich {l : ℕ} [hl : Fact l.Prime] {F : GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1 := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := jr_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩, fun i g h => ?_⟩
  · rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  · rw [MonoidHom.comp_apply, h, map_one]
private theorem jr_abs {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B) {ι : Type} (K : Type) [CommRing K] [Algebra O K]
    (x : ι → B.B →ₐ[O] K) (hJ : ∀ i, ∀ b ∈ J, x i b = 0) (sep : ∀ b, (∀ i, x i b = 0) → b ∈ J)
    (ρ : ι → F.G₀ →* GL (Fin n) K) (hD : ∀ i, B.u.D.map (x i : B.B →+* K) = GDet.ofRep (mat (ρ i)))
    (form : ∀ i, ∃ P, F.IsForm O n (ρ i) P)
    (flag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (x i : B.B →+* K) (B.u.ψ v j))
    (type : ∀ i t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
      ((g * ρ i y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y))
    (unr : r.V0ok → ∀ i, ∀ g ∈ F.I0, ρ i g = 1)
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1)
    (fin : ((Ideal.Quotient.mk J).comp (Λ.toPair B.u : Λ.Λ →+* B.B)).Finite)
    (tf : ∀ a : Λ.Λ, a ≠ 0 → ∀ b : B.B, Λ.toPair B.u a * b ∈ J → b ∈ J) : B.RingProps Λ J := by
  let f : ι → (B.B ⧸ J) →ₐ[O] K := fun i => Ideal.Quotient.liftₐ J (x i) (hJ i)
  have hf : ∀ i, (f i : B.B ⧸ J →+* K).comp (Ideal.Quotient.mk J) = x i := fun i => rfl
  have hinj : ∀ a, (∀ i, f i a = 0) → a = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (sep b ha)
  have hD' : ∀ i, (B.DD J).map (f i : B.B ⧸ J →+* K) = GDet.ofRep (mat (ρ i)) := fun i => by
    rw [UniversalOrdinaryDeterminantRing.DD, (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D _).2.2.2.2.2.2.1, hf, hD]
  have hflag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) := flag
  have hP : F.IsPolar O (B.DD J) := UpperTheory.V.AlgebraTools.Det.polarInj F O _ n _ (fun _ => K) f hinj fun i => by
    obtain ⟨P, hP⟩ := form i
    rw [hD' i]
    exact (UpperTheory.V.AlgebraTools.Det.formRep F O K n (ρ i) P hP).2.2
  have hker : ∀ g, (∀ i, ρ i g = 1) → (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) ∧
      (B.DD J).Kills (F.star O _ n (MonoidAlgebra.single g 1) - 1) := fun g hg => by
    have hk : (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      rw [map_sub, map_sub, map_one, map_one, MonoidAlgebra.mapRingHom_single, map_one]
      simp [GDet.repAlg, mat, hg i]
    refine ⟨hk, ?_⟩
    have h1 := UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk
    have h2 : F.star O (B.B ⧸ J) n (MonoidAlgebra.single g 1 - 1) = F.star O _ n (MonoidAlgebra.single g 1) - 1 := by
      simp [GFrame.star]
    rwa [h2] at h1
  refine ⟨fin, tf, hP, fun v g => ?_, fun v g => ?_, fun u g hg => hker g fun i => ?_, fun t ht u => ?_,
    fun h g hg => hker g fun i => unr h i g hg⟩
  · ext k
    rw [← sub_eq_zero]
    apply hinj
    intro i
    have h1 := (UpperTheory.V.AlgebraTools.Det.mapApi (B.DD J) (f i : B.B ⧸ J →+* K)).1 (MonoidAlgebra.single (F.φ v g) 1)
    rw [hD' i, MonoidAlgebra.mapRingHom_single, map_one, (UpperTheory.V.AlgebraTools.Det.repApi (mat (ρ i))).2.1] at h1
    have h2 := (UpperTheory.V.AlgebraTools.Det.flagRel _ _ (hflag i v)).1 g
    have h3 : mat ((ρ i).comp (F.φ v)) g = mat (ρ i) (F.φ v g) := rfl
    rw [h3, h1] at h2
    have h4 : (∏ j, (X - C ((B.psiT J v j g : (B.B ⧸ J)ˣ) : B.B ⧸ J))).map (f i : B.B ⧸ J →+* K) =
        ∏ j, (X - C ((pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) g : Kˣ) : K)) := by
      rw [Polynomial.map_prod]
      simp
    have h5 := congrArg (fun p => p.coeff k) (h2.trans h4.symm)
    simp only [Polynomial.coeff_map] at h5
    rw [map_sub, sub_eq_zero]
    exact h5
  · have hk : (B.DD J).Kills (F.oEl v (B.psiT J v) g) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      have h1 : MonoidAlgebra.mapRingHom F.G₀ (f i : B.B ⧸ J →+* K) (F.oEl v (B.psiT J v) g) =
          F.oEl v (fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j)) g := by
        unfold GFrame.oEl
        rw [map_list_prod, List.map_ofFn]
        apply congrArg (fun terms => (List.ofFn terms).prod)
        funext j
        simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one,
          pushCh, MonoidHom.comp_apply, Units.coe_map]
        rfl
      rw [h1]
      exact UpperTheory.V.AlgebraTools.Det.oElRep F O K n (ρ i) v _ (hflag i v) g
    exact ⟨hk, UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk⟩
  · obtain ⟨t, ht, ht1⟩ := hT
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 := hQ g hg.1
    have h2 : ∀ j, t j g = 1 := fun j => ht1 j g (Subgroup.mem_iInf.1 hg.2 j)
    simp only [h2, Units.val_one, map_one, Matrix.diagonal_one] at h1
    have h3 : Q * ρ i g * Q⁻¹ = 1 := Units.ext h1
    simpa using h3
  · refine (UpperTheory.V.AlgebraTools.Det.injTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) hinj).1 _ _ fun i => ?_
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 : ((B.DD J).comap (F.Iu u).subtype).map (f i : B.B ⧸ J →+* K) =
        ((B.DD J).map (f i : B.B ⧸ J →+* K)).comap (F.Iu u).subtype := rfl
    rw [h1, hD', (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.1, (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.1]
    refine (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q fun y => ?_
    have h2 : (RingHom.mapMatrix (f i : B.B ⧸ J →+* K)).toMonoidHom.comp
        (diagRep fun j => pushCh (algebraMap O (B.B ⧸ J)) ((t j).comp (F.Iu u).subtype)) y =
        Matrix.diagonal fun j => algebraMap O K (t j y) := by
      change (Matrix.diagonal _).map (f i) = _
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext j
      exact (f i).commutes _
    rw [h2, ← hQ y y.2, ← Units.val_mul, inv_mul_cancel_right]
    rfl
private theorem jr_surj {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) {T : Type} [CommRing T] [Algebra O T] [Algebra Λ.Λ T] (f : B.B →ₐ[O] T)
    (hsurj : Function.Surjective f) (hlam : ∀ b, f (Λ.toPair B.u b) = algebraMap Λ.Λ T b) (K : Type) [CommRing K] [Algebra O K]
    (good : (T →ₐ[O] K) → Prop) (sep : ∀ t, (∀ x, good x → x t = 0) → t = 0)
    (pt : ∀ x, good x → ∃ ρ : F.G₀ →* GL (Fin n) K, (B.u.D.map f.toRingHom).map x.toRingHom = GDet.ofRep (mat ρ) ∧
      (∃ P, F.IsForm O n ρ P) ∧
      (∀ v, HasFlag (ρ.comp (F.φ v)) fun j => pushCh x.toRingHom (pushCh f.toRingHom (B.u.ψ v j))) ∧
      (∀ t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
        ((g * ρ y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y)) ∧
      (r.V0ok → B.u.D.map (x.comp f : B.B →+* K) = GDet.ofRep (mat ρ) → ∀ g ∈ F.I0, ρ g = 1))
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1) (hfin : (algebraMap Λ.Λ T).Finite)
    (htf : ∀ b : Λ.Λ, b ≠ 0 → ∀ t : T, algebraMap Λ.Λ T b * t = 0 → t = 0) : B.RingProps Λ (RingHom.ker f) := by
  choose ρ hD hform hfl hty hun using fun x : {x // good x} => pt x.1 x.2
  have hD' : ∀ x : {x // good x}, B.u.D.map (x.1.comp f : B.B →+* K) = GDet.ofRep (mat (ρ x)) := fun x => by
    rw [← hD x]
    exact ((UpperTheory.V.AlgebraTools.Det.mapApi B.u.D f.toRingHom).2.2.2.2.2.2.1 x.1.toRingHom).symm
  refine jr_abs B Λ _ K (fun x : {x // good x} => x.1.comp f) (fun x b hb => ?_) (fun b hb => ?_) ρ hD' hform hfl hty
    (fun h x => hun x h (hD' x)) hT ?_ ?_
  · rw [AlgHom.comp_apply, (RingHom.mem_ker).1 hb, map_zero]
  · exact sep (f b) fun x hx => hb ⟨x, hx⟩
  · let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
    have he : (Ideal.Quotient.mk (RingHom.ker f)).comp (Λ.toPair B.u : Λ.Λ →+* B.B) =
        (e.symm : T →+* B.B ⧸ RingHom.ker f).comp (algebraMap Λ.Λ T) := by
      refine RingHom.ext fun b => ?_
      change _ = e.symm (algebraMap Λ.Λ T b)
      rw [AlgEquiv.eq_symm_apply]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hsurj _).trans (hlam b)
    rw [he]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp hfin
  · intro a ha b hb
    refine htf a ha (f b) ?_
    rw [← hlam, ← map_mul]
    exact hb
end Abstract
theorem UpperTheory.V.Hi.ring_props_of_is_j_unitary_hecke_data :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.RingProps Λ J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ
  rcases hJ with ⟨-, rfl⟩ | ⟨hcomm, hco, f, hne, hmap, hsurj, hlam, rfl⟩
  · refine jr_abs B Λ ⊤ (ι := Empty) (Qbar l) Empty.elim (fun i => i.elim) (fun _ _ => trivial) Empty.elim (fun i => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun _ i => i.elim) (jr_isTeich c r) ?_ fun _ _ _ _ => trivial
    exact RingHom.Finite.of_surjective _ fun b => ⟨0, Subsingleton.elim _ _⟩
  have hAx := _root_.UpperTheory.V.Hi.axU_s hP.litN l L Ω s n hn V Q c R.m R.τ₀
  obtain ⟨hdom, hden⟩ := _root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta hP.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta
  obtain ⟨-, hfin, htf, -⟩ := hiAlg L Ω l n c (hset Q R.τ₀) hAx Λ.Λ R.θ R.isWt R.a K hne
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have hAut := _root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor
    hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type
  have hLam : lam ∈ (hset Q R.τ₀).admitted := Set.mem_univ _
  have hout := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight
    hP.litN L Ω l n c (hset Q R.τ₀) hAx Λ.Λ R.θ R.isWt ι _ hAut lam hLam
    (hden lam) R.a K _ _ hmap
  refine jr_surj B Λ f hsurj hlam (Qbar l) _ (hout.sep lam hLam (hden lam)) (fun x hx => ?_) (jr_isTeich c r) hfin (htf hdom)
  obtain ⟨ρ, hc, -, hPU, hD, hfl⟩ := hout.pt lam hLam x hx.2.1
  exact ⟨ρ, hD, hPU.form, fun v => (hfl hx v).1, hPU.type, fun h h' => point_rep_unramified_at_auxiliary_place hn B h _ _ hc h'⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinTop
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N UpperTheory.V.Af UpperTheory.GalN.V
namespace UpperTheory.V.Z.Win
theorem aIsoTw_alt : _root_.UpperTheory.V.Z.Win.AIsoTwAlt := _root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws ImaginaryQuadraticEtaCharacter.winTw
theorem aUpDown_alt : _root_.UpperTheory.V.Z.Win.AUpDownAlt := fun P =>
  _root_.UpperTheory.V.Z.Win.aUpDownOf_alt weakOfAtt flagLaws thruF (_root_.UpperTheory.V.Z.Ord.thruL_alt P.toClassicalTheorems plainRec) ImaginaryQuadraticEtaCharacter.winUpDown ImaginaryQuadraticEtaCharacter.winOf P
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} [IsAlgClosure F Ω]
theorem WitA.witness_twist_algebraic_character [IsCMField F] (P : _root_.UpperTheory.V.Af.Hypotheses') {μ : G F Ω →* (Qbar l)ˣ} (hμ : IsAlgChar ι μ) (_hc : Continuous μ) (_ha : IsRegAlgAutomorphicAttached ι r)
    (h : WitA ι r) : WitA ι (Af.tw r μ) := (_root_.UpperTheory.V.Z.Win.aIsoTw_alt P F Ω l ι n r h).2 μ hμ
end UpperTheory.V.Z.Win
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJDense
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem UpperTheory.V.Hi.dense_arithmetic_points {O A B T E : Type} [CommRing O] [CommRing A] [CommRing B] [CommRing T] [CommRing E]
    [Algebra O A] [Algebra O B] [Algebra O T] [Algebra O E] [Algebra A T] (lam : A →ₐ[O] B) (f : B →ₐ[O] T)
    (hf : ∀ a, f (lam a) = algebraMap A T a) (P : (A →+* E) → Prop) (G : (B →ₐ[O] E) → Prop)
    (hG : ∀ x : B →ₐ[O] E, P (x.comp lam).toRingHom → G x)
    (hsep : ∀ t : T, (∀ x : T →ₐ[O] E, P (x.toRingHom.comp (algebraMap A T)) → x t = 0) → t = 0) (b : B)
    (hb : ∀ x : B →ₐ[O] E, RingHom.ker f ≤ RingHom.ker x → G x → x b = 0) : b ∈ RingHom.ker f := by
  rw [RingHom.mem_ker]
  refine hsep (f b) fun x hx => hb (x.comp f) (fun y hy => ?_) (hG _ ?_)
  · rw [RingHom.mem_ker] at hy ⊢
    rw [AlgHom.comp_apply, hy, map_zero]
  · have e : ((x.comp f).comp lam).toRingHom = x.toRingHom.comp (algebraMap A T) :=
      RingHom.ext fun y => congrArg x (hf y)
    rw [e]
    exact hx
theorem UpperTheory.V.Hi.dense_of_is_j_unitary_hecke_data :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.Dense J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ h hh b hb
  rcases hJ with ⟨_, rfl⟩ | ⟨hc, hco, f, _, hmap, hsurj, hlam, rfl⟩
  · exact Submodule.mem_top
  have hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis := hP.litN
  obtain ⟨⟨lam, hl⟩, hbr⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight hN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h hh
  have hd := (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta hN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam
  have hout := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight hN L Ω l n c (hset Q R.τ₀) (_root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _) hd R.a K _ _ hmap
  exact dense_arithmetic_points (Λ.toPair B.u) f hlam (fun x => (hset Q R.τ₀).Good R.θ x lam) (fun x : B.Pt => x.Good h)
    (fun x hx => (hbr lam hl x).2.2 hx) (hout.sep lam (Set.mem_univ _) hd) b hb
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd1W
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeIdealEnd
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
section SlopeTestRemainingChoices
open Formalism.MainNotions.N
variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩
private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl
end SlopeTestRemainingChoices
private theorem absPt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a K) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) {P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop} {I : Ideal (H.TK θ a K)}
    {ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ} (out : H.Out θ a K P I (D₀.map f.toRingHom) ψ)
    (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n) (hl : lam ∈ H.admitted)
    (har : H.Arith θ (x.comp j).toRingHom lam) :
    ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ P lam ρ ∧
      D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat ρ) := by
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hs, hP, hD, -⟩ := out.pt lam hl y (e1 ▸ har)
  exact ⟨ρ, hc, hs, hP, (map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD⟩
theorem hecke_ideal_end (H : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ _root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι lam ρ ∧
      x.IsRep (ρ.comp V.pr) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  have out := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight H.litN L Ω l n c (hset Q R.τ₀) (_root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _)
    ((_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  obtain ⟨ρ, hc, hs, hP, e3⟩ := absPt (hset Q R.τ₀) R.θ R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out x hx lam (Set.mem_univ _) har
  refine ⟨lam, ρ, hc, hs, hP, ?_⟩
  replace e3 : x.D = W.GDet.ofRep (W.mat ρ) := e3
  change x.D.comap V.pr = _
  rw [e3]
  exact (AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
open UpperTheory.GalN.V
theorem UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 L),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
    intro w
    have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L
      (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
        obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
        ext x
        apply (algebraMap L Ω).injective
        exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
    have hbot : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
    have he := UpperTheory.V.CF.ineCard.1 (Lp L) L w
    rw [hbot, Subgroup.card_bot] at he
    exact Ideal.ramificationIdx_eq_one_iff.1 he.symm
  refine fun x h hx ha => ?_
  · obtain ⟨lam, ρ, hc, hs, hP, hr⟩ := _root_.hecke_ideal_end H hn hJ x h hx ha
    have hc' : Continuous (ρ.comp V.pr) := hc.comp (V.pr_cont W.continuous_resP)
    have hs' : Formalism.MainNotions.N.IsSSRep (ρ.comp V.pr) := by
      intro M hM
      obtain ⟨M', hM', hcompl⟩ := hs M (fun g => by
        obtain ⟨g', rfl⟩ := hpr g
        exact hM g')
      exact ⟨M', fun g => hM' (V.pr g), hcompl⟩
    obtain ⟨σ, hσ, hlg, -⟩ := hP.aut
    exact ⟨_, hc', hs', hr,
      _root_.UpperTheory.V.Z.Win.Gu.endShape'_alt H L Ω hunr l s.odd ι n hn σ hσ _ hc' hs' hlg⟩
end
end
