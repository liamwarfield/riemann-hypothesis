module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ExistsIrreducibleTypeCharacters
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PTypeEx

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NzOfSteps
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeData
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeDataOfSTy
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
abbrev _root_.UpperTheory.NonzeroTypeTheory.typeData_of_s_ty : Prop := ∀ (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct) (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia)
    (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp) (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp),
    _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt
end UpperTheory.NonzeroTypeTheory
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ UpperTheory.NonzeroTypeTheory UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.T2
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
private theorem good_of_sph (x : IrrGL (k := w.adicCompletion E)) (hx : IsSpherical x.rep) : Good x := by
  obtain ⟨s, hs, h1⟩ := GlobalTheory.SphSupport.toral_of_isSpherical GlobalTheory.bernsteinZelevinskyFiniteness_holds _ x hx
  refine ⟨s, hs, fun y hy => Or.inl ?_⟩
  obtain ⟨χ, -, hχ, rfl⟩ := h1 y hy
  rfl
private theorem sph_of {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X) (hs : IsSmooth σ) (hi : σ.IsIrreducible)
    (hσ : IsSpherical σ) : IsSpherical (IrrGL.of σ hs hi).rep :=
  SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hσ
private theorem sphOfUnrV (H : UpperTheory.V.Z.Win.LawsV a ha ε rc) (d : ℕ) (v : WD h) (hv : v.unr) (hd : v.lpDim = d) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X)
      (hs : IsSmooth σ) (hi : σ.IsIrreducible), IsSpherical σ ∧ rc (IrrGL.of σ hs hi) = v := by
  subst hd
  obtain ⟨α, hα⟩ := GlobalTheory.LocLanglands.unr_eq_diag_inv E Ω A w h v hv
  obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
  have φ := equivRep π
  have hπ' : HasSatake (GlobalTheory.LocLanglands.cls π).rep α := ⟨IrrRep.irr _, SphericalUnramified.isSpherical_of_equiv φ hπ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.smooth, π.irr, hπ.2.1, ?_⟩
  exact (H.sat (GlobalTheory.LocLanglands.cls π) α hπ').trans hα.symm
private theorem prodRcV (L : UpperTheory.V.Z.Win.LawsV a ha ε rc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b))
      (hs : ∀ b, IsSmooth (σ b)) (hi : ∀ b, (σ b).IsIrreducible)
      (hI : (multiProd (stdBlocks d hd) σ).IsIrreducible),
      rc (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI) =
        sumList (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b))) := by
  intro s
  induction s with
  | zero =>
    intro N d hd X _ _ σ hs hi hI
    have h0 : N = 0 := by simpa using hd.symm
    rw [List.ofFn_zero, sumList, List.foldr_nil]
    exact P_prodRc.wd_eq_lpZero ((L.dim (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI)).trans h0)
  | succ s ih =>
    intro N d hd X _ _ σ hs hi hI
    obtain rfl : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨Φ⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hts : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => σ i.succ) :=
      isSmooth_parInd _ _
    have hti := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ _ _ _ _ _ _ (σ 0) _ (multiProd (stdBlocks d hd) σ)
      (hs 0) (hi 0) hts hI ⟨Φ.symm⟩
    have key := L.prod (d 0) (∑ i : Fin s, d i.succ) ⟨X 0, σ 0, hs 0, hi 0⟩ ⟨_, _, hts, hti⟩
      ⟨_, multiProd (stdBlocks d hd) σ, isSmooth_parInd _ _, hI⟩ ⟨Φ.symm⟩
    refine key.trans ?_
    rw [List.ofFn_succ, sumList, List.foldr_cons]
    congr 1
    exact ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs i.succ)
      (fun i => hi i.succ) hti
private theorem good_prod (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt) {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type)
    [∀ b, AddCommGroup (X b)] [∀ b, Module ℂ (X b)]
    (τ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b)) (hs : ∀ b, IsSmooth (τ b))
    (hi : ∀ b, (τ b).IsIrreducible) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ) (hη : ∀ b, IsSmoothChar (η b))
    (hdet : ∀ b, HasDetVec (τ b) (η b)) (hI : (multiProd (stdBlocks d hd) τ).IsIrreducible) :
    Good (IrrGL.of (multiProd (stdBlocks d hd) τ) (isSmooth_parInd _ _) hI) := by
  choose μ hμ hcs using fun b => _root_.UpperTheory.TNZ.step_cuspSupp_alt hL _ (d b) (X b) (τ b) (hs b) (hi b) (η b) (hη b) (hdet b)
  have hS := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel hd τ hs hi
    (fun b => hasSupport_of_isCuspSupport (hcs b)) hI
  refine ⟨_, hS.of_equiv (IrrGL.equivOf _ _ _), fun y hy => Or.inl ?_⟩
  obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hc
  rfl
private theorem gMainV (hLit : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt) (gi : ArtinInertiaProp) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc)
    {s : ℕ} (d : Fin s → ℕ) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ) (hη : ∀ b, IsSmoothChar (η b))
    (hdist : ∀ b c, b ≠ c → ∃ t : Ine (F := E) A, η b (a (ineIncl h t)) ≠ η c (a (ineIncl h t)))
    (x : IrrGL (k := w.adicCompletion E)) (hd : ∑ b, d b = x.1) :
    ((rc x).mono0 ∧ ∀ t : Ine (F := E) A,
        (rc x).charPol (ineIncl h t) = ∏ b, (X - C ((η b (a (ineIncl h t)) : ℂˣ) : ℂ)) ^ d b) ↔
      IsTwSphProd x.rep d hd η := by
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := step_isotypic E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := step_scalarInertia E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => sphOfUnrV H (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    have hs' : ∀ b, IsSmooth (twist (σ b) (detChar (Fin (d b)) (η b))) :=
      fun b => isSmooth_twist (hs b) (hη b).detChar
    have hi' : ∀ b, (twist (σ b) (detChar (Fin (d b)) (η b))).IsIrreducible := fun b => isIrreducible_twist (hi b) _
    have hrc' : ∀ b, rc (IrrGL.of (twist (σ b) (detChar (Fin (d b)) (η b))) (hs' b) (hi' b)) =
        (rc (IrrGL.of (σ b) (hs b) (hi b))).lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := fun b => by
      rw [← IrrGL.tw_of (hχ := hη b), H.twist _ _ _ (good_of_sph _ (sph_of _ _ _ (hsph b))), H.one]
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (step_detVec _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (gi E Ω A w h a ha).1 t, ht⟩
    have hI := _root_.UpperTheory.TNZ.step_prodIrr_alt _root_.UpperTheory.TNZ.step_cuspSupp_alt hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi'
      η hη hdet hdistU
    have hrcP := prodRcV H s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (H.inj x _ (good_prod hLit d hd Xs _ hs' hi' η hη hdet hI) heq.symm).symm.trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      have hs' : IsSmooth (twist (σ b) (detChar (Fin (d b)) (η b)⁻¹)) := isSmooth_twist (hs b) (hη b).inv.detChar
      have hi' : (twist (σ b) (detChar (Fin (d b)) (η b)⁻¹)).IsIrreducible := isIrreducible_twist (hi b) _
      have hsp := sph_of _ hs' hi' ((step_detVec _ (d b) (Xs b) (σ b) (η b)).2 (hdet b))
      refine ⟨_, (H.sph _).1 hsp, H.dim _, ?_⟩
      rw [P_untwistRc.of_eq_tw (σ b) (hs b) (hi b) (η b) (hη b), H.twist _ _ _ (good_of_sph _ hsp), H.one]
    choose u hu hud hur using hfac
    have hl := step_sumList E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := prodRcV H s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (step_unrTwist E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (step_unrTwist E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl
end UpperTheory.V.Z.Win.T2
theorem UpperTheory.V.Z.Win.T2.typeData_alt :
    _root_.UpperTheory.NonzeroTypeTheory.typeData_of_s_ty := by
  intro P a1 a3 a4 a5 a6 a7 gm ge gi cm cp gr E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  obtain ⟨μ, hμs, hμ⟩ := a1 E Ω A w h a ha n χ ho
  obtain ⟨G, σ, hG⟩ := gr (w.adicCompletion E) n μ hμs
  have hcond : ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π ↔ IsTwSphProd π.ρ G.d G.hd G.μ := by
    intro π
    have e := gMainV P.loc gi H G.d G.μ G.smooth (a6 gi E Ω A w h a ha n G)
      (IrrGL.of π.ρ π.smooth π.irred) G.hd
    rw [← a5 _ n π.V π.ρ π.smooth π.irred G.s G.d G.hd G.μ, ← e]
    unfold Cond
    refine and_congr_right fun _ => forall_congr' fun s => ?_
    rw [a3 E Ω A w h a ha n χ ho μ hμ G σ hG s]
  obtain ⟨hJK, h1J, hmul, hinv, hne, hKCo, h1KC, hKCJ, hlam1, hst, hfin, hv0m, hv00, hv0e⟩ := cp (w.adicCompletion E) n G
  have hK : KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := SphCompletion.KO_completion w n
  change ∃ (J : Subgroup ↥(GlobalTheory.LFun.KGL w (n := n))) (lam : ↥J →* ℂˣ) (m : ℕ)
      (V0 : Representation ℂ ↥(GlobalTheory.LFun.KGL w (n := n)) (Fin m → ℂ))
      (v0 : Fin m → ℂ), IsOpen (J : Set ↥(GlobalTheory.LFun.KGL w (n := n))) ∧
      IsOpen (lam.ker : Set ↥J) ∧ GlobalTheory.PRep.IsSmooth V0 ∧
      v0 ≠ 0 ∧ (∀ j : ↥J, V0 (j : ↥(GlobalTheory.LFun.KGL w (n := n))) v0 = ((lam j : ℂˣ) : ℂ) • v0) ∧
      (∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)),
        (∃ x : π.V, x ≠ 0 ∧ ∀ j : ↥J, π.ρ ((j : ↥(GlobalTheory.LFun.KGL w (n := n))) : GL (Fin n) (w.adicCompletion E)) x = ((lam j : ℂˣ) : ℂ) • x) →
          Cond h rc χ ho π) ∧
      ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π →
        ∃ f : (Fin m → ℂ) →ₗ[ℂ] π.V, Function.Injective f ∧ ∀ k v, f (V0 k v) = π.ρ k (f v)
  rw [← hK]
  let J : Subgroup ↥(KO (w.adicCompletion E) (Fin n)) :=
    { carrier := {j | (j : GL (Fin n) (w.adicCompletion E)) ∈ G.JSet}
      mul_mem' := fun {x y} hx hy => (hmul _ hx _ hy).1
      one_mem' := h1J
      inv_mem' := fun {x} hx => hinv _ hx }
  let lam : ↥J →* ℂˣ :=
    { toFun := fun j => Units.mk0 (G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E))) (hne _ j.2)
      map_one' := Units.ext (by simpa using hlam1 1 h1KC)
      map_mul' := fun x y => Units.ext (by simpa using (hmul _ x.2 _ y.2).2) }
  have hlamv : ∀ j : ↥J, ((lam j : ℂˣ) : ℂ) = G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E)) :=
    fun _ => rfl
  obtain ⟨m, V0, e, he, hre, heq, hsm⟩ := a4 _ G.V0sp hfin (fun φ hφ k' => hst φ hφ k') (a7 _ n G hKCo h1KC)
  obtain ⟨v0, hv0⟩ : G.v0 ∈ LinearMap.range e := hre ▸ hv0m
  have hU : IsOpen {j : ↥(KO (w.adicCompletion E) (Fin n)) | (j : GL (Fin n) (w.adicCompletion E)) ∈ KC _ n G.lev} :=
    hKCo.preimage continuous_subtype_val
  refine ⟨J, lam, m, V0, v0, ?_, ?_, hsm, fun h0 => hv00 (by rw [← hv0, h0, map_zero]), fun j => he ?_, ?_, ?_⟩
  · exact Subgroup.isOpen_of_mem_nhds J (Filter.mem_of_superset (hU.mem_nhds (show (1 : ↥(KO (w.adicCompletion E) (Fin n))) ∈ _ from h1KC)) fun j hj => hKCJ hj)
  · exact Subgroup.isOpen_of_mem_nhds lam.ker (Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds (show (1 : ↥J) ∈ _ from h1KC)) fun j hj => MonoidHom.mem_ker.2 (Units.ext (by
        rw [hlamv]; exact hlam1 _ hj)))
  · rw [heq, hv0, hv0e _ j.2, map_smul, hv0, hlamv]
  · rintro π ⟨x, hx, hxj⟩
    rw [hcond]
    refine cm P _ n G π.V π.ρ π.smooth π.irred ⟨x, hx, fun g hg => ?_⟩
    have := hxj ⟨⟨g, hJK hg⟩, hg⟩
    rwa [hlamv] at this
  · intro π hc
    rw [hcond] at hc
    obtain ⟨f, hf, hfeq⟩ := ge _ n G π.V π.ρ hc
    let e' : (Fin m → ℂ) →ₗ[ℂ] ↥G.V0sp := LinearMap.codRestrict G.V0sp e fun v => hre ▸ LinearMap.mem_range_self e v
    refine ⟨f ∘ₗ e', hf.comp fun v v' hvv => he (congrArg Subtype.val hvv), fun κ v => ?_⟩
    exact hfeq κ (e' v) (e' (V0 κ v)) (heq κ v)
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroKTop
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
theorem nz_of_typeData_alt (h2 : SmoothRepIrreducibleSubcontainingVector) (h3 : SmoothRepMinimalSubrepresentation) (h4 : SchurInjectiveFromIrreducible) (TD : _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt) : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes := by
  intro E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨J, lam, m, V0, v0, -, -, hsm, hv0, hvec, himp, hemb⟩ := TD E Ω A w h rc hrc n χ ho
  have : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) :=
    isCompact_iff_compactSpace.1 (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  obtain ⟨S, p, hS0, hSst, hSirr, hpS, hpid, hpeq, hpv⟩ := h2 _ m V0 hsm v0 hv0
  obtain ⟨d, ξ, ι, hι, hrange, hint, hirr, hsmξ⟩ := h3 _ m V0 hsm S hS0 hSst hSirr
  refine ⟨d, ξ, hirr, hsmξ, fun π => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg0, hg⟩
    have hgi : Function.Injective g := h4 _ d ξ hirr π.V (π.ρ.comp (GlobalTheory.LFun.KGL w (n := n)).subtype) g hg0 hg
    obtain ⟨z, hz⟩ : p v0 ∈ LinearMap.range ι := hrange ▸ hpS v0
    refine himp π ⟨g z, fun h0 => hpv ?_, fun j => ?_⟩
    · have : z = 0 := hgi (h0.trans (map_zero g).symm)
      rw [← hz, this, map_zero]
    · have hξz : ξ (j : ↥(GlobalTheory.LFun.KGL w (n := n))) z = ((lam j : ℂˣ) : ℂ) • z := hι (by
        rw [← hint, hz, ← hpeq, hvec j, map_smul, ← hz, map_smul])
      have := hg (j : ↥(GlobalTheory.LFun.KGL w (n := n))) z
      rw [hξz, map_smul] at this
      exact this.symm
  · intro hc
    obtain ⟨f, hf, hfeq⟩ := hemb π hc
    obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, z ≠ 0 := by
      by_contra hne
      push Not at hne
      have : S = ⊥ := by
        rw [← hrange, LinearMap.range_eq_bot]
        exact LinearMap.ext fun v => by rw [hne v, map_zero, LinearMap.zero_apply]
      exact hS0 this
    refine ⟨f ∘ₗ ι, fun h0 => hz (hι (hf ?_)), fun k v => ?_⟩
    · rw [map_zero, map_zero]
      exact LinearMap.congr_fun h0 z
    · simp only [LinearMap.comp_apply]
      rw [← hint, hfeq]
end UpperTheory.NonzeroTypeTheory
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
theorem nz_of_steps_alt (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (k2 : SmoothRepIrreducibleSubcontainingVector) (k3 : SmoothRepMinimalSubrepresentation) (k4 : SchurInjectiveFromIrreducible) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct)
    (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia) (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp)
    (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp) : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes :=
  _root_.UpperTheory.NonzeroTypeTheory.nz_of_typeData_alt k2 k3 k4 (_root_.UpperTheory.V.Z.Win.T2.typeData_alt P a1 a3 a4 a5 a6 a7 gm ge gi cm cp gr)
end UpperTheory.NonzeroTypeTheory
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSuppProd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpOrd
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spOrd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end UpperTheory.TNZ.Grp.P_spOrd
namespace UpperTheory.TNZ.Grp
open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem step_spOrd_alt : _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) := by
  intro hL V _ _ π hs hi c hc σ h
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hL.loc.zel k
  obtain ⟨hp1, e1⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i)))
    (fun i => hasFiniteLength_detRep1 (c (σ i)))
  obtain ⟨hp2, e2⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i))
    (fun i => hasFiniteLength_detRep1 (c i))
  have hcl : clsGL _ hp1 = clsGL _ hp2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))
  have h1 := h.trans (prin_sub_multi (fun i => c (σ i)))
  have h2 := clsGL_of_pos hp1 hs hi h1
  rw [hcl] at h2
  exact (isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)
end UpperTheory.TNZ.Grp
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpCount
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spCount
section Abstract
variable {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W]
end Abstract
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ}
variable (G : Grp k n)
end Local
end UpperTheory.TNZ.Grp.P_spCount
namespace UpperTheory.TNZ.Grp
open P_spCount
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open scoped Classical in
set_option maxHeartbeats 800000 in
theorem step_spCount_alt {n : ℕ} (G : Grp k n) : G.Step_spCount_alt := by
  intro hL c hc hres
  have hE : G.etaSp (jacU G.e (prinSeries c)) =
      eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta (jac G.e (parInd (points (Fin n)) (ρc c))) :=
    eS_jacU_eq G.e (parInd (points (Fin n)) (ρc c)) G.eta
  obtain ⟨N, b, hb⟩ := (hL.loc.geo k).1 (Fin n) (Fin G.s) (Fin n) (fun _ => Unit)
    (fun a => Fin (G.d a)) (points (Fin n)) G.e
  obtain ⟨S, hmono, h0, hN, hS⟩ := hb ℂ (ρc c) (isSmooth_ρc c hc)
  obtain ⟨fr⟩ : Nonempty (∀ t : Fin N, ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ (fun _ : Fin n => Unit) i) :=
    ⟨fun t => (b t).nonempty_rows.some⟩
  obtain ⟨gc⟩ : Nonempty (∀ t : Fin N, ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) :=
    ⟨fun t => (b t).nonempty_cols.some⟩
  have hr : ∀ t : Fin N, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (subQuot (S t.succ) (S t.castSucc))) ≤ Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a)))
        G.eta (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := by
    intro t
    have e : Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
        (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := hS t (fr t) (gc t)
    exact rank_eS_le_of_equiv _ _ e.some
  have hr1 : ∀ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) ≤
        ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := by
    intro t
    split_ifs with hP
    · refine (rank_eS_le (gc t) (cellRep G c (b t) (fr t) (gc t)) G.eta).trans
        ((rank_quotient_le _).trans (le_of_eq ?_))
      rw [Module.rank_self, Nat.cast_one]
    · refine (rank_eS_eq_zero _ _ _ ?_).trans_le zero_le
      intro F hF
      by_contra hne
      apply hP
      intro i a h
      by_contra hab
      apply G.dist a (G.bl i) hab
      refine MonoidHom.ext fun w => ?_
      have h1 := cell_char G c (b t) (fr t) (gc t) F hF hne i a h w
      have h2 : c i (unitIncl k w) = G.μ (G.bl i) (unitIncl k w) := DFunLike.congr_fun (hres i) w
      exact h1.symm.trans h2
  have hsum : ∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) ≤ 1 := by
    rw [← Finset.card_filter]
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    exact b.injective (good_unique G ht ht')
  have hrank : Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 := by
    calc _ ≤ ∑ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
          (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) :=
          rank_le_of_filtration _ _ S hmono h0 hN _ hr
      _ ≤ ∑ t : Fin N, ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := Finset.sum_le_sum fun t _ => hr1 t
      _ = ((∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) : ℕ) : Cardinal) := (Nat.cast_sum _ _).symm
      _ ≤ 1 := by exact_mod_cast hsum
  haveI : Module.Free ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) := Module.Free.of_divisionRing ℂ _
  have hfin : FiniteDimensional ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.one_lt_aleph0)
  have hfr : Module.finrank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 :=
    Module.finrank_le_of_rank_le (n := 1) (by rw [Nat.cast_one]; exact hrank)
  rw [hE]
  exact ⟨hfin, hfr⟩
end UpperTheory.TNZ.Grp
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpPiSub
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spPiSub
end UpperTheory.TNZ.Grp.P_spPiSub
namespace UpperTheory.TNZ.Grp
open P_spPiSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem step_spPiSub_alt {n : ℕ} (G : Grp k n) : G.Step_spPiSub_alt := by
  intro hOrd hL Y _ _ τ _ _ ν hν hc hI
  let χ : Fin G.s → kˣ →* ℂˣ := fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  have hsupp : ∀ a, HasSupport (G.twD τ a)
      (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) := by
    intro a
    have h1 := (hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)
    rw [Multiset.map_map] at h1
    convert h1 using 2
    · rfl
    · rename_i j _
      exact (IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm
  have hcOf : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hS := SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth)
    (fun a => (hsupp a).isIrreducible) hsupp hI
  have hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) =
      Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i) :=
    sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))
  obtain ⟨h, x, hx, -, -, e', he⟩ := hS
  rw [hsum] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx
  obtain rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _) := funext fun b => (hσ b).symm
  have hn : h = n := by simpa using Fintype.card_congr σ
  subst hn
  let φ := multiProdEquiv e' fun b =>
    (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm
  have hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b)) :=
    (he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans
      (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)
  exact hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq
end UpperTheory.TNZ.Grp
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpSupp
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)
end P_spSupp
open P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}
theorem step_spSupp_alt (G : Grp k n) : G.Step_spSupp_alt := by
  intro hOrd hLit V _ _ π hπs hπi Y _ _ τ hτs hτi ν hν hcs hjac
  have hG := hLit.loc.geo
  have hZ := hLit.loc.zel
  have hBZ := hLit.loc.bz
  have hs' : ∀ a, IsSmooth (G.twD τ a) := fun a =>
    isSmooth_twist (hτs a) (isSmoothChar_absPow _).detChar
  have hi' : ∀ a, (G.twD τ a).IsIrreducible := fun a => GlobalTheory.LocGL.isIrreducible_twist (hτi a) _
  have hτJ : (piTensor (G.twD τ)).IsIrreducible := isIrreducible_piTensor_twD G hBZ τ hs' hi'
  have hJs : IsSubquotient (piTensor (G.twD τ)) (jac G.e π) := by
    rw [piTensor_twD_eq]
    exact GlobalTheory.LocGL.isSubquotient_twist hjac _
  obtain ⟨s, hsπ⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ (IrrGL.of π hπs hπi)
  have hsπ' : HasSupport π s := hsπ.of_equiv (IrrGL.equivOf π hπs hπi).symm
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (G.d j)) k), IsSubquotient y.ρ
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j) :
        Representation ℂ (GL (Fin (G.d j)) k) _) ∧ Nonempty ((G.twD τ j).Equiv y.ρ) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτJ)
    have h1 : IsSubquotient υ (G.twD τ j) :=
      GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (G.twD τ) j hυ hυs
    exact ⟨⟨X, υ, h1.isSmooth (hs' j), hυ⟩, hυs,
      GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hυ (hi' j) h1⟩
  choose y hy hyE using hy
  obtain ⟨t, ht, hst⟩ := GlobalTheory.LocGL.SupportUnique.exists_sum_of_jac hG hZ hsπ' G.e hτJ hJs y hy
  have hsm : ∀ a j,
      IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    fun a j => (hν a j).mul (isSmoothChar_absPow _)
  have htj : ∀ j, t j = Finset.univ.val.map fun i => IrrGL.ofChar _ (hsm j i) := by
    intro j
    obtain ⟨φ⟩ := hyE j
    refine GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport hG hZ (G.d j)
      (IrrGL.of (G.twD τ j) (hs' j) (hi' j)) rfl _ _ ?_ ?_
    · exact ((ht j).of_equiv φ.symm).of_equiv (IrrGL.equivOf _ _ _)
    · exact (hasSupport_twD G τ ν hν hcs j (hsm j)).of_equiv (IrrGL.equivOf _ _ _)
  have hc : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hsF : s = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hc i) := by
    rw [hst, Finset.sum_congr rfl fun j _ => htj j]
    exact sum_map_univ G.e _ _ fun a j => IrrGL.ofChar_inj.2 (by
      unfold Grp.cOf
      rw [Equiv.symm_apply_apply])
  obtain ⟨h, x, hx, -, -, e, he⟩ := hsπ'
  rw [hsF] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x _ hx
  obtain rfl : x = fun a => IrrGL.ofChar (G.cOf ν (σ a)) (hc (σ a)) := funext hσ
  obtain rfl : h = n := by simpa using Fintype.card_congr σ
  let φ := multiProdEquiv e fun a =>
    (GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ a)) (hc (σ a)))).symm
  have h1 : IsSubquotient π (multiProd e fun a => detRep (Fin 1) (G.cOf ν (σ a))) :=
    he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have h2 := h1.trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e fun a => G.cOf ν (σ a))
  exact hOrd hLit V π hπs hπi (G.cOf ν) hc σ h2
end UpperTheory.TNZ.Grp
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpTop
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem step_spTop_alt (G : Grp k n) : G.Step_spTop_alt := by
  intro hLat hUniq hCount hLift hTw hRes hPiEta hOrd hPiSub hSupp hCusp hProd hTen L V _ _ π hπs hπi Y iY mY τ hτs hτi hτd hsub
  have hc : ∀ a, ∃ μ' : Fin (G.d a) → kˣ →* ℂˣ,
      (∀ j, IsSmoothChar (μ' j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ' j u = G.μ a u) ∧
        IsCuspSupport (τ a) (fun _ => 1) (fun j => detRep (Fin 1) (μ' j)) :=
    fun a => hCusp L.loc k (G.d a) (Y a) (τ a) (hτs a) (hτi a) (G.μ a) (G.smooth a) (hτd a)
  choose ν hν hνc using hc
  have hνs : ∀ a j, IsSmoothChar (ν a j) := fun a j => (hν a j).1
  have hνr : ∀ a j, res (ν a j) = res (G.μ a) := fun a j => P_spTop.res_eq (hν a j).2
  have htw := fun a => hTw Y τ a (hτs a) (hτi a) (hτd a)
  have hPi : (multiProd G.e (G.twD τ)).IsIrreducible :=
    hProd hCusp L.loc k G.s n G.d G.hd Y (G.twD τ) (fun a => (htw a).1) (fun a => (htw a).2.1) G.μ G.smooth
      (fun a => (htw a).2.2) (fun b c hbc => P_spTop.exists_unit_ne (G.dist b c hbc))
  have hπI := hSupp hOrd L V π hπs hπi Y τ hτs hτi ν hνs hνc hsub
  have hPI := hPiSub hOrd L Y τ hτs hτi ν hνs hνc hPi
  obtain ⟨hfd, hle⟩ := hCount L (G.cOf ν) (P_spTop.isSmoothChar_cOf G ν hνs) (hRes ν hνr)
  have hπη : G.HasEtaVec (jacU G.e π) := by
    obtain ⟨v, hv0, hv⟩ := hTen k G.s G.d Y τ G.μ hτd
    refine hLift _ _ (jacU G.e π) (piTensor τ) (isSmooth_jacU G.e hπs) hsub ⟨v, hv0, fun m hm => ?_⟩
    have hm' := hm
    rw [leviK, Subgroup.mem_pi] at hm'
    exact hv m fun a => hm' a (Set.mem_univ a)
  have hPη := hPiEta hLift Y τ hτs hτd
  obtain ⟨e⟩ := hUniq hLat _ (prinSeries (G.cOf ν)) (P_spTop.isSmooth_prinSeries _) hfd hle _ _ π
    (multiProd G.e (G.twD τ)) hπi hPi hπI hPI hπη hPη
  exact ⟨Y, iY, mY, G.twD τ, fun a => (htw a).1, fun a => (htw a).2.1, fun a => (htw a).2.2, ⟨e⟩⟩
end UpperTheory.TNZ.Grp
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TNZ.Grp
theorem step_suppProd_alt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.Step_suppProd_alt :=
  _root_.UpperTheory.TNZ.Grp.step_spTop_alt G UpperTheory.TNZ.step_spLat (step_spUniq G) (_root_.UpperTheory.TNZ.Grp.step_spCount_alt G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) _root_.UpperTheory.TNZ.Grp.step_spOrd_alt (_root_.UpperTheory.TNZ.Grp.step_spPiSub_alt G) (_root_.UpperTheory.TNZ.Grp.step_spSupp_alt G) _root_.UpperTheory.TNZ.step_cuspSupp_alt _root_.UpperTheory.TNZ.step_prodIrr_alt
    UpperTheory.TNZ.step_tensorVec
end UpperTheory.TNZ.Grp
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJTop
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCTop
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem cMain_alt (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k)) (hlL : LeviSubgroupRestriction) (hjI : G.JacquetImageProp) (hjP : G.Step_jacProd_alt) : G.CMainForAlt := by
  intro L V _ _ π hs hirr ⟨x, hx0, hx⟩
  refine hjP L V π hs hirr ⟨_, G.jac_ne_zero hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp
    hjK hTI hun π hs x hx0 hx, fun m hm => hjI hlL hJone V π x hx m hm⟩
end Grp
end UpperTheory.TNZ
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem jacProd_of_alt (hjF : G.Step_jacFin_alt) (hsub : G.SubquotientProp) (hten : G.Step_tensor_alt) (hsupp : G.Step_suppProd_alt) :
    G.Step_jacProd_alt := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩
end Grp
def CStepsAlt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.Step_jacFin_alt ∧ G.SubquotientProp ∧ G.Step_tensor_alt ∧ G.Step_suppProd_alt
open UpperTheory.NonzeroTypeTheory in
theorem twisted_spherical_product_of_irreducible_of_eigenvector (hC : _root_.UpperTheory.TNZ.CStepsAlt) (hlL : LeviSubgroupRestriction) (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain_alt hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of_alt hjF hsub hten hsupp) L V ρ hs hi hx
open UpperTheory.NonzeroTypeTheory in
theorem need_CProps_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem
open UpperTheory.NonzeroTypeTheory in
theorem need_Grp_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩
end UpperTheory.TNZ
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroGTop
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TNZ
theorem gMain_alt (h1 : DeterminantVectorProp) (h2 : UnramifiedTwistProp) (h3 : SumOverListProp) (h4a : IsotypicComponentProp)
    (h4b : ScalarOnInertiaProp) (h5 : SphericalOfUnramifiedProp) (h5' : SphericalUnramifiedProp) (h6 : TwistRestrictionProp) (h6' : UntwistRestrictionProp)
    (h7 : ProductRestrictionProp) (h8a : _root_.UpperTheory.TNZ.Step_cuspSupp_alt) (h8b : _root_.UpperTheory.TNZ.Step_prodIrr_alt) (h9 : ArtinInertiaProp) : _root_.UpperTheory.TNZ.GMainAlt := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL hLit s d η hη hdist x hd
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := h4a E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := h4b E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => h5 E Ω A w h a ha ε rc hL (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    choose hs' hi' hrc' using fun b => h6 E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (h1 _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (h9 E Ω A w h a ha).1 t, ht⟩
    have hI := h8b h8a hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' η hη hdet hdistU
    have hrcP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (hL.bij.1 heq).trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨hs', hi', hr⟩ := h6' E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
      exact ⟨_, h5' E Ω A w h a ha ε rc hL (d b) (Xs b) _ hs' hi' ((h1 _ (d b) (Xs b) (σ b) (η b)).2 (hdet b)),
        hL.dim _, hr⟩
    choose u hu hud hur using hfac
    have hl := h3 E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (h2 E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (h2 E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl
end UpperTheory.TNZ
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPJacFin
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
namespace JacquetFiniteLength₂
variable {n : ℕ} (G : Grp k n)
end JacquetFiniteLength₂
theorem step_jacFin_alt {n : ℕ} (G : Grp k n) : G.Step_jacFin_alt := by
  intro L V _ _ π hπ hirr
  exact ⟨isSmooth_jacU G.e hπ,
    JacquetFiniteLength₂.hasFiniteLength_jacU G L.loc.bz π hπ (hasFiniteLength_of_isIrreducible hirr)⟩
end Grp
end UpperTheory.TNZ
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPTensor
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct
open Module
namespace UpperTheory.TNZ.Grp.Tensor₂
section Contr
variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {Y : ι → Type} [∀ b, AddCommGroup (Y b)]
  [∀ b, Module ℂ (Y b)]
end Contr
end UpperTheory.TNZ.Grp.Tensor₂
namespace UpperTheory.TNZ.Grp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem step_tensor_alt {n : ℕ} (G : Grp k n) : G.Step_tensor_alt := by
  intro hN X _ _ σ hs hirr hη
  obtain ⟨y, hy0, hy⟩ := hη
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s)
    (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }
  refine ⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ,
    fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩
  have hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y) := fun m =>
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y
  have hEy : E y ≠ 0 := (map_ne_zero_iff E (EquivLike.injective E)).2 hy0
  have hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)),
      piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) =
        ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y := by
    intro g hg
    have hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈
        leviK k (m := fun b : Fin G.s => Fin (G.d b)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    rw [← hE, hy _ hm, map_smul]
    congr 1
    rw [eta, Finset.prod_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK
end UpperTheory.TNZ.Grp
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel UpperTheory.TNZ
namespace UpperTheory.NonzeroTypeTheory
theorem cSteps_all_alt
     :
    _root_.UpperTheory.TNZ.CStepsAlt := by
  intro k _ _ _ _
  exact ⟨Grp.step_ccBasic (k := k), Grp.step_unif (k := k), Grp.step_exGrp (k := k), fun n G => ⟨Grp.step_ccBound (G := G), Grp.step_Jone (G := G), Grp.step_Jmul (G := G), Grp.step_Jinv (G := G), Grp.step_KC (G := G), Grp.step_DUnit (G := G), Grp.step_DMul (G := G), Grp.step_lamMul (G := G), Grp.step_lamBasic (G := G), Grp.step_lamUnip (G := G), Grp.step_iwahori (G := G), Grp.step_V0stable (G := G), Grp.step_V0fin (G := G), Grp.leviEigenvector_holds (G := G), Grp.step_PJ (G := G), Grp.step_kill (G := G), Grp.step_nonint (G := G), Grp.step_TzE (G := G), Grp.step_Tpow (G := G), Grp.step_jacKer (G := G), Grp.step_TzInj (G := G), Grp.step_jacImage (G := G), _root_.UpperTheory.TNZ.Grp.step_jacFin_alt (G := G), Grp.step_subq (G := G), _root_.UpperTheory.TNZ.Grp.step_tensor_alt (G := G), _root_.UpperTheory.TNZ.Grp.step_suppProd_alt (G := G)⟩⟩
theorem nonzero_types_of_literal_automorphy (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis)
     : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes :=
  _root_.UpperTheory.NonzeroTypeTheory.nz_of_steps_alt P invariantComplement_holds minimalSubrepresentation_holds schurInjective_holds artinTransferDecomposition_holds localArtinCharacterProduct_holds finiteDimensionalTranslation_holds twistedSphericalRepresentative_holds distinctOnInertia_holds smoothVectorsFixed_holds
    (_root_.UpperTheory.TNZ.gMain_alt step_detVec step_unrTwist step_sumList step_isotypic step_scalarInertia step_sphOfUnr step_sphUnr step_twistRc
      step_untwistRc step_prodRc _root_.UpperTheory.TNZ.step_cuspSupp_alt _root_.UpperTheory.TNZ.step_prodIrr_alt step_artinIne)
    (gEmb step_tensorVec step_lamLevi step_parabKO step_indDetK step_indExt) step_artinIne
    (fun L => _root_.UpperTheory.TNZ.twisted_spherical_product_of_irreducible_of_eigenvector (_root_.UpperTheory.NonzeroTypeTheory.cSteps_all_alt ) step_lamLevi L) (_root_.UpperTheory.TNZ.need_CProps_alt (_root_.UpperTheory.NonzeroTypeTheory.cSteps_all_alt ))
    (_root_.UpperTheory.TNZ.need_Grp_alt (_root_.UpperTheory.NonzeroTypeTheory.cSteps_all_alt ))
end UpperTheory.NonzeroTypeTheory
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep' :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ :=
  fun P => _root_.UpperTheory.V.Z.Desc.P.exists_integral_type_for_residual_rep P (_root_.UpperTheory.NonzeroTypeTheory.nonzero_types_of_literal_automorphy P )
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end
