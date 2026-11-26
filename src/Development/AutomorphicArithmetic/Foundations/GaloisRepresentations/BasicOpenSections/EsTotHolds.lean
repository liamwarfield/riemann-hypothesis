module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.CorrOpEq
public import Development.EtaleCohomology.EtaleTrace.FrobTraceOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.CycAllHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.SpecCorrOfHolds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

theorem pullHQ_comp (l : ℕ) [Fact l.Prime] {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n i : ℤ) :
    pullHQ l (sch.map (f ≫ g)) n i = pullHQ l (sch.map f) n i ∘ₗ pullHQ l (sch.map g) n i := by
  rw [Functor.map_comp]
  simp only [pullHQ, pullHl_comp, LinearMap.baseChange_comp]

end UpperTheory.Gal.TranscendenceTraces

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCorrOpEq
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt)
open UpperTheory.Gal.crystallineComparison (PtId fn)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem isIso_reindex {W P : Scheme.{0}} {J : Type} {m : ℕ} (e : Fin m ≃ J) (f : J → (W ⟶ P))
    (h : IsIso (Sigma.desc f : ∐ (fun _ : J => W) ⟶ P)) :
    IsIso (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) := by
  have heq : (Sigma.desc (fun i => f (e i)) : ∐ (fun _ : Fin m => W) ⟶ P) =
      (Sigma.reindex e (fun _ : J => W)).hom ≫ Sigma.desc f := by
    ext i
    have h2 : Sigma.ι (fun _ : Fin m => W) i ≫ (Sigma.reindex e (fun _ : J => W)).hom =
        Sigma.ι (fun _ : J => W) (e i) := Sigma.ι_reindex_hom e (fun _ : J => W) i
    rw [← Category.assoc, h2]
    simp
  rw [heq]
  infer_instance

private theorem existsUnique_sec {U P : Scheme.{0}} (p' : P ⟶ U) {m : ℕ} (s' : Fin m → (U ⟶ P))
    (hs : ∀ j, s' j ≫ p' = 𝟙 U) (hiso : IsIso (Sigma.desc s' : ∐ (fun _ : Fin m => U) ⟶ P))
    {Ω : Type} [Field Ω] (x0 : gp Ω ⟶ U) (y : gp Ω ⟶ P) (hy : y ≫ p' = x0) :
    ∃! j, x0 ≫ s' j = y := by
  classical
  set D : ∐ (fun _ : Fin m => U) ⟶ P := Sigma.desc s' with hD
  have hι : ∀ j, Sigma.ι (fun _ : Fin m => U) j ≫ D = s' j := fun j => Sigma.ι_desc _ _
  have huniq : ∀ j₁ j₂, x0 ≫ s' j₁ = x0 ≫ s' j₂ → j₁ = j₂ := by
    intro j₁ j₂ h
    rw [← hι j₁, ← hι j₂, ← Category.assoc, ← Category.assoc, cancel_mono] at h
    have h2 := congrArg (fun f : gp Ω ⟶ ∐ (fun _ : Fin m => U) => f (IsLocalRing.closedPoint Ω)) h
    simp only [Scheme.Hom.comp_apply] at h2
    have h3 := (sigmaι_eq_iff (fun _ : Fin m => U) j₁ j₂ _ _).mp h2
    exact (Sigma.mk.inj_iff.mp h3).1
  obtain ⟨⟨j, u⟩, hju⟩ :=
    (sigmaMk (fun _ : Fin m => U)).surjective ((y ≫ inv D) (IsLocalRing.closedPoint Ω))
  rw [sigmaMk_mk] at hju
  have hrange : Set.range (y ≫ inv D).base ⊆ Set.range (Sigma.ι (fun _ : Fin m => U) j).base := by
    rintro _ ⟨z, rfl⟩
    refine ⟨u, ?_⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
    exact hju
  obtain ⟨t, ht⟩ : ∃ t, t ≫ Sigma.ι (fun _ : Fin m => U) j = y ≫ inv D :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hy2 : t ≫ s' j = y := by
    rw [← hι j, ← Category.assoc, ht, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have htx : t = x0 := by
    rw [← hy, ← hy2, Category.assoc, hs, Category.comp_id]
  have hy3 : x0 ≫ s' j = y := by
    rw [← htx]
    exact hy2
  exact ⟨j, hy3, fun j₁ hj₁ => huniq _ _ (hj₁.trans hy3.symm)⟩

private theorem push_one {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Surjective c] {G : Type} [Finite G]
    (a : G → (W ⟶ W)) (hs : Splits c c a) : (Wt.const W 1).push c = Wt.const S (Nat.card G : ℤ) := by
  classical
  obtain ⟨hac, hiso⟩ := hs
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ G) := ⟨Nat.card G, ⟨(Finite.equivFin G).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  funext Ω _ _ x
  show ∑ᶠ (z : gp Ω ⟶ W) (_ : z ∈ fib c x), (1 : ℤ) = (Nat.card G : ℤ)
  obtain ⟨v, hv⟩ := c.surjective (pt x)
  obtain ⟨z0, hz0, -⟩ := TranscendenceTraces.ptLift_holds c Ω x v hv
  have key := fun (y : gp Ω ⟶ pullback c c) (hy : y ≫ pullback.snd c c = z0) =>
    existsUnique_sec (pullback.snd c c)
      (fun j => pullback.lift (a (e j)) (𝟙 W) (by rw [hac, Category.id_comp]))
      (fun j => pullback.lift_snd _ _ _) hiso' z0 y hy
  have hlift : ∀ g : G, z0 ≫ pullback.lift (a g) (𝟙 W) (by rw [hac, Category.id_comp]) =
      pullback.lift (z0 ≫ a g) z0 (by rw [Category.assoc, hac]) := by
    intro g
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  have hfib : fib c x = Set.range (fun g : G => z0 ≫ a g) := by
    ext z
    constructor
    · intro hz
      have hzc : z ≫ c = z0 ≫ c := by
        rw [hz0]
        exact hz
      obtain ⟨j, hj, -⟩ := key (pullback.lift z z0 hzc) (pullback.lift_snd _ _ _)
      refine ⟨e j, ?_⟩
      have h1 := congrArg (· ≫ pullback.fst c c) hj
      simp only [Category.assoc, pullback.lift_fst] at h1
      exact h1
    · rintro ⟨g, rfl⟩
      show (z0 ≫ a g) ≫ c = x
      rw [Category.assoc, hac, hz0]
  have hinj : Function.Injective (fun g : G => z0 ≫ a g) := by
    intro g₁ g₂ h
    have h' : z0 ≫ a g₁ = z0 ≫ a g₂ := h
    obtain ⟨j, -, huniq⟩ := key (pullback.lift (z0 ≫ a g₁) z0 (by rw [Category.assoc, hac]))
      (pullback.lift_snd _ _ _)
    have e1 := huniq (e.symm g₁) (by
      simp only [Equiv.apply_symm_apply]
      exact hlift g₁)
    have e2 := huniq (e.symm g₂) (by
      simp only [Equiv.apply_symm_apply]
      rw [hlift g₂]
      congr 1
      exact h'.symm)
    exact e.symm.injective (e1.trans e2.symm)
  rw [hfib, finsum_mem_range hinj]
  haveI := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

private theorem pull_inj (l : ℕ) [Fact l.Prime] {W S : Scheme.{0}} (c : W ⟶ S) [IsFinite c] [Etale c] [Surjective c]
    {G : Type} [Finite G] [Nonempty G] (a : G → (W ⟶ W)) (hs : Splits c c a) (hl : IsUnit (l : Γ(S, ⊤))) (k : ℤ) :
    Function.Injective (pullHQ l (sch.map c) k 0) := by
  have wt : IsWt c (Wt.const W 1) := by
    rw [← UpperTheory.Gal.TranscendenceTraces.multBasic_holds.2.2 c]
    exact UpperTheory.Gal.TranscendenceTraces.wtFlat_holds c
  have hd := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.1 l k 0 c (Wt.const W 1) (Nat.card G : ℤ) wt hl (push_one c a hs)
  have hne : (((Nat.card G : ℤ) : ℤ) : ℚ_[l]) ≠ 0 := by
    have : (Nat.card G : ℤ) ≠ 0 := by
      exact_mod_cast Nat.card_pos.ne'
    exact_mod_cast this
  intro x y hxy
  have h1 := LinearMap.congr_fun hd x
  have h2 := LinearMap.congr_fun hd y
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 h2
  rw [hxy, h2] at h1
  exact (smul_right_injective _ hne h1).symm

theorem UpperTheory.Gal.Mod.corrOpEq :
    CorrOpEq := by
  intro l _ S c _ hw hl T hT
  obtain ⟨W, c', G, _, _, a, J, _, σ, hgal, hsplit, hTx⟩ := hT
  obtain ⟨hfin, het, hsurj, -, -, hsc⟩ := hgal
  haveI := hfin
  haveI := het
  haveI := hsurj
  haveI : IsFinite c.p := c.fin
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨hσ, hiso⟩ := hsplit
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (Fin m ≃ J) := ⟨Fintype.card J, ⟨(Fintype.equivFin J).symm⟩⟩
  have hiso' := isIso_reindex e _ hiso
  have hsplitQ : ∀ k : ℤ, pullHQ l (sch.map c') k 0 ∘ₗ TranscendenceTraces.trHQ l c.p (Wt.const c.Z 1) k 0 =
      ∑ j : Fin m, pullHQ l (sch.map (σ (e j))) k 0 := fun k =>
    TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l k 0 c.p hl W c' m (fun j => σ (e j)) (fun j => hσ (e j)) hiso'
  have hinj : Function.Injective (pullTot l (sch.map c')) := by
    intro x y hxy
    refine DFinsupp.ext fun k => ?_
    have h := congrArg (fun z => z k) hxy
    simp only [pullTot, DirectSum.lmap_apply] at h
    exact pull_inj l c' a hsc hl k h
  apply LinearMap.ext
  intro x
  apply hinj
  rw [hTx x]
  refine DFinsupp.ext fun k => ?_
  have h1 := LinearMap.congr_fun (hsplitQ k) (pullHQ l (sch.map c.f) k 0 (x k))
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h1
  erw [DirectSum.sum_apply]
  simp only [pullTot, DirectSum.lmap_apply, TranscendenceTraces.Corr.opQ, hw, LinearMap.comp_apply, h1,
    TranscendenceTraces.pullHQ_comp]
  exact (e.sum_comp (fun j => pullHQ l (sch.map (σ j)) k 0 (pullHQ l (sch.map c.f) k 0 (x k)))).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFrobQ
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.frobQ :
    FrobTors → FrobQ := by
  intro hT l _ X p f hp h hl k
  have key : pullHl l (sch.map (absFrob X p f hp h)) k 0 = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun j => ?_)
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hu : IsUnit (((l ^ j : ℕ)) : Γ(X, ⊤)) := by
      rw [Nat.cast_pow]; exact hl.pow j
    exact hT (l ^ j) X p f hp h hu k (x.1 j)
  unfold pullHQ
  rw [key]
  exact LinearMap.baseChange_id
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PEsGen
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem pullHQ_comp_apply (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (a : E ⟶ E') (b : E' ⟶ E'') (n i : ℤ)
    (x : HQ l E'' n i) : pullHQ l (a ≫ b) n i x = pullHQ l a n i (pullHQ l b n i x) := by
  unfold pullHQ
  rw [pullHl_comp, LinearMap.baseChange_comp]
  rfl

private theorem galHQ_eq_pullHQ_galMap (l : ℕ) [Fact l.Prime] {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]
    {X : Scheme} (t : X ⟶ Spec (CommRingCat.of k)) (n i : ℤ) (σ : Gal(Ω/k)) (x : HQ l (sch.obj (geom Ω t)) n i) :
    galHQ l Ω t n i σ x = pullHQ l (sch.map (galMap Ω t σ)) n i x := rfl

private theorem pullHQ_surjective_of_forall_pull_bijective (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (h : ∀ k : ℕ, Function.Bijective (GlobalTheory.EtC.pull (ZMod (l ^ k)) f (tw (l ^ k) i) n)) :
    Function.Surjective (pullHQ l f n i) := by
  have hs : Function.Surjective (pullHl l f n i) := by
    intro y
    let x : (k : ℕ) → HtL l k E' n i := fun k => (Equiv.ofBijective _ (h k)).symm (y.1 k)
    have hx : ∀ k, GlobalTheory.EtC.pull (ZMod (l ^ k)) f (tw (l ^ k) i) n (x k) = y.1 k := fun k =>
      Equiv.ofBijective_apply_symm_apply _ (h k) (y.1 k)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · intro k
      apply (h k).1
      rw [pull_red, hx, hx]
      exact y.2 k
    · apply Subtype.ext
      funext k
      exact hx k
  unfold pullHQ
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ hs

theorem UpperTheory.Gal.Mod.esGen :
    SpecGood → ESPt → NwtOne → FrobQ → BaseFacts → DenseGen → FrEx → CorrPull → CorrComm → ESGen := by
  intro hSG hES hNwt hFQ hBF hDG hFrEx hCP hCC
  intro l _ p f n hp O _ _ _ ϖ hϖ hpu K _ _ κ _ _ hp0 hκ hfin Ω _ _ _ V hV kb _ _ _ r hr hrc hl Y g _ _ T hT hPt c hc σ hσ k
  let ρ : O →+* V := ((algebraMap K Ω).comp (algebraMap O K)).codRestrict V hV
  have hρ : CommRingCat.ofHom (algebraMap O κ) ≫ CommRingCat.ofHom (algebraMap κ kb) =
      CommRingCat.ofHom ρ ≫ CommRingCat.ofHom r := by
    ext a
    exact (hrc a).symm
  have hρK : CommRingCat.ofHom (algebraMap O K) ≫ CommRingCat.ofHom (algebraMap K Ω) =
      CommRingCat.ofHom ρ ≫ CommRingCat.ofHom V.subtype := by
    ext a
    rfl
  let iY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom r)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρ])
  let jY : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom ρ)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom V.subtype)) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hρK])
  have HSG := @hSG O _ K _ _ κ _ _ Ω _ _ _ V hV kb _ _ _ r hr hrc Y g _ _ iY jY
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨sp, hsp1, hsp2⟩ := HSG.2 l hl k 0
  have hpO : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hpκ : (p : κ) = 0 := by
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hpO
    rw [← map_natCast (algebraMap O κ), ← hu, map_mul, hκ, mul_zero]
  have hpkb : (p : kb) = 0 := by
    rw [← map_natCast (algebraMap κ kb), hpκ, map_zero]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP kb p := (CharP.charP_iff_prime_eq_zero hp).2 hpkb
  let τ : Gal(kb/κ) := AlgEquiv.ofRingEquiv (f := iterateFrobeniusEquiv kb p f) (fun a => by
    show iterateFrobenius kb p f _ = _
    rw [iterateFrobenius_def, ← map_pow, hfin])
  have hτ : ∀ a, τ a = a ^ p ^ f := fun a => iterateFrobeniusEquiv_apply kb p f a
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := sp.surjective x
    have e := hsp2 σ 1 hσ (fun v => by rw [h1 v]; rfl) y
    rw [map_one] at e
    exact e.symm
  · have hcomp : ∀ x, sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) =
        galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ (sp x) :=
      hsp2 σ τ hσ (fun v => by rw [h2 v, hτ])
    let φG : kb →+* Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤) :=
      (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom
    have hpG : ((p : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)) = 0 := by
      rw [← map_natCast φG p, hpkb, map_zero]
    have hlG : IsUnit ((l : ℕ) : Γ(geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))), ⊤)) := by
      rw [← map_natCast φG l]
      exact hl.map φG
    obtain ⟨Fr, hFr1, hFr2, hFr3⟩ := hFrEx p f hp κ kb hfin _
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) hpG τ hτ
    have hAF := hFQ l (geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))) p f hp hpG hlG k
    have hFG : ∀ x, pullHQ l (sch.map Fr) k 0
        (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ x) = x := by
      intro x
      rw [galHQ_eq_pullHQ_galMap, ← pullHQ_comp_apply, ← Functor.map_comp, hFr2, hAF]
      rfl
    have hinvτ : ∀ x, galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ
        (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) = x := by
      intro x
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have hsemi : ∀ x, sp (pullHQ l (sch.map Fr) k 0 x) =
        galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x) := by
      intro x
      calc sp (pullHQ l (sch.map Fr) k 0 x)
          = sp (pullHQ l (sch.map Fr) k 0
              (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ
                (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x))) := by
            rw [hinvτ]
        _ = sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x) := by
            rw [hFG]
        _ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹
              (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ
                (sp (galHQ l kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) k 0 τ⁻¹ x))) := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
            rfl
        _ = galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ (sp x) := by
            rw [← hcomp, hinvτ]
    have hpO0 : (p : O) ≠ 0 := by
      intro h0
      apply hp0
      rw [← map_natCast (algebraMap O K), h0, map_zero]
    obtain ⟨hLoc, hGen, hSpe, hBO⟩ := hBF p O ϖ hϖ hpO0 hpu Y g
    have hOne : ∀ j, Mod.One (T j) (nwt (T j).p) := fun j => hNwt p Y (T j) hLoc hGen
    have hβ : Spec.map (CommRingCat.ofHom (algebraMap κ kb)) ≫ Spec.map (CommRingCat.ofHom (algebraMap O κ)) =
        Spec.map (CommRingCat.ofHom ((algebraMap κ kb).comp (algebraMap O κ))) := by
      rw [← Spec.map_comp]
      rfl
    have hPBS : IsPullback
        (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
        (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
        g (Mod.sp ((algebraMap κ kb).comp (algebraMap O κ))) := by
      have e := IsPullback.paste_horiz (IsPullback.of_hasPullback
        (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
        (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
      rw [hβ] at e
      exact e
    have hDense := hDG O ϖ hϖ kb ((algebraMap κ kb).comp (algebraMap O κ)) (by simp [hκ]) Y _ g _ _ hPBS
    have hSep : ∀ (Ω' : Type) [Field Ω'] (x x' : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))),
        x ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) =
        x' ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) →
        x ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) =
        x' ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) → x = x' := by
      intro Ω' _ x x' e1 e2
      apply pullback.hom_ext _ e2
      apply pullback.hom_ext
      · simpa only [Category.assoc] using e1
      · simp only [Category.assoc, pullback.condition]
        rw [← Category.assoc, e2, Category.assoc]
    have hTw : ∀ (Ω' : Type) [Field Ω'] (φ : Ω' →+* Ω'), (∀ a, φ a = a ^ p ^ f) →
        ∀ (x : gp Ω' ⟶ geom kb (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))),
        x ≫ Fr ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) =
        twist φ Y (x ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
          (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))) := by
      intro Ω' _ φ hφ x
      have e := hFr3 Ω' φ hφ x
      calc _ = (x ≫ Fr ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O κ))))
              (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap O κ))) := by
            simp only [Category.assoc]
        _ = _ := by
            rw [e]
            simp only [Category.assoc]
            rfl
    have hc' := fun j => hCP p g _ _ _ hPBS (T j) (nwt (T j).p) (hOne j).1 (hT j)
    choose c' hc'' using hc'
    choose v hv using hc''
    have hE := hES l p f n hp Y (fn g ϖ) T (fun j => nwt (T j).p) hOne hPt hSpe hBO _ _ _ _ Fr hlG hDense hSep hFr1 hTw c' v
      (fun j => (hv j).1) (fun j => (hv j).2.1) (fun j => (hv j).2.2.1) (fun j => (hv j).2.2.2) k 0
    have hPBV := IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom ρ))
    have hcV := fun j => hCP p g _ _ _ hPBV (T j) (nwt (T j).p) (hOne j).1 (hT j)
    choose cV hcV' using hcV
    have hlVV : IsUnit ((l : ℕ) : V) := by
      by_contra h
      have hm : ((l : ℕ) : V) ∈ IsLocalRing.maximalIdeal V := h
      have hk : RingHom.ker r = IsLocalRing.maximalIdeal V :=
        IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)
      rw [← hk, RingHom.mem_ker, map_natCast] at hm
      exact hl.ne_zero hm
    let φV : V →+* Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤) :=
      (pullback.snd g (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    have hlV : IsUnit ((l : ℕ) : Γ(pullback g (Spec.map (CommRingCat.ofHom ρ)), ⊤)) := by
      rw [← map_natCast φV l]
      exact hlVV.map φV
    have CCi := fun j => hCC l p g _ _ _ hPBV iY _ (Spec.map (CommRingCat.ofHom r)) (pullback.lift_snd _ _ _) hlV
      (T j) (nwt (T j).p) (cV j) (c' j) (hcV' j) (by rw [pullback.lift_fst]; exact ⟨v j, hv j⟩) k 0
    have hcN : ∀ j, IsBC (T j) (nwt (T j).p) (jY ≫ pullback.fst g (Spec.map (CommRingCat.ofHom ρ)))
        (pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) (c j) := by
      intro j
      obtain ⟨vK, e1, e2, e3, e4⟩ := hc j
      refine ⟨vK, ?_, ?_, e3, ?_⟩
      · rw [pullback.lift_fst]
        exact e1
      · rw [pullback.lift_fst]
        exact e2
      · rw [e4]
        funext Ω' i1 i2 z
        symm
        apply (hOne j).2 Ω' (z ≫ vK)
        intro h0
        let φ := Spec.preimage (z ≫ (c j).p ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K))))
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))
        have h1 : φ.hom (p : Ω) = 0 := by
          rw [map_natCast]
          exact h0
        have h2 : (p : Ω) = 0 := φ.hom.injective (by rw [h1, map_zero])
        apply hp0
        apply (algebraMap K Ω).injective
        rw [map_natCast, h2, map_zero]
    have CCj := fun j => hCC l p g _ _ _ hPBV jY _ (Spec.map (CommRingCat.ofHom V.subtype)) (pullback.lift_snd _ _ _) hlV
      (T j) (nwt (T j).p) (cV j) (c j) (hcV' j) (hcN j) k 0
    have hunit : ∀ m : ℕ, IsUnit (((l ^ m : ℕ)) : kb) := fun m => by
      rw [Nat.cast_pow]
      exact hl.pow m
    have hPs := pullHQ_surjective_of_forall_pull_bijective l (sch.map iY) k 0 (fun m => (HSG.1 (l ^ m) (hunit m) 0).1 k)
    have hopc : ∀ j x, TranscendenceTraces.Corr.opQ l (c j) k 0 (sp x) = sp (TranscendenceTraces.Corr.opQ l (c' j) k 0 x) := by
      intro j x
      obtain ⟨y, rfl⟩ := hPs x
      have e1 := LinearMap.congr_fun (CCi j) y
      have e2 := LinearMap.congr_fun (CCj j) y
      simp only [LinearMap.comp_apply] at e1 e2
      rw [hsp1, ← e2, ← hsp1, e1]
    have hpow : ∀ (m : ℕ) y, (galHQ l Ω (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap O K)))) k 0 σ⁻¹ ^ m) (sp y) =
        sp ((pullHQ l (sch.map Fr) k 0 ^ m) y) := by
      intro m
      induction m with
      | zero => intro y; rfl
      | succ m ih =>
        intro y
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← hsemi, ih]
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := sp.surjective x
    have hE' := LinearMap.congr_fun hE y
    rw [LinearMap.zero_apply] at hE' ⊢
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at hE' ⊢
    simp only [hpow, hopc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_zero sp, ← hE', map_sum]
    simp only [map_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.FrEx
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.frEx :
    FrEx := by
  intro p f hp κ kb _ _ _ hκ X t h τ hτ
  have K : absFrob (geom kb t) p f hp h ≫ pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (τ : kb →+* kb)) := by
    by_cases hk : (p : kb) = 0
    · have hk' : (p : Γ(Spec (CommRingCat.of kb), ⊤)) = 0 := by
        rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom p]
        erw [hk]
        exact map_zero _
      rw [GlobalTheory.SS.FrobField.absFrob_nat _ p f hp h hk']
      congr 1
      exact GlobalTheory.SS.FrobField.absFrob_spec kb p f hp hk' (τ : kb →+* kb) hτ
    · haveI : IsEmpty (geom kb t) := by
        refine ⟨fun x => hk ?_⟩
        have hinj := (((geom kb t).presheaf.germ ⊤ x trivial).hom.comp
          ((pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom)).injective
        apply hinj
        rw [map_zero]
        simp only [RingHom.comp_apply]
        rw [map_natCast, map_natCast, h, map_zero]
      exact isInitialOfIsEmpty.hom_ext _ _
  have hc : (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ t =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (algebraMap κ kb)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, K, Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    simp
  refine ⟨pullback.lift (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
    (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) hc, pullback.lift_snd _ _ _, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, galMap_fst, pullback.lift_fst]
    · rw [Category.assoc, galMap_snd, ← Category.assoc, pullback.lift_snd, K]
  · intro Ω _ φ hφ x
    have hΩ := GlobalTheory.SS.FrobField.cast_zero_of_hom x h
    have e := GlobalTheory.SS.FrobField.absFrob_nat x p f hp hΩ h
    have e2 : absFrob (gp Ω) p f hp hΩ = Mod.sp φ := GlobalTheory.SS.FrobField.absFrob_spec Ω p f hp hΩ φ hφ
    rw [pullback.lift_fst, ← Category.assoc, ← e, e2, Category.assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PBaseFacts
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem nml_spec (O : Type) [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    (y : Spec (CommRingCat.of O)) :
    IsDomain ((Spec (CommRingCat.of O)).presheaf.stalk y) ∧
      IsIntegrallyClosed ((Spec (CommRingCat.of O)).presheaf.stalk y) := by
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  letI : Algebra O ((Spec (CommRingCat.of O)).presheaf.stalk y) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of O) y
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of O)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of O) y
  exact GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain y.asIdeal _

private theorem natCast_eq_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (p : ℕ) :
    (p : Γ(Y, ⊤)) = fn g (p : O) := by
  simp [fn]

private theorem mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (a : O)
    (y : Y) : y ∈ Y.basicOpen (fn g a) ↔ g y ∈ PrimeSpectrum.basicOpen a := by
  rw [fn, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

private theorem exists_generic {O : Type} [CommRing O] [IsDomain O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O))
    [Flat g] (a : O) (ha : a ≠ 0) (y : Y) : ∃ η ∈ Y.basicOpen (fn g a), η ⤳ y := by
  let s : Spec (CommRingCat.of O) := ⟨⊥, Ideal.isPrime_bot⟩
  have hs : s ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨η, hη, rfl'⟩ := (Flat.generalizingMap g) hs
  refine ⟨η, ?_, hη⟩
  rw [mem_basicOpen_fn, rfl']
  exact ha

theorem UpperTheory.Gal.Mod.baseFacts :
    BaseFacts := by
  intro p O _ _ _ ϖ hϖ hp0 hpu Y g _
  haveI : Flat g := inferInstance
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have hbo : Y.basicOpen (p : Γ(Y, ⊤)) = Y.basicOpen (fn g (p : O)) := by
    rw [natCast_eq_fn g p]
  have hϖp : ϖ ∣ (p : O) := by
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
    cases n with
    | zero => exact absurd (hn.isUnit_iff.mpr (by simp)) hpu
    | succ n => exact (dvd_pow_self ϖ (Nat.succ_ne_zero n)).trans hn.symm.dvd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact TranscendenceTraces.nmlLoc_holds Y
      (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g (nml_spec O)) (Or.inr inferInstance)
  · intro y hy
    obtain ⟨η, hη, hηy⟩ := exists_generic g (p : O) hp0 y
    rw [hbo, ← hy η hηy]
    exact hη
  · intro y
    obtain ⟨η, hη, hηy⟩ := exists_generic g (p : O) hp0 y
    exact ⟨η, hbo ▸ hη, hηy⟩
  · intro y hy
    rw [hbo, mem_basicOpen_fn] at hy
    rw [mem_basicOpen_fn]
    change (p : O) ∉ (g y).asIdeal at hy
    change ϖ ∉ (g y).asIdeal
    intro h
    obtain ⟨c, hc⟩ := hϖp
    exact hy (hc ▸ Ideal.mul_mem_right c _ h)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFrobTors
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

namespace UpperTheory.Gal.Mod.FrobeniusTorsors

open UpperTheory.Gal.TranscendenceTraces GlobalTheory.SS.FrobField

private theorem prim_pow {m : ℕ} {A : Type} [CommRing A] (ζ : Prim m A) : ζ.1 ^ m = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

private theorem prim_ex (m : ℕ) [NeZero m] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hm : IsUnit (m : Ω)) :
    Nonempty (Prim m Γ(gp Ω, ⊤)) := by
  haveI : NeZero (m : Ω) := ⟨hm.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  refine ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ⟨ζ, hm, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ.isRoot_cyclotomic (NeZero.pos m)

private theorem tw_sub (m : ℕ) [NeZero m] (hm : m = 1) (i : ℤ) {U : Scheme.{0}} (a b : Sec (tw m i) U) : a = b := by
  subst hm
  have e : (1 : ULift.{1} (ZMod 1)) = 0 := Subsingleton.elim _ _
  rw [← one_smul (ULift.{1} (ZMod 1)) a, ← one_smul (ULift.{1} (ZMod 1)) b, e, zero_smul, zero_smul]

private theorem frob_top (Ω : Type) [Field Ω] (p f : ℕ) (hp : p.Prime) (h : (p : Γ(gp Ω, ⊤)) = 0) (c : Γ(gp Ω, ⊤)) :
    (absFrob (gp Ω) p f hp h).appTop.hom c = c ^ p ^ f := rfl

private theorem frob_pt (m : ℕ) [NeZero m] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p f : ℕ) (hp : p.Prime)
    (h : (p : Γ(gp Ω, ⊤)) = 0) (hm : IsUnit (m : Ω)) (y : Sec (tw m 0) (gp Ω)) :
    Sec.res (absFrob (gp Ω) p f hp h) y = y := by
  obtain ⟨ζ⟩ := prim_ex m Ω hm
  obtain ⟨φ, -, hφ⟩ := secFun_holds m 0 (gp Ω) ζ y
  have hI := GlobalTheory.T.tateTwist_sections_locally_generated m 0
  have key : Sec.res (absFrob (gp Ω) p f hp h) (twGen 0 ζ) = twGen 0 ζ := by
    rw [hI.2.2.2.1]
    by_cases h1 : m = 1
    · exact tw_sub m h1 0 _ _
    · have hpΩ : (p : Ω) = 0 := by
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom h
        rw [map_natCast, map_zero] at this
        exact this
      have hcop : Nat.Coprime (p ^ f) m := by
        refine Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_)
        rintro ⟨k, hk⟩
        apply hm.ne_zero
        rw [hk, Nat.cast_mul, hpΩ, zero_mul]
      haveI : Fact (1 < m) := ⟨by
        have := NeZero.ne m
        omega⟩
      rw [hI.2.2.2.2.1 (gp Ω) ζ _ (ZMod.unitOfCoprime (p ^ f) hcop)]
      · rw [zpow_zero, Units.val_one, ZMod.val_one, one_smul]
      · show (absFrob (gp Ω) p f hp h).appTop.hom ζ.1 = ζ.1 ^ ((ZMod.unitOfCoprime (p ^ f) hcop : ZMod m)).val
        rw [frob_top, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
        conv_lhs => rw [← Nat.mod_add_div (p ^ f) m]
        rw [pow_add, pow_mul, prim_pow ζ, one_pow, mul_one]
  apply ptInj_holds m 0
  intro Ω' _ _ x
  rw [res_res, hφ Ω' _, hφ Ω' x, ← res_res, key, Subsingleton.elim (pt (x ≫ absFrob (gp Ω) p f hp h)) (pt x)]

private theorem frob_sec (m : ℕ) [NeZero m] (U : Scheme.{0}) (p f : ℕ) (hp : p.Prime) (h : (p : Γ(U, ⊤)) = 0)
    (hm : IsUnit (m : Γ(U, ⊤))) (a : Sec (tw m 0) U) : Sec.res (absFrob U p f hp h) a = a := by
  refine ptInj_holds m 0 U _ _ fun Ω _ _ x => ?_
  have hΩ : (p : Γ(gp Ω, ⊤)) = 0 := cast_zero_of_hom x h
  have hmΩ : IsUnit (m : Ω) := by
    have h1 := (hm.map x.appTop.hom).map (Scheme.ΓSpecIso (.of Ω)).hom.hom
    simpa using h1
  rw [res_res, ← absFrob_nat x p f hp hΩ h, ← res_res]
  exact frob_pt m Ω p f hp hΩ hmΩ _

variable {X : Scheme.{0}}

private noncomputable def sc (A : Sq (𝟙 X)) : A.U ⟶ A.V :=
  A.pb.lift A.u (𝟙 _) (by simp)

private theorem sc_v (A : Sq (𝟙 X)) : sc A ≫ A.v = A.u := A.pb.lift_fst _ _ _

private theorem sc_r (A : Sq (𝟙 X)) : sc A ≫ A.r = 𝟙 _ := A.pb.lift_snd _ _ _

private theorem r_sc (A : Sq (𝟙 X)) : A.r ≫ sc A = 𝟙 _ := by
  refine A.pb.hom_ext ?_ ?_
  · rw [Category.assoc, sc_v, Category.id_comp, ← A.pb.w, Category.comp_id]
  · rw [Category.assoc, sc_r, Category.comp_id, Category.id_comp]

private theorem sc_nat {A B : Sq (𝟙 X)} (t : A.To B) : sc A ≫ t.k = t.g ≫ sc B := by
  refine B.pb.hom_ext ?_ ?_
  · rw [Category.assoc, t.hv, sc_v, Category.assoc, sc_v, t.hu]
  · rw [Category.assoc, t.hr, ← Category.assoc, sc_r, Category.id_comp, Category.assoc, sc_r, Category.comp_id]

private noncomputable def fk (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (A : Sq (𝟙 X)) : A.U ⟶ A.V :=
  absFrob A.U p f hp (cast_zero_of_hom A.u h) ≫ sc A

private theorem fk_nat (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {A B : Sq (𝟙 X)} (t : A.To B) :
    t.g ≫ fk p f hp h B = fk p f hp h A ≫ t.k := by
  unfold fk
  rw [← Category.assoc, ← absFrob_nat t.g p f hp (cast_zero_of_hom A.u h) (cast_zero_of_hom B.u h), Category.assoc,
    ← sc_nat, Category.assoc]

private noncomputable def fam0 (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (F : GlobalTheory.EtC.Shv R) :
    Fam0 (𝟙 X) F F where
  app A := (F.obj.map (fk p f hp h A).op).hom.toAddMonoidHom
  nat {A B} t a := (res_res t.g (fk p f hp h B) a).trans
    ((congrArg (fun e => Sec.res e a) (fk_nat p f hp h t)).trans (res_res (fk p f hp h A) t.k a).symm)

private noncomputable def fam (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (I : Cx R) :
    Fam (𝟙 X) I I where
  deg s := fam0 p f hp h (I.X s)
  comm A s t a := (map_res (I.d s t) (fk p f hp h A) a)

private theorem fk_self (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) :
    fk p f hp h (Sq.self (𝟙 X)) = absFrob X p f hp h := by
  unfold fk
  have h1 : sc (Sq.self (𝟙 X)) = 𝟙 _ := (Category.comp_id (sc (Sq.self (𝟙 X)))).symm.trans (sc_r (Sq.self (𝟙 X)))
  rw [h1]
  exact Category.comp_id _

private theorem fam_app (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (I : Cx R) (s : ℤ)
    (A : Sq (𝟙 X)) (a : Sec (I.X s) A.V) : ((fam p f hp h I).deg s).app A a = Sec.res (fk p f hp h A) a := rfl

private theorem fam_sums (m : ℕ) [NeZero m] (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (hm : IsUnit (m : Γ(X, ⊤))) :
    (fam p f hp h (res _ (tw m 0))).Sums (Wt.const X 1) := by
  intro A a
  have hmU : IsUnit (m : Γ(A.U, ⊤)) := by simpa using hm.map A.u.appTop.hom
  refine ⟨Sec.res (sc A) a, ?_, fun Ω _ _ x => ?_⟩
  · rw [fam_app, ← map_res]
    refine congrArg (Sec.map (resι _ _)) ?_
    unfold fk
    rw [← res_res]
    exact frob_sec m A.U p f hp _ hmU _
  · have hf : fib A.r x = {x ≫ sc A} := by
      ext z
      constructor
      · intro hz
        have hz' : z ≫ A.r = x := hz
        rw [Set.mem_singleton_iff, ← hz', Category.assoc, r_sc, Category.comp_id]
      · rintro rfl
        change (x ≫ sc A) ≫ A.r = x
        rw [Category.assoc, sc_r, Category.comp_id]
    rw [hf, finsum_mem_singleton, res_res]
    exact (one_smul ℤ _).symm

end UpperTheory.Gal.Mod.FrobeniusTorsors

open UpperTheory.Gal.Mod.FrobeniusTorsors in
theorem UpperTheory.Gal.Mod.frobTors :
    FrobTors := by
  intro m _ X p f hp h hm k x
  have e1 := (TranscendenceTraces.trChar_holds m 0 (𝟙 X) (Wt.const X 1) (TranscendenceTraces.wtLin_holds.2.2 (𝟙 X) 1) hm).2.2 _
    (fam_sums m p f hp h hm) k
  have e2 := (TranscendenceTraces.trLin_holds m k 0).2.2 X 1 hm x
  rw [e1, one_smul] at e2
  obtain ⟨a, ha⟩ := (TranscendenceTraces.rpBasic_of _ (res _ (tw m 0)) X k).1 x
  have h1 := (TranscendenceTraces.rpBasic_of _ (res _ (tw m 0)) X k).2.2.2.1 X (absFrob X p f hp h) x a ha
  have h2 := (TranscendenceTraces.rpOp_of TranscendenceTraces.imgBasic_of) _ _ (fam p f hp h (res _ (tw m 0))) k x a ha
  rw [e2] at h2
  refine ((TranscendenceTraces.rpBasic_of _ _ X k).2.2.1 _ _ _ _ h1 h2).2.1 ?_
  exact (congrArg (fun e => Sec.res e a) (fk_self p f hp h)).symm
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCorrPull
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.corrPull :
    CorrPull := by
  intro p Y S B O g s bS β hS T w hw hr
  have hsq : (pullback.fst T.p s ≫ T.r) ≫ g = (pullback.snd T.p s ≫ bS) ≫ β := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, hS.w,
      Category.assoc]
  haveI := T.fin
  refine ⟨⟨pullback T.p s, pullback.snd T.p s, hS.lift _ _ hsq, Wt.comap (pullback.fst T.p s) w,
    inferInstance,
    TranscendenceTraces.wtBC_holds _ _ _ _ w (IsPullback.of_hasPullback T.p s) hw⟩,
    pullback.fst T.p s, IsPullback.of_hasPullback T.p s, hS.lift_fst _ _ _, ?_, rfl⟩
  exact hS.lift_snd _ _ _
end

section -- restored from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCorrComm
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.corrComm :
    CorrComm := by
  intro l _ p Y S S' B B' O g s bS β hS i bS' γ hcomm hl T w c c' hc hc' k j
  obtain ⟨v, hv, hf, hb, hw⟩ := hc
  obtain ⟨v', hv', hf', hb', hw'⟩ := hc'
  have hsq : v' ≫ T.p = (c'.p ≫ i) ≫ s := by
    rw [Category.assoc]
    exact hv'.w
  obtain ⟨u, huv, hup⟩ : ∃ u, u ≫ v = v' ∧ u ≫ c.p = c'.p ≫ i :=
    ⟨hv.lift v' (c'.p ≫ i) hsq, hv.lift_fst _ _ _, hv.lift_snd _ _ _⟩
  subst huv
  have hpb : IsPullback u c'.p c.p i := IsPullback.of_right hv' hup hv
  have hfu : c'.f ≫ i = u ≫ c.f := by
    apply hS.hom_ext
    · simp only [Category.assoc]
      rw [hf', hf, Category.assoc]
    · calc (c'.f ≫ i) ≫ bS = (c'.f ≫ bS') ≫ γ := by rw [Category.assoc, hcomm, Category.assoc]
        _ = (c'.p ≫ bS') ≫ γ := by rw [hb']
        _ = c'.p ≫ i ≫ bS := by rw [Category.assoc, hcomm]
        _ = (u ≫ c.p) ≫ bS := by rw [hup, Category.assoc]
        _ = (u ≫ c.f) ≫ bS := by rw [Category.assoc, Category.assoc, hb]
  have hwu : c'.w = Wt.comap u c.w := by
    rw [hw', hw]
    funext Ω _ _ z
    simp only [Wt.comap, Category.assoc]
  exact TranscendenceTraces.corrBCQ_holds a8 l k j c' c i i u hpb hfu hwu hl
end

namespace UpperTheory.Gal.Mod

theorem esGen_holds (h : GlobalTheory.EtC.SpecGood) : ESGen :=
  esGen h esPt_holds nwtOne (frobQ frobTors) baseFacts denseGen frEx @corrPull @corrComm

end UpperTheory.Gal.Mod
