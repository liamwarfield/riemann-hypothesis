module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemClosureOfJumps
public import Formalism.LocalToGlobal.CyclotomicLocalNorms.AddValuationAlgebraMapPadicIntUnitEqZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JBridgeInt
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jBridgeInt :
    UpperTheory.Gal.Seam.IntMap → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BridgeInt := by
  intro hInt E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hB γ x
  obtain ⟨φ, hφ, -⟩ := hInt E Ω l w A hA O Bw hB
  have h1 : Bw.j (algebraMap E Ω x) =
      ((algebraMap (CrystallineSemistableComparison.OK l Bw.Kw.1) Bw.Kw.1 (φ x) : Bw.Kw.1) : PadicAlgCl l) := by
    rw [hφ x]
    rfl
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ ≤ 1 := by
    rw [h1]
    have hm : ‖(((φ x : Bw.Kw.1)) : PadicAlgCl l)‖₊ ≤ 1 := (φ x).2
    exact_mod_cast hm
  have h3 : ‖γ (Bw.j (algebraMap E Ω x))‖ = ‖Bw.j (algebraMap E Ω x)‖ :=
    (GlobalTheory.Cyc.Model.isom_gal γ).norm_map_of_map_zero (map_zero _) _
  rw [h3]
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHodgeOpBc
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV GlobalTheory.HodgeCoh UpperTheory.Gal.G3 UpperTheory.Gal.Int.Geo
universe u v

private theorem hodgeTrace_pull_congr {F : Type} [Field F] {Y Z : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s]
    (p : Z ⟶ sp F) {q q' : Y ⟶ sp F} (e : q = q') (h₁ : s ≫ p = q) (h₂ : t ≫ p = q) (h₁' : s ≫ p = q') (h₂' : t ≫ p = q')
    (a b : ℕ) (x : hodgeH p a b) :
    hodgeTrace h₁ a b (hodgePull h₂ a b x) = hodgeTrace h₁' a b (hodgePull h₂' a b x) := by
  subst e; rfl

theorem UpperTheory.Gal.G3.jHodgeOpBc :
    BcSplits → HodgeTr → TrBc.{0} → HodgeOpBc := by
  intro hBc hTr hTrBc k F _ _ φ H g _ _ a b
  letI : Algebra k F := φ.toAlgebra
  obtain ⟨hF, hE, -⟩ := hBc (Spec.map (CommRingCat.ofHom φ)) H.q (H.s g ≫ H.q) (H.s g ≫ H.q) (H.s g) rfl
    (H.s g) rfl PEmpty (fun e => e.elim) (fun e => e.elim)
  refine ⟨hF, hE, hodgeTrace (bcMap_snd _ (H.s g) rfl) a b, ?_, ?_⟩
  · exact hTrBc (hodge F a b) _ H.q (H.s g ≫ H.q) (H.s g) rfl _ (hTr F a b _ _ _ (bcMap_snd _ _ _))
  · intro hF' hE' x
    exact @hodgeTrace_pull_congr _ _ _ _ _ _ hF' hE' _ _ _
      (bcMap_snd (Spec.map (CommRingCat.ofHom φ)) (H.s g) rfl) _ _ _ _ a b x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowNice
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem sq_bc {T Y S B : Scheme.{0}} (s : T ⟶ Y) (p : Y ⟶ S) (c : B ⟶ S) :
    IsPullback (pullback.fst (s ≫ p) c)
      (pullback.lift (pullback.fst (s ≫ p) c ≫ s) (pullback.snd (s ≫ p) c)
        (by rw [Category.assoc, pullback.condition]) : pullback (s ≫ p) c ⟶ pullback p c)
      s (pullback.fst p c) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := p) (h₃₁ := c) ?_ ?_
    (IsPullback.of_hasPullback p c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (s ≫ p) c
  · rw [pullback.lift_fst]

theorem UpperTheory.Gal.G3.jLowNice :
    FEtBasic → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowNice := by
  intro hb k L _ _ H θ O _ _ C D
  haveI : Smooth C.p := C.smooth
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (pullback.snd C.p (UpperTheory.Gal.Int.Geo.gen O k))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap O k) C.proj
  · intro g
    exact ⟨D.d g, hb.1 _ _ _ _ _ (sq_bc (D.s g) C.p (UpperTheory.Gal.Int.Geo.gen O k)) (D.fet g)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocalMat
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem isMatF_of_isMat {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
    (θ : H.Γ → Formalism.ConjugateSelfDual.Qbar l) {d : ℕ} (ρ₁ : (Ω ≃ₐ[k] Ω) →* Matrix.GeneralLinearGroup (Fin d) (Formalism.ConjugateSelfDual.Qbar l))
    (h : UpperTheory.Gal.Int.Geo.IsMat l H Ω (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁)
    (f : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Formalism.ConjugateSelfDual.Qbar l)) (hf : ∀ σ, (ρ₁ σ).val = f σ) :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.IsMatF H Ω θ f := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun σ j => ?_⟩
  rw [hb σ j, hf σ]

theorem UpperTheory.Gal.G3.jLocalMat :
    UpperTheory.Gal.Seam.NiceBc → UpperTheory.Gal.Seam.HopEx → UpperTheory.Gal.Seam.LocTower → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LocalMat := by
  intro hNice hHop hLoc E Ω _ _ _ _ _ l _ H θ hN Gw O _ _ _ Bw τK hτ
  refine ⟨fun g => ⟨_, hHop l _ _ (UpperTheory.Gal.Int.Geo.bcAlong H τK) (hNice _ _ τK H hN) g⟩, ?_⟩
  intro d ρ hρ
  obtain ⟨ρ₁, hρ₁, hc⟩ := hLoc l E _ Ω (Formalism.ConjugateSelfDual.Qbar l) τK Bw.j (fun x => (hτ x).symm) H hN
    (Formalism.ConjugateSelfDual.Qbar l) θ d ρ hρ
  refine isMatF_of_isMat (UpperTheory.Gal.Int.Geo.bcAlong H τK) (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁ hρ₁ _
    (fun σ => congrArg Units.val (hc _ σ (fun x => ?_)))
  rw [← Bw.e_comm]
  erw [MulEquiv.apply_symm_apply]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JModBc
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jModBc :
    UpperTheory.Gal.Seam.GoodOf → ModBc := by
  intro hG l _ K O _ _ φ Y W p d hs hp c _ _
  haveI : SmoothOfRelativeDimension d p := hs
  haveI : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 inferInstance
  have hcs : SmoothOfRelativeDimension d (c ≫ p) := by
    have h : SmoothOfRelativeDimension (0 + d) (c ≫ p) := inferInstance
    rwa [Nat.zero_add] at h
  have hqs : SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hcs
  have hcq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (c ≫ p) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_general c (GlobalTheory.SchemeWords.isQProjOver_of_isProjOver hp)
  haveI : IsProper p := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  have hcp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (c ≫ p) :=
    GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper O W (c ≫ p) hcq inferInstance
  have hqp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd φ hcp
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hsm : Smooth (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    SmoothOfRelativeDimension.smooth d _
  exact ⟨⟨hG l K.1 ⟨_, _⟩ hsm hqp, hsm⟩, hqs⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JBCTower
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3.BaseChangeTowers

private noncomputable def cmp {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    pullback p ab ⟶ pullback p a :=
  pullback.lift (pullback.fst p ab) (pullback.snd p ab ≫ b)
    (by rw [pullback.condition, Category.assoc, h])

private theorem cmp_fst {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.fst p a = pullback.fst p ab := pullback.lift_fst _ _ _

private theorem cmp_snd {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.snd p a = pullback.snd p ab ≫ b := pullback.lift_snd _ _ _

private theorem cmp_isPullback {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp p a ab b h) (pullback.snd p ab) (pullback.snd p a) b := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p a) (h₂₂ := a) (v₁₃ := p) ?_ (cmp_snd p a ab b h)
    (IsPullback.of_hasPullback p a)
  rw [cmp_fst, h]
  exact IsPullback.of_hasPullback p ab

private theorem cmp_bcMap {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp q a ab b h ≫ bcMap a f hf = bcMap ab f hf ≫ cmp p a ab b h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, cmp_fst, bcMap_fst, ← Category.assoc, cmp_fst]
  · rw [Category.assoc, Category.assoc, bcMap_snd, cmp_snd, cmp_snd, ← Category.assoc, bcMap_snd]

private theorem cmp_bcMap_isPullback {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp q a ab b h) (bcMap ab f hf) (bcMap a f hf) (cmp p a ab b h) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p ab) (v₂₂ := pullback.snd p a) (h₃₁ := b) ?_
    (cmp_bcMap p q f hf a ab b h) (cmp_isPullback p a ab b h)
  rw [bcMap_snd, bcMap_snd]
  exact cmp_isPullback q a ab b h

end UpperTheory.Gal.G3.BaseChangeTowers

open UpperTheory.Gal.G3.BaseChangeTowers in
theorem UpperTheory.Gal.G3.jBCTower :
    UpperTheory.Gal.Seam.NiceBc → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BCTower := by
  intro hN k K F _ _ _ τ φ H hH
  refine ⟨hN k K τ H hH, ⟨?_⟩⟩
  have hab : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom (φ.comp τ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let a := Spec.map (CommRingCat.ofHom τ)
  let ab := Spec.map (CommRingCat.ofHom (φ.comp τ))
  let b := Spec.map (CommRingCat.ofHom φ)
  have hz : IsPullback (cmp H.q a ab b hab) (UpperTheory.Gal.Int.Geo.bcAlong H (φ.comp τ)).q
      (UpperTheory.Gal.Int.Geo.bcAlong H τ).q b := cmp_isPullback H.q a ab b hab
  refine
    { z := cmp H.q a ab b hab
      hz := hz
      y := fun j => cmp (H.s j ≫ H.q) a ab b hab
      hs := fun j => ?_
      ht := fun j => ?_ }
  · exact cmp_bcMap_isPullback H.q (H.s j ≫ H.q) (H.s j) rfl a ab b hab
  · exact cmp_bcMap H.q (H.s j ≫ H.q) (H.t j) (H.comm j) a ab b hab
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHopLies
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

namespace UpperTheory.Gal.G3.HopfLiesOver

private theorem isTr_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} (p : Z ⟶ B)
    {q q' : Y ⟶ B} (e : q = q') (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p) (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} (r : X ⟶ B) (t : Y ⟶ X) (a : t ≫ r = q) (a' : t ≫ r = q') (y : T.H r),
        tr' (T.pull t a' y) = tr (T.pull t a y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ _ => rfl⟩

private theorem unit_l (l : ℕ) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (hl : (l : k) ≠ 0) :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h0
    apply hl
    apply (algebraMap k Ω).injective
    simpa using h0
  have h2 := (h1.isUnit).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem low_fet (hF : FEtBasic) {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) : FEt ((low D).s g) (D.d g) := by
  have hp : IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g)
      (pullback.fst C.p (gen O k)) := by
    refine (IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k)).flip).flip
    · change IsPullback (bcMap (gen O k) (D.s g) rfl ≫ pullback.snd C.p (gen O k)) _ _ _
      rw [bcMap_snd]
      exact (IsPullback.of_hasPullback _ _).flip
    · exact bcMap_fst (gen O k) (D.s g) rfl
  exact hF.1 _ _ _ _ _ hp (D.fet g)

end UpperTheory.Gal.G3.HopfLiesOver

open UpperTheory.Gal.G3.HopfLiesOver in
theorem UpperTheory.Gal.G3.jHopLies :
    EtGood → BcGood.{1} → FEtBasic → HopSpec → LiesOp.{1} → HopLies := by
  intro hEt hBc hF hHop hLies l _ k L O _ _ _ _ hl H θ C D hN Ω _ _ g
  have hT : (etG l k Ω).Good := hBc _ _ (hEt l (sp Ω) (unit_l l hl))
  obtain ⟨d, hd⟩ := hN.2.2 g
  haveI : IsFinite (H.s g) := hd.1
  haveI : Etale (H.s g) := hd.2.1
  obtain ⟨trg, htrg⟩ := hT.tr H.q (H.s g ≫ H.q) (H.s g) rfl
  have hfet := low_fet hF D g
  obtain ⟨tr, htr⟩ := @Th.Good.tr _ _ _ _ hT _ _ (pullback.snd C.p (gen O k))
    (pullback.snd (D.s g ≫ C.p) (gen O k)) ((low D).s g) hfet.1 hfet.2.1
    (bcMap_snd (gen O k) (D.s g) rfl)
  have hq : pullback.snd (D.s g ≫ C.p) (gen O k) = (low D).s g ≫ (low D).q :=
    (bcMap_snd (gen O k) (D.s g) rfl).symm
  obtain ⟨tr', htr', hrel⟩ := isTr_congr (etG l k Ω) _ hq _ tr htr
  rw [(hHop l hl H Ω g d hd).2 trg htrg, (hHop l hl (low D) Ω g (D.d g) hfet).2 tr' htr']
  apply LinearMap.ext
  intro x
  have e := hLies C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet (etG l k Ω) hT tr trg
    htr htrg x
  have e2 := hrel _ _ (bcMap_snd (gen O k) (D.t g) (D.comm g))
    ((bcMap_snd (gen O k) (D.t g) (D.comm g)).trans hq) x
  exact e.trans (congrArg (fun y => (D.m g : ℚ_[l]) • (etG l k Ω).pull (piK C) (piK_snd C) y) e2.symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JConjBridge
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual
universe u v

theorem UpperTheory.Gal.G3.jConjBridge :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.ConjBridge := by
  intro E Ω _ _ _ _ _ l _ Gw O iR iA iT Bw τ LL' τ' hτ
  haveI := Bw.Kw.2
  haveI := LL'.2
  let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
  let g : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l) :=
    fun x => τo.liftNormal_commutes (Om l) x
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hcont : Continuous (fun x : Om l => g x) := (GlobalTheory.Cyc.Model.isom_gal g).continuous
  let c : ↥(GK Bw.Kw) ≃* ↥(GK K₁) :=
    { toFun := fun h => ⟨g * (h : GQ l) * g⁻¹, GlobalTheory.Pst.BridgeInd.mem_GK_conj hK h.2⟩
      invFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  have c_cont : Continuous c :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have c_symm_cont : Continuous c.symm :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let Bw' : LocBridge l E Ω Gw O :=
    { Kw := K₁
      j := (g : Om l →+* Om l).comp Bw.j
      j_E := fun x => (hK _).1 (Bw.j_E x)
      j_dense := by
        intro y hy
        have h1 : g⁻¹ y ∈ Bw.Kw.1 := (hK _).2 (by simpa using hy)
        have h2 := image_closure_subset_closure_image hcont (Set.mem_image_of_mem _ (Bw.j_dense h1))
        have h3 : g (g⁻¹ y) = y := g.apply_symm_apply y
        simp only [h3] at h2
        refine closure_mono ?_ h2
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      e := Bw.e.trans c
      e_cont := c_cont.comp Bw.e_cont
      e_symm_cont := Bw.e_symm_cont.comp c_symm_cont
      e_comm := fun h x => by
        have h1 : g⁻¹ (g (Bw.j x)) = Bw.j x := g.symm_apply_apply _
        have h2 := Bw.e_comm h x
        change g (((Bw.e h : ↥(GK Bw.Kw)) : GQ l) (g⁻¹ (g (Bw.j x)))) = g (Bw.j ((h : Ω ≃ₐ[E] Ω) x))
        rw [h1, h2]
      LL := Bw.LL
      LL_split := fun σ x => by
        have hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
        let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
          ((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
        have he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (g.apply_symm_apply _)
        rw [← he]
        exact Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩
      eO := Bw.eO
      eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont
      eO_symm_cont := Bw.eO_symm_cont }
  refine ⟨g, O, iR, iA, iT, Bw', ⟨fun x => rfl, fun h => rfl⟩, ?_⟩
  refine RingHom.ext fun x => ?_
  exact (hg ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩).trans (hτ x).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowHodge
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

private theorem isTr_transport {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} {p : Z ⟶ B}
    {q q' : Y ⟶ B} (e : q = q') {s : Y ⟶ Z} {tr : T.H q →ₗ[R] T.H p} (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} {r : X ⟶ B} (t : Y ⟶ X) (h₁ : t ≫ r = q) (h₂ : t ≫ r = q') (y : T.H r),
        tr' (T.pull t h₂ y) = tr (T.pull t h₁ y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ => rfl⟩

private theorem low_square {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : GlobalTheory.GalV.HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) :
    IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g) (pullback.fst C.p (gen O k)) := by
  have hls : (low D).s g ≫ pullback.snd C.p (gen O k) = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    bcMap_snd (gen O k) (D.s g) rfl
  have hlf : (low D).s g ≫ pullback.fst C.p (gen O k) = pullback.fst (D.s g ≫ C.p) (gen O k) ≫ D.s g :=
    bcMap_fst (gen O k) (D.s g) rfl
  refine IsPullback.of_bot ?_ hlf.symm (IsPullback.of_hasPullback C.p (gen O k))
  convert IsPullback.of_hasPullback (D.s g ≫ C.p) (gen O k) using 2
  exact hls

theorem UpperTheory.Gal.G3.jLowHodge :
    HodgeGood → BcGood.{0} → FEtBasic → HodgeOpBc → CoverInv.{0} → LiesOp.{0} → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge := by
  intro hHG hBG hFB hOB hCI hLO k L F _ _ _ _ φ ψ H θ O _ _ C D hN hO a hH
  unfold HOcc at hH ⊢
  unfold Nice at hN
  obtain ⟨b, x, hx, he⟩ := hH
  unfold IsHEig at he
  set T' := (hodge F a b).bc (Spec.map (CommRingCat.ofHom φ)) with hT'
  have hgood : T'.Good := hBG _ _ (hHG F a b)
  obtain ⟨hinj, hsurj⟩ := hCI C hO T' hgood
  have hH' : ∀ g : H.Γ, ∃ trg : T'.H (H.s g ≫ H.q) →ₗ[F] T'.H H.q,
      T'.IsTr H.q (H.s g ≫ H.q) (H.s g) trg ∧ trg (T'.pull (H.t g) (H.comm g) x) = ψ (θ g) • x := by
    intro g
    obtain ⟨d, hd⟩ := hN.2.2 g
    haveI : IsFinite (H.s g) := hd.1
    haveI : Etale (H.s g) := hd.2.1
    obtain ⟨i1, i2, tr, htr, heq⟩ := hOB k F φ H g a b
    obtain ⟨j1, j2, hg⟩ := he g
    exact ⟨tr, htr, (heq j1 j2 x).symm.trans hg⟩
  obtain ⟨z, hz⟩ := hsurj x (fun g _ hθ => by
    obtain ⟨trg, htr, heq⟩ := hH' g
    exact ⟨trg, htr, by rw [heq, hθ, map_one, one_smul]⟩)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hz]; exact map_zero _)
  refine ⟨b, z, hz0, ?_⟩
  unfold IsHEig
  intro g
  have hfet : FEt ((low D).s g) (D.d g) := hFB.1 _ _ _ _ _ (low_square D g) (D.fet g)
  haveI : IsFinite ((low D).s g) := hfet.1
  haveI : Etale ((low D).s g) := hfet.2.1
  obtain ⟨i1, i2, trL, htrL, heqL⟩ := hOB k F φ (low D) g a b
  refine ⟨i1, i2, ?_⟩
  rw [heqL i1 i2 z]
  obtain ⟨tr', htr', htrans⟩ := isTr_transport T' (q := (low D).s g ≫ (low D).q)
    (q' := pullback.snd (D.s g ≫ C.p) (gen O k)) (bcMap_snd (gen O k) (D.s g) rfl) htrL
  obtain ⟨trg, htrg, hgeq⟩ := hH' g
  have hlies := hLO C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet T' hgood tr' trg htr' htrg z
  rw [hz, hgeq, ← hz, ← map_smul] at hlies
  have h := hinj ((map_smul (T'.pull (piK C) _) (ψ (θ g)) z).trans hlies)
  have h₂ : bcMap (gen O k) (D.t g) (D.comm g) ≫ (low D).q = pullback.snd (D.s g ≫ C.p) (gen O k) :=
    ((low D).comm g).trans (bcMap_snd (gen O k) (D.s g) rfl)
  have h3 : tr' (T'.pull (bcMap (gen O k) (D.t g) (D.comm g)) h₂ z) =
      trL (T'.pull ((low D).t g) ((low D).comm g) z) := htrans ((low D).t g) ((low D).comm g) h₂ z
  have h' : ψ (θ g) • z = ((D.m g : ℕ) : F) • trL (T'.pull ((low D).t g) ((low D).comm g) z) :=
    h.trans (congrArg (fun w => ((D.m g : ℕ) : F) • w) h3)
  have hm : ((D.m g : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
  have hw : trL (T'.pull ((low D).t g) ((low D).comm g) z) = ψ (θ g / (D.m g : L)) • z := by
    rw [map_div₀, map_natCast, div_eq_inv_mul, mul_smul, h']
    exact (inv_smul_smul₀ hm _).symm
  exact hw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowPiece
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open Formalism.ConjugateSelfDual (Qbar)
universe u v

private theorem intertwine_of_restrict {K V₁ V₀ G : Type*} [Field K] [AddCommGroup V₁] [Module K V₁]
    [AddCommGroup V₀] [Module K V₀] (f : V₁ →ₗ[K] V₀) (hf : Function.Injective f) {d₁ d₀ : ℕ}
    (W₁ : Submodule K V₁) (W₀ : Submodule K V₀) (b₁ : Module.Basis (Fin d₁) K W₁)
    (b₀ : Module.Basis (Fin d₀) K W₀) (hW : ∀ x ∈ W₁, f x ∈ W₀)
    (g₁ : G → V₁ →ₗ[K] V₁) (g₀ : G → V₀ →ₗ[K] V₀) (hc : ∀ σ x, g₀ σ (f x) = f (g₁ σ x))
    (ρ₁ : G → Matrix (Fin d₁) (Fin d₁) K) (ρ₀ : G → Matrix (Fin d₀) (Fin d₀) K)
    (h₁ : ∀ σ j, g₁ σ (b₁ j).1 = ∑ i, ρ₁ σ i j • (b₁ i).1)
    (h₀ : ∀ σ j, g₀ σ (b₀ j).1 = ∑ i, ρ₀ σ i j • (b₀ i).1) :
    ∃ A : Matrix (Fin d₀) (Fin d₁) K, Function.Injective A.mulVec ∧ ∀ σ, ρ₀ σ * A = A * ρ₁ σ := by
  let f' : W₁ →ₗ[K] W₀ := f.restrict hW
  have hf' : Function.Injective f' := fun x y h =>
    Subtype.ext (hf (congrArg Subtype.val h))
  let A := LinearMap.toMatrix b₁ b₀ f'
  have hA : ∀ j, f (b₁ j).1 = ∑ i, A i j • (b₀ i).1 := by
    intro j
    have e2 := congrArg W₀.subtype (b₀.sum_repr (f' (b₁ j)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simp only [A, LinearMap.toMatrix_apply]
    exact e2.symm
  refine ⟨A, ?_, fun σ => ?_⟩
  · intro v w h
    have key : ∀ u : Fin d₁ → K, A.mulVec u = b₀.repr (f' (b₁.equivFun.symm u)) := by
      intro u
      have hu : ⇑(b₁.repr (b₁.equivFun.symm u)) = u := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      have := LinearMap.toMatrix_mulVec_repr b₁ b₀ f' (b₁.equivFun.symm u)
      rw [hu] at this
      exact this
    rw [key, key] at h
    exact b₁.equivFun.symm.injective (hf' (b₀.repr.injective (Finsupp.ext fun i => congrFun h i)))
  · have hli : LinearIndependent K (fun i => (b₀ i).1) :=
      b₀.linearIndependent.map' W₀.subtype (Submodule.ker_subtype _)
    ext i j
    have e₁ : g₀ σ (f (b₁ j).1) = ∑ i, (ρ₀ σ * A) i j • (b₀ i).1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hA, map_sum]
      simp only [map_smul, h₀, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₂ : f (g₁ σ (b₁ j).1) = ∑ i, (A * ρ₁ σ) i j • (b₀ i).1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h₁, map_sum]
      simp only [map_smul, hA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
    have e₃ : ∑ i, ((ρ₀ σ * A) i j - (A * ρ₁ σ) i j) • (b₀ i).1 = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← e₁, ← e₂, hc, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.1 hli _ e₃ i)

private theorem galMap_bcMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    {p : X ⟶ sp k} {q : Y ⟶ sp k} (f : Y ⟶ X) (h : f ≫ p = q) (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω q σ ≫ bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h =
      bcMap (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f h ≫ galMap Ω p σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, galMap_fst, bcMap_fst, galMap_fst_assoc]
  · rw [Category.assoc, Category.assoc, bcMap_snd, galMap_snd, galMap_snd, reassoc_of% bcMap_snd]

theorem UpperTheory.Gal.G3.jLowPiece :
    HopLies → PieceLe → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := by
  intro hL hP E Ω _ _ _ _ _ l _ H θ O _ _ C D hN hO d₁ d₀ ρ₁ ρ₀ ⟨b₁, h₁⟩ ⟨b₀, h₀⟩
  have hl : (l : E) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  obtain ⟨hinj, -⟩ := hP l hl C hO Ω
  have hop' := fun g => hL l hl C D hN Ω g
  let P : Htot l (sch.obj ((low D).geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
    (etG l E Ω).pull (piK C) (piK_snd C)
  have hop'' : ∀ g, hop l H Ω g ∘ₗ P = (D.m g : ℚ_[l]) • (P ∘ₗ hop l (low D) Ω g) := hop'
  have hinj' : Function.Injective (P.baseChange (Qbar l)) := hinj
  have hW : ∀ x ∈ piece l (low D) Ω (Qbar l) (fun g => θ g / D.m g),
      P.baseChange (Qbar l) x ∈ piece l H Ω (Qbar l) θ := by
    intro x hx
    simp only [piece, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro g
    have hm : ((D.m g : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (D.lies g).1.ne'
    have e : (hop l H Ω g).baseChange (Qbar l) (P.baseChange (Qbar l) x) =
        ((hop l H Ω g ∘ₗ P).baseChange (Qbar l)) x := by
      rw [LinearMap.baseChange_comp]; rfl
    rw [e, hop'', LinearMap.baseChange_smul, LinearMap.smul_apply, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx g, map_smul, ← algebraMap_smul (Qbar l) (D.m g : ℚ_[l]), map_natCast,
      smul_smul, mul_div_cancel₀ _ hm]
  have hc : ∀ (σ : Ω ≃ₐ[E] Ω) x, galV l H Ω (Qbar l) σ (P.baseChange (Qbar l) x) =
      P.baseChange (Qbar l) (galV l (low D) Ω (Qbar l) σ x) := by
    intro σ x
    have e : galTot l Ω H.q σ ∘ₗ P = P ∘ₗ galTot l Ω (low D).q σ := by
      have e' := congrArg (fun u => pullTot l (sch.map u))
        (galMap_bcMap (Ω := Ω) (piK C) (piK_snd C) σ)
      simp only [Functor.map_comp, pullTot_comp] at e'
      exact e'
    have e2 := congrArg (fun u => LinearMap.baseChange (Qbar l) u x) e
    simp only [LinearMap.baseChange_comp] at e2
    exact e2
  exact intertwine_of_restrict _ hinj' _ _ b₁ b₀ hW (galV l (low D) Ω (Qbar l)) (galV l H Ω (Qbar l)) hc
    (fun σ => (ρ₁ σ).val) (fun σ => (ρ₀ σ).val) h₁ h₀
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCoverOp
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3

private theorem isUnit_natCast_sp (l : ℕ) (hl : l ≠ 0) (Ω : Type) [Field Ω] [CharZero Ω] :
    IsUnit ((l : Γ(sp Ω, ⊤))) := by
  have h : IsUnit ((l : Ω)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl)
  have h2 := h.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem th_pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}} {p : X ⟶ B}
    {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : T.pull f h = T.pull f' h' := by
  subst e; rfl

private theorem bcMap_comp' {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'} (u : Z ⟶ Y)
    (f : Y ⟶ X) (hu : u ≫ q = r) (hf : f ≫ p = q) (h : (u ≫ f) ≫ p = r) :
    bcMap g u hu ≫ bcMap g f hf = bcMap g (u ≫ f) h := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, bcMap_fst, Category.assoc]
  · rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]

private theorem lmap_of_key {R : Type*} [Semiring R] {M N P : ℤ → Type*} [∀ m, AddCommMonoid (M m)]
    [∀ m, AddCommMonoid (N m)] [∀ m, AddCommMonoid (P m)] [∀ m, Module R (M m)] [∀ m, Module R (N m)]
    [∀ m, Module R (P m)] (T : ∀ m, M m →ₗ[R] N m) (C : ∀ m, N m →ₗ[R] P m) {I : Type*} [Fintype I]
    (S : I → ∀ m, M m →ₗ[R] P m) (h : ∀ m x, C m (T m x) = ∑ i, S i m x) (x : DirectSum ℤ M) :
    DirectSum.lmap C (DirectSum.lmap T x) = ∑ i, DirectSum.lmap (S i) x := by
  apply DFinsupp.ext
  intro m
  have hs : ∀ s : Finset I, (∑ i ∈ s, DirectSum.lmap (S i) x) m = ∑ i ∈ s, S i m (x m) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, DirectSum.add_apply, ih, DirectSum.lmap_apply]
  rw [hs, DirectSum.lmap_apply, DirectSum.lmap_apply]
  exact h m (x m)

private theorem coverCore (hE : EtnGood) (hS : BcSplits) (hG : BcGal) (hU : CorrUniq) (l : ℕ) [Fact l.Prime]
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω] (H : HTower k) (g : H.Γ) [IsFinite (H.s g)] [Etale (H.s g)]
    (W : Scheme.{0}) (c : W ⟶ H.Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)) (I : Type) [Fintype I]
    (σ : I → (W ⟶ H.Y g)) (hσ : ∀ i, (σ i ≫ H.t g) ≫ H.q = c ≫ H.q) (hGal : IsGalois c G a) (hSp : Splits (H.s g) c σ)
    (hEx : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T) :
    ∃ Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0,
      hop l H Ω g = DirectSum.lmap Tm ∧
      (∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0), pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x) ∧
      ∀ m : ℤ, Function.Injective (pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0) := by
  classical
  have hu := isUnit_natCast_sp l (Fact.out : l.Prime).ne_zero Ω
  have hGood := fun m : ℤ => hE l (sp Ω) hu m 0
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hσs : ∀ j, σ j ≫ H.s g ≫ H.q = c ≫ H.q := fun j => by
    rw [← Category.assoc, hSp.choose j]
  have hac : ∀ x, a x ≫ c ≫ H.q = c ≫ H.q := fun x => by
    rw [← Category.assoc, hGal.2.2.2.2.2.choose x]
  obtain ⟨hfin, het, hspl⟩ := hS g₀ H.q (H.s g ≫ H.q) (c ≫ H.q) (H.s g) rfl c rfl I σ hσs
  have hsp' := hspl hSp
  have hgal' := hG g₀ H.q (c ≫ H.q) c rfl G a hac hGal
  choose tr htr using fun m : ℤ => (hGood m).tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  let Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0 := fun m =>
    tr m ∘ₗ (etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
  have key : ∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0),
      pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x := by
    intro m x
    have h1 := htr m _ (pullback.snd (c ≫ H.q) g₀) (bcMap g₀ c rfl) (bcMap_snd _ _ _) I
      (fun j => bcMap g₀ (σ j) (hσs j)) (fun j => bcMap_snd _ _ _) hsp'
      ((etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) x)
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    have e := bcMap_comp' g₀ (σ i) (H.t g) (hσs i) (H.comm g) (hσ i)
    have h2 := (etn l (sp Ω) m 0).pull_comp (bcMap g₀ (σ i) (hσs i)) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
      (bcMap_snd _ _ _) (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x
    rw [← h2, th_pull_congr _ e _ (bcMap_snd _ _ _)]
    rfl
  have hA : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (DirectSum.lmap Tm) := by
    refine ⟨_, bcMap g₀ c rfl, G, inferInstance, inferInstance, fun x => bcMap g₀ (a x) (hac x), I, inferInstance,
      fun j => bcMap g₀ (σ j) (hσs j), hgal', hsp', fun x => ?_⟩
    have e : ∀ j, bcMap g₀ (σ j) (hσs j) ≫ H.tΩ Ω g = geomMap Ω (c ≫ H.q) (σ j ≫ H.t g) (hσ j) := fun j =>
      bcMap_comp' g₀ (σ j) (H.t g) (hσs j) (H.comm g) (hσ j)
    simp only [e]
    exact lmap_of_key Tm (fun m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0)
      (fun i m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0) key x
  refine ⟨Tm, ?_, key, fun m => ?_⟩
  · have hh : hop l H Ω g = hEx.choose := by
      unfold hop
      exact dif_pos hEx
    rw [hh]
    exact hU l Ω (pullback.snd H.q g₀) _ _ _ _ hEx.choose_spec hA
  · exact (hGood m).inj _ _ (bcMap g₀ c rfl) (bcMap_snd _ _ _) G _ hgal'

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.jCoverOp :
    EtnGood → BcSplits → BcGal → CorrUniq → PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := by
  intro hE hS hG hU l _ K H _ g _ _ W c G _ _ a I _ σ hσ hGal hSp hEx n
  obtain ⟨Tm, h1, h2, h3⟩ := coverCore hE hS hG hU l H g W c G a I σ hσ hGal hSp hEx
  refine ⟨h3 n, Tm n, fun x => ?_, ?_⟩
  · rw [h1, DirectSum.lmap_lof]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.sum_apply]
    exact h2 n x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JJumpOfHT2
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace UpperTheory.Gal.G3

private theorem eig_coord {F : Type} [Field F] {m : ℕ} (s : F →+* F) (A : Matrix (Fin m) (Fin m) F)
    (Q : Matrix.GeneralLinearGroup (Fin m) F) (D : Fin m → F) (z : Fin m → F) (u : F)
    (h1 : A * (Q : Matrix (Fin m) (Fin m) F).map s = (Q : Matrix (Fin m) (Fin m) F) * Matrix.diagonal D)
    (h2 : A.mulVec (fun q => s (z q)) = u • z) (i : Fin m) :
    D i * s (((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F).mulVec z i) =
      u * ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F).mulVec z i := by
  set Qi : Matrix (Fin m) (Fin m) F := ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) with hQi
  set Qm : Matrix (Fin m) (Fin m) F := (Q : Matrix (Fin m) (Fin m) F) with hQm
  have hQ1 : Qm * Qi = 1 := by
    rw [hQi, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQ2 : Qi * Qm = 1 := by
    rw [hQi, hQm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set c : Fin m → F := Qi.mulVec z with hc
  have hz : Qm.mulVec c = z := by
    rw [hc, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  have hsz : (fun q => s (z q)) = (Qm.map s).mulVec (fun q => s (c q)) := by
    funext q
    rw [← hz]
    exact RingHom.map_mulVec s Qm c q
  have key : Qm.mulVec ((Matrix.diagonal D).mulVec (fun q => s (c q))) = Qm.mulVec (u • c) := by
    rw [Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, ← hsz, h2, Matrix.mulVec_smul, hz]
  have key2 : (Matrix.diagonal D).mulVec (fun q => s (c q)) = u • c := by
    have h3 : ∀ v : Fin m → F, Qi.mulVec (Qm.mulVec v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, hQ2, Matrix.one_mulVec]
    rw [← h3 ((Matrix.diagonal D).mulVec fun q => s (c q)), key, h3]
  have := congrFun key2 i
  simpa [Matrix.mulVec_diagonal] using this

private theorem chi_solve {l : ℕ} [Fact l.Prime] (t : ℚ_[l]ˣ) (n b : ℤ) (x y : ℂ_[l])
    (h : (((t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y = (((t ^ (-b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) :
    y = (((t ^ (n - b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x := by
  have e : ∀ u v : ℚ_[l]ˣ, (((u * v : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = ((u : ℚ_[l]) : ℂ_[l]) * ((v : ℚ_[l]) : ℂ_[l]) :=
    fun u v => by rw [Units.val_mul]; exact map_mul (algebraMap ℚ_[l] ℂ_[l]) _ _
  have one : (((1 : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    rw [Units.val_one]; exact map_one (algebraMap ℚ_[l] ℂ_[l])
  calc y = (((t ^ n * t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y := by
        rw [← zpow_add, add_neg_cancel, zpow_zero, one, one_mul]
    _ = (((t ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * ((((t ^ (-n) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * y) := by
        rw [e, mul_assoc]
    _ = (((t ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * ((((t ^ (-b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) := by rw [h]
    _ = (((t ^ (n - b) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x := by
        rw [← mul_assoc, ← e, ← zpow_add, sub_eq_add_neg]

private theorem gal_cont {l : ℕ} [Fact l.Prime] (g : GQ l) : Continuous fun x : Om l => g x := by
  refine (AddMonoidHomClass.isometry_of_norm g fun x => ?_).continuous
  have h := GlobalTheory.RingBasics.norm_σC g (x : ℂ_[l])
  rw [GlobalTheory.RingBasics.σC_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe] at h
  exact h

private theorem chiPow_eq {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (n : ℤ) :
    GlobalTheory.HTLink.chiPow σ n = ((((P.χQ σ) ^ n : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) := by
  have hχ : P.χQ = Formalism.L2.LocGap.Gal.χQ l := Formalism.L2.LocGap.Gal.eq_χQ_of_cyc P.χQ P.χQ_cyc
  rw [GlobalTheory.HTLink.chiPow, hχ, Units.val_zpow_eq_zpow_val]
  exact (map_zpow₀ (algebraMap ℚ_[l] ℂ_[l]) _ n).symm

end UpperTheory.Gal.G3


set_option maxHeartbeats 1000000 in
theorem UpperTheory.Gal.G3.jJumpOfHT2 :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.JumpOfHT2 := by
  classical
  unfold PositivityTheory.AutomorphicGaloisHodgeTate.G8.JumpOfHT2
  intro E Ω _ _ _ _ _ l _ P AI hT' Gw O O' _ _ _ _ _ _ Bw Bw' γ hC d r a Jm hOcc hJ
  obtain ⟨hT⟩ := hT'
  obtain ⟨LL', r', ⟨hLL, hmod⟩, hdR, τ', hInd, hcnt⟩ := hJ
  obtain ⟨S, z, hz0, hz⟩ := hOcc
  haveI := Bw.Kw.2
  haveI := Bw'.Kw.2
  haveI := LL'.2

  have hg : ∀ y : ↥Bw.Kw.1, γ (y : Om l) = ((τ' y : ↥LL'.1) : Om l) := by
    let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
    let g₁ : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
    have hg₁ : ∀ y : ↥Bw.Kw.1, g₁ (y : Om l) = ((τ' y : ↥LL'.1) : Om l) := fun y =>
      τo.liftNormal_commutes (Om l) y
    have hclosed : IsClosed {x : Om l | g₁ x = γ x} := isClosed_eq (gal_cont g₁) (gal_cont γ)
    have hsub : Set.range (fun x : E => Bw.j (algebraMap E Ω x)) ⊆ {x : Om l | g₁ x = γ x} := by
      rintro _ ⟨x, rfl⟩
      calc g₁ (Bw.j (algebraMap E Ω x)) = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL'.1) : Om l) :=
            hg₁ ⟨_, Bw.j_E x⟩
        _ = Bw'.j (algebraMap E Ω x) := (hInd x).symm
        _ = γ (Bw.j (algebraMap E Ω x)) := hC.1 _
    intro y
    rw [← hg₁ y]
    exact ((hclosed.closure_subset_iff.2 hsub) (Bw.j_dense y.2)).symm

  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (γ : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (γ : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (γ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ γ x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hK₁LL : K₁.1 ≤ LL'.1 := by
    rw [hK₁]
    rintro _ ⟨x, hx, rfl⟩
    change γ x ∈ LL'.1
    rw [show γ x = _ from hg ⟨x, hx⟩]
    exact (τ' ⟨x, hx⟩).2

  let cj : ↥(GK K₁) →* ↥(GK Bw.Kw) :=
    { toFun := fun h => ⟨γ⁻¹ * (h : GQ l) * γ, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  let r₁ : ↥(GK K₁) →* Matrix.GeneralLinearGroup (Fin d) ↥LL'.1 :=
    (r'.comp Bw.e.symm.toMonoidHom).comp cj
  have hρ : ∀ (h : ↥(GK Bw.Kw)) (h' : ↥(GK K₁)), (h' : GQ l) = γ * h * γ⁻¹ →
      (((Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
        ((Units.coeHom _).comp r₁)) h' = Bw.repE LL' r' h := by
    intro h h' hh
    have : cj h' = h := Subtype.ext (by simp [cj, hh, mul_assoc])
    simp only [MonoidHom.comp_apply, r₁, this]
    rfl
  have hD := GlobalTheory.Pst.BridgeInd.finrank_DdR_conj P hρ hK
  have hdR₁ := hD.symm.trans (hdR.trans (congrArg (· * d) (GlobalTheory.Pst.BridgeInd.finrank_eq_of_mem_iff_field hK)))
  let τ₂ : ↥K₁.1 →ₐ[ℚ_[l]] ↥LL'.1 := IntermediateField.inclusion hK₁LL
  have hτ₂ : ∀ x : ↥K₁.1, ((τ₂ x : ↥LL'.1) : Om l) = (x : Om l) := fun x => rfl
  have hM : ∀ n, multV (P.PD Bw.Kw) (Bw.repE LL' r') τ' n = multV (P.PD K₁) _ τ₂ n :=
    fun n => GlobalTheory.Pst.BridgeInd.multV_conj P hρ hK τ' τ₂ (fun c c' hc => Subtype.ext (by
      change (c' : Om l) = _; rw [hc, hg])) n
  have hsplit : ∀ (σ : ↥K₁.1 →ₐ[ℚ_[l]] Om l) (x : ↥K₁.1), σ x ∈ LL'.1 := by
    intro σ x
    have hx : γ⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
    let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
      ((γ : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
    have he : e₁ ⟨γ⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (by
      change γ (γ⁻¹ (x : Om l)) = (x : Om l)
      rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl)
    rw [← he]
    exact hLL (Bw.LL_split (σ.comp e₁) ⟨γ⁻¹ (x : Om l), hx⟩)
  haveI := K₁.2
  let K₀ : FinExt l := ⟨K₁.1 ⊔ LL'.1, inferInstance⟩
  obtain ⟨Pm, k, hk, heig⟩ := GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis l P AI hT K₁ LL' d r₁ hdR₁ hsplit τ₂ hτ₂ K₀
    le_sup_left le_sup_right
  have hJm : Multiset.map k Finset.univ.val = Jm := by
    refine Multiset.ext.mpr fun n => ?_
    have := (hk n).trans ((hM n).symm.trans (hcnt n).symm)
    exact_mod_cast this

  let F : IntermediateField ℚ_[l] (Om l) := IntermediateField.adjoin ℚ_[l] (S : Set (Om l))
  haveI : FiniteDimensional ℚ_[l] F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI := K₀.2
  let K'' : FinExt l := ⟨K₀.1 ⊔ Bw'.Kw.1 ⊔ F, inferInstance⟩
  set c : Fin d → ℂ_[l] :=
    ((Pm⁻¹ : Matrix.GeneralLinearGroup (Fin d) ℂ_[l]) : Matrix (Fin d) (Fin d) ℂ_[l]).mulVec z with hc
  have hcoord : ∀ h : GQ l, h ∈ GK K'' → ∀ i,
      ((((P.χQ h) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * Per.σC h (c i) =
        ((((P.χQ h) ^ (-a) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * c i := by
    intro h hh i
    have h0 : h ∈ GK K₀ := GK_le (le_trans le_sup_left le_sup_left) hh
    have hw : h ∈ GK Bw'.Kw := GK_le (le_trans le_sup_right le_sup_left) hh
    have h1 : h ∈ GK K₁ := GK_le le_sup_left h0
    have hS : ∀ x ∈ S, h x = x := fun x hx =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x
        ((le_sup_right : F ≤ K''.1) (IntermediateField.subset_adjoin _ _ hx))
    have hx : Bw'.e.symm ⟨h, hw⟩ = Bw.e.symm (cj ⟨h, h1⟩) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [hC.2, MulEquiv.apply_symm_apply]
      change h = γ * (γ⁻¹ * h * γ) * γ⁻¹
      group
    have e1 : ((r (Bw'.e.symm ⟨h, hw⟩)).val.map (algebraMap (Om l) ℂ_[l])).mulVec (fun q => Per.σC h (z q)) =
        GlobalTheory.HTLink.chiPow h (-a) • z := hz ⟨h, hw⟩ hS
    have e2 := heig ⟨h, h1⟩ h0
    have hr : (r (Bw.e.symm (cj ⟨h, h1⟩))).val.map (algebraMap (Om l) ℂ_[l]) =
        (r₁ ⟨h, h1⟩ : Matrix (Fin d) (Fin d) ↥LL'.1).map (fun x => (((x : ↥LL'.1) : Om l) : ℂ_[l])) := by
      rw [← hmod]
      rfl
    rw [hx, hr, chiPow_eq P] at e1
    exact eig_coord (Per.σC h) _ Pm _ z _ e2 e1 i
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hz0
    have hc' : c = 0 := funext hall
    have : (Pm : Matrix (Fin d) (Fin d) ℂ_[l]).mulVec c = z := by
      rw [hc, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [← this, hc', Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := hc0
  have hki : k i = a := by
    by_contra hne
    exact hi (GlobalTheory.T.tate_no_twisted_invariants_complexPadic l P AI hT K'' (k i - a) (sub_ne_zero.2 hne) (c i) fun g =>
      UpperTheory.Gal.G3.chi_solve _ _ _ _ _ (hcoord g g.2 i))
  rw [← hJm, ← hki]
  exact Multiset.mem_map_of_mem k (Finset.mem_univ_val i)

end
end
