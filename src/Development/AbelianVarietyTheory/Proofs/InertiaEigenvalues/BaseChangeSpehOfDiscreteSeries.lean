module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcSpehProof

theorem hasInfCharGL_unique {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} (hV : V ≠ ⊥) {τ : E →+* ℂ} {m m' : Multiset ℂ} (h : HasInfCharGL V τ m)
    (h' : HasInfCharGL V τ m') : m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hV
  have e : ((m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem spehInf_eq (d : ℕ) (m : Multiset ℂ) : GlobalTheory.SphGal.spehInf d m = GlobalTheory.DefiniteBC.spehInf d m := by
  unfold GlobalTheory.SphGal.spehInf GlobalTheory.DefiniteBC.spehInf
  rw [← List.sum_ofFn, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem isUnitarisable_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitarisable_of_isLocComp (H : GlobalTheory.Published.DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, ⟨hV, hS⟩, -⟩ := (H E a ha).2.1 a 1 P (one_mul a) hP
  have hc := (H E a ha).2.2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

theorem hasInfChar_eq_of_sigma {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b : ℕ} {P : CuspSub E a}
    {Q : CuspSub E b} (h : (⟨a, CG.mk P⟩ : Σ c, CG E c) = ⟨b, CG.mk Q⟩) {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (hm : P.HasInfChar τ m) (hm' : Q.HasInfChar τ m') : m = m' := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h
  exact (CuspSub.Iso.hasInfChar (Quotient.exact (eq_of_heq h2)) hm).unique hm'

end GlobalTheory.BcSpehProof

namespace GlobalTheory.BcSpehProof

theorem baseChange_speh_of_discreteSeries (H : GlobalTheory.Published.DiscreteSpectrumGL)
    (hW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
      ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = n}
    {V : ∀ i, Submodule ℂ (Sm E (N i))} {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (bc : IsBaseChange π h V σ m) (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i))
    (hPn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (P i)) (hPs : ∀ i, GlobalTheory.DiscSpec.IsSpehOf (V i) (P i) (d i))
    (hNad : ∀ i, N i = d i * a i) :
    ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w)) := by
  have hN : ∀ i, 1 ≤ N i := bc.pos
  have hc : ∀ i, GlobalTheory.DiscSpec.HasSpehComp (V i) (P i) (d i) := fun i =>
    (H E (N i) (hN i)).2.2.2.2 (V i) (bc.discrete i) (a i) (d i) (P i) (hPn i) (hPs i)
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  choose m' hm1 hm2 using fun i τ => (hc i).inf τ
  have hmm : ∀ i τ, m i τ = GlobalTheory.DefiniteBC.spehInf (d i) (m' i τ) := fun i τ =>
    (hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hm2 i τ)).trans (spehInf_eq _ _)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have := hN i
    rw [hNad i] at this
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this⟩
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    GlobalTheory.DiscSpec.isCsd_of_isSpehOf H (hN i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  have hun : ∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ := fun i w =>
    ⟨isUnitarisable_of_isLocComp H (hpos i).1 (P i) (hPn i) w (ρ i w) (hρ i w),
      GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E (N i) (V i) (bc.discrete i) w (σ i w) (bc.loc i w)⟩
  have hm0 : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
    have h1 := (bc.inf i τ).1
    rw [h0, Multiset.card_zero] at h1
    have := hN i
    omega
  obtain rfl : N = fun i => d i * a i := funext hNad
  refine ⟨c, a, d, h, P, ρ, m', σ, ⟨hpos, hcsd, hρ, hm1, fun τ lam hl => ?_, fun i j hd hs => ?_, ?_⟩,
    fun i w => ⟨(hun i w).1, (hun i w).2, hsp i w⟩, bc.split⟩
  · rw [← bc.weight τ lam hl]
    exact Finset.sum_congr rfl fun i _ => (hmm i τ).symm
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hl⟩ := hW E n hn π hπ τ
    refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (hm0 i τ) ?_
    rw [hmm i τ, hmm j τ, hd, hasInfChar_eq_of_sigma hs (hm1 i τ) (hm1 j τ)]
  · intro w s ϖ q hs hU α hα
    exact GlobalTheory.T.satakeParameter_spherical_product_spehQuotients E w c n a d h (ρ · w) (σ · w) (fun i => (hpos i).2) (fun i => hsp i w) _
      (bc.inert w s ϖ q hs hU α hα)

end GlobalTheory.BcSpehProof

theorem GlobalTheory.BcSpeh.bcSpeh_of_baseChange : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.DiscreteSpectrumGL → BcSpeh := by
  intro H1 H2 E _ _ _ hE n hn π hπ
  obtain ⟨c, N, h, V, σ, m, bc⟩ := H1 E hE n hn π hπ
  choose a d P _ hPn hPs using fun i => (H2 E (N i) (bc.pos i)).1 (V i) (bc.discrete i)
  exact GlobalTheory.BcSpehProof.baseChange_speh_of_discreteSeries H2 GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary hn hπ bc a d P hPn hPs fun i => (hPs i).mul_eq.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecLaws

section Core

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

abbrev clsOf {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : IrrGL (k := w.adicCompletion E) :=
  cls (ParLaws.toRep σ)

end Core

end GlobalTheory.RecLaws

namespace GlobalTheory.RecLaws

section Core2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem rec_hasSatGL (H : IsRec h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (clsOf σ)).unr ∧ (rc (clsOf σ)).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (clsOf σ)).unr := (ParLaws.unr_iff H _).2 hsph
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [clsOf, ParLaws.rec_eq_diag H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl

end Core2

end GlobalTheory.RecLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0VanishOfZeroMultiplicity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0VanishOfZeroMultiplicity
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InvJump

open Module

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def qRep (ρ : Representation LL G V) (p : Submodule LL V) (hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p) :
    Representation LL G (V ⧸ p) where
  toFun g := p.mapQ p (ρ g) (fun x hx => hp g x hx)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

end Gen

theorem h0V_eq_bot_of_multV_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ hdR hm
  haveI := K.2
  haveI := LL.2
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.ne_bot_iff _ |>.1 hne
  have hinv : ∀ g, ρ g v = v := by
    intro g
    have := (Submodule.mem_iInf _).1 hv g
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this

  let σ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1) := 1
  let ι : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] V := (LinearMap.proj 0).smulRight v
  have hι : ∀ u, ι u = u 0 • v := fun u => rfl
  have hιeq : ∀ g x, ι (σ g x) = ρ g (ι x) := by
    intro g x
    rw [hι, hι, map_smul, hinv]
    rfl
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker, hι] at hu
    have h0 : u 0 = 0 := (smul_eq_zero.1 hu).resolve_right hv0
    funext c
    rw [Subsingleton.elim c 0, h0]
    rfl
  let p : Submodule ↥LL.1 V := LinearMap.range ι
  have hp : ∀ g, ∀ x ∈ p, ρ g x ∈ p := by
    rintro g _ ⟨u, rfl⟩
    exact ⟨σ g u, hιeq g u⟩
  let ρ₂ := GlobalTheory.InvJump.qRep ρ p hp
  have hπeq : ∀ g x, p.mkQ (ρ g x) = ρ₂ g (p.mkQ x) := fun g x => rfl
  obtain ⟨-, -, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T K LL (Fin 1 → ↥LL.1) σ V ρ (V ⧸ p) ρ₂
    ι p.mkQ hιeq hπeq hιinj (Submodule.mkQ_surjective p) (Submodule.ker_mkQ p).symm hdR
  have h1 : multV (P.PD K) σ τ 0 = 1 := by
    have := GlobalTheory.PtCore.multV_cycPow_line (P.PD K) (GlobalTheory.DRFil.isField_dR T)
      (GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K) σ 0 (fun g u => by simp [σ]) τ 0
    simpa using this
  have h2 := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL (V ⧸ p) ρ₂ τ 0).2.1
  have h3 := (hadd τ 0).2.1
  omega

end GlobalTheory.InvJump
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0VanishOfZeroMultiplicityStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_vanish_of_zero_multiplicity : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  first | exact @GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero | exact GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero | (intros; apply GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.GTwoTheta

open Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

theorem zero_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (0 : ℚ) ∉ JW D up j ρ := by
  obtain ⟨hlow, -, hcl, h0⟩ := hc j hj1 hjm ρ
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union, reflS, Set.mem_setOf_eq, AdmissibleParameterJ.refl]
    rintro (h | h)
    · have := hcl _ h; linarith
    · rcases hlow _ h with ⟨-, h2⟩ | ⟨h2, -⟩ <;> linarith
  · simpa only [JW, cloudT, lowT, ↓reduceIte] using h0

theorem JW_sub_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : JW D up j ρ ⊆ JJ D up j ρ := by
  intro q hq
  cases up
  · simp only [JW, cloudT, lowT, Bool.false_eq_true, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, Bool.false_eq_true, ↓reduceIte, Jm, Jp]
    rcases hq with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
  · simp only [JW, cloudT, lowT, ↓reduceIte, Set.mem_union] at hq
    simp only [JJ, ↓reduceIte, Jp, Set.mem_union]
    exact Or.inl hq

theorem neg_one_not_mem_JW {L : SizeData₂ D} (hc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) : (-1 : ℚ) ∉ JW D up j ρ :=
  fun h => ((hc j hj1 hjm ρ).2.1 up).1 (JW_sub_JJ up j ρ h)

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem dR_WT (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) ∧
      IsDR (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) := by
  have := D.nd.lPrime i
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e :=
    (GlobalTheory.DecompForms.main D i r ρ π).1 hD
  have hsum := (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hdec).1 hc
  exact ⟨(GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.1).1,
    (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) _ _ _ _ hsum.2).1⟩

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem twistedRep_no_invariants_purity (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (hr : GoodR D.nd i r)
    (hπ : π ∈ D.nd.Z i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)))) :
    H0V (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) = ⊥ ∧ H0V (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π))) = ⊥ := by
  have := D.nd.lPrime i
  have hjr := D.nd.j_range i
  obtain ⟨hdrW, hdrT⟩ := dR_WT D i r ρ π w hw C hD hc
  obtain ⟨τ₀⟩ := GlobalTheory.PtCore.nonempty_embE D i w hw C.LL C.le
  obtain ⟨g, ρ', -, -, hW⟩ := hJ i r hr w hw C τ₀
  obtain ⟨-, hW0, -, hT0⟩ := hW ρ π hπ hD 0
  constructor
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrW ?_
    refine hW0.trans ?_
    rw [if_neg]
    push_cast
    exact zero_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _
  · refine GlobalTheory.T.H0_vanish_of_zero_multiplicity _ _ _ (D.locT _) _ _ _ _ τ₀ hdrT ?_
    refine hT0.trans ?_
    rw [if_neg]
    rw [GlobalTheory.JumpSets.dualS_int]
    push_cast
    exact neg_one_not_mem_JW hJc _ hjr.1 hjr.2 ρ' _

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

theorem chi_jump (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hamb : ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∀ c ∈ Finset.Icc 1 D.R.t, ∀ a,
      multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a =
        if a = (c : ℤ) - 1 then 1 else 0)
    (c : ℕ) (hc1 : 1 ≤ c) (hct : c ≤ D.R.t) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (a : ℤ) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a ↔ a = (c : ℤ) - 1 := by
  have := D.nd.lPrime i
  have hm := hamb τ c (Finset.mem_Icc.2 ⟨hc1, hct⟩) a
  refine (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ (D.locT _) _ _ _
    (matRep (TruncatedSeriesCountingIdentities.locC C (chiRatO D.nd i c))) τ a).2.2.trans ?_
  refine (Iff.of_eq (congrArg (· ≠ 0) hm)).trans ?_
  split_ifs with h <;> simp [h]

theorem tw_jumps (D : D7) (L : SizeData₂ D) (ep : Bool) (hJ : hodgeTateJumpsAtModulesForSign D ep) (hJc : jcCondition L) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    (∀ (x y : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a =
        multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r y)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a) ∧
    (∀ (x : D.nd.X i) (a : ℤ),
      multV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ a ≤ 1) ∧
    (∀ x : D.nd.X i,
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (twistM (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹)) τ (-1)) := by
  have hjr := D.nd.j_range i
  obtain ⟨g, ρ', -, hx, -⟩ := hJ i r hr w hw C τ
  refine ⟨fun x y a => ?_, fun x a => ?_, fun x => ?_⟩
  · rw [← locC_rTwO, ← locC_rTwO, (hx x a).2.1, (hx y a).2.1]
  · rw [← locC_rTwO, (hx x a).2.1]
    split_ifs <;> norm_num
  · rw [← locC_rTwO, (hx x (-1)).1]
    push_cast
    exact ((hJc _ hjr.1 hjr.2 ρ').2.1 _).1

end GlobalTheory.GTwoTheta

namespace GlobalTheory.GTwoTheta
open Formalism.MainNotions.AdmissibleParameterJ

end GlobalTheory.GTwoTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesA
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesA
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ColumnUnramified

theorem blochKatoFinite_trivialRep_unramified_columnPlaces : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  intro D i dc w hw _ C
  rw [GlobalTheory.BridgeInertia.inertEq D i w hw]
  exact GlobalTheory.T.unramified_trivial_local (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL

end GlobalTheory.ColumnUnramified
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesAStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedTrivialH1f_of_decl : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  first | exact @GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | exact GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces | (intros; apply GlobalTheory.ColumnUnramified.blochKatoFinite_trivialRep_unramified_columnPlaces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem isIrreducible_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f) (hρ : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact e.isSimpleOrder

def pull (f : Weil h' →* Weil h) (hdeg : ∀ σ, deg (f σ) = deg σ) (hq : normV w = normV w')
    (hs : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g → IsSmooth (g.comp f))
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) : WDRep h' V where
  ρ := a.ρ.comp f
  N := a.N
  smooth := hs _ a.ρ a.smooth
  semisimple σ := a.semisimple (f σ)
  nilpotent := a.nilpotent
  comm σ := by
    show a.ρ (f σ) * a.N = _
    rw [a.comm (f σ), hdeg, hq]
    rfl

section Pull

variable (f : Weil h' →* Weil h) (hdeg : ∀ σ, deg (f σ) = deg σ) (hq : normV w = normV w')
    (hs : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g → IsSmooth (g.comp f))

theorem iso_pull {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {a : WDRep h V} {b : WDRep h V'}
    (hab : a.Iso b) : (pull f hdeg hq hs a).Iso (pull f hdeg hq hs b) := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e, fun σ v => h1 (f σ) v, h2⟩

def pullWD : WD h → WD h' :=
  Quotient.lift (s := isoSetoid h) (fun a => WD.mk (pull f hdeg hq hs a.2))
    (fun _ _ hab => WD.sound (iso_pull f hdeg hq hs hab))

theorem pullWD_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) :
    pullWD f hdeg hq hs (WD.mk a) = WD.mk (pull f hdeg hq hs a) :=
  WD.sound (iso_pull f hdeg hq hs (WD.iso_std a).symm)

theorem pullWD_eq {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h' V')
    (e : V ≃ₗ[ℂ] V') (h1 : ∀ σ v, e (a.ρ (f σ) v) = b.ρ σ (e v)) (h2 : ∀ v, e (a.N v) = b.N (e v)) :
    pullWD f hdeg hq hs (WD.mk a) = WD.mk b := by
  rw [pullWD_mk]; exact WD.sound ⟨e, h1, h2⟩

end Pull

end GlobalTheory.WDTransport

namespace GlobalTheory.WDTransport


open WDRep in
theorem exists_equiv_wd : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ S : WD h ≃ WD h', (∀ y y', WDRel φ y y' ↔ S y = y') ∧ (∀ y, (S y).lpDim = y.lpDim) ∧ S (WD.lpZero (h := h)) = WD.lpZero (h := h') ∧ (∀ y z, S (y.lpSum z) = (S y).lpSum (S z)) ∧ (∀ y z, S (y.lpChar z) = (S y).lpChar (S z)) ∧ (∀ y (s : ℝ), S (y.lpTw s) = (S y).lpTw s) ∧ (∀ n, S (WD.lpSp (h := h) n) = WD.lpSp (h := h') n) ∧ (∀ y, IsIrrWD (S y) ↔ IsIrrWD y) ∧ ∀ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (ξ' : Weil h' →* ℂˣ) (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ'), (∀ σ σ', WeilRel φ σ σ' → ξ σ = ξ' σ') → S (WD.lpOfChar h ξ hξ) = WD.lpOfChar h' ξ' hξ' := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i hP
  have hd1 : ∀ σ, deg (c.symm.toMonoidHom σ) = deg σ := fun σ => by
    have := hdegc (c.symm σ); simp only [MulEquiv.apply_symm_apply] at this
    simpa using this.symm
  have hd1' : ∀ σ, deg (c.symm σ) = deg σ := hd1
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g →
      IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have hs2 : ∀ (M : Type) [Monoid M] (g : Weil h' →* M), IsSmooth g →
      IsSmooth (g.comp c.toMonoidHom) := fun M _ g hg => (hsm M g).mp hg
  have hd2 : ∀ σ, deg (c.toMonoidHom σ) = deg σ := fun σ => hdegc σ
  let F := pullWD c.symm.toMonoidHom hd1 hq.symm hs1
  let B := pullWD c.toMonoidHom hd2 hq hs2
  have hF : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V),
      F (WD.mk a) = WD.mk (pull c.symm.toMonoidHom hd1 hq.symm hs1 a) := fun a => pullWD_mk _ _ _ _ a
  have hB : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h' V),
      B (WD.mk a) = WD.mk (pull c.toMonoidHom hd2 hq hs2 a) := fun a => pullWD_mk _ _ _ _ a
  let S : WD h ≃ WD h' :=
    { toFun := F
      invFun := B
      left_inv := fun y => by
        induction y using WD.ind with
        | hP n a =>
          rw [hF, hB]
          exact WD.sound ⟨.refl _ _, fun σ v => by simp [pull], fun v => rfl⟩
      right_inv := fun y => by
        induction y using WD.ind with
        | hP n a =>
          rw [hB, hF]
          exact WD.sound ⟨.refl _ _, fun σ v => by simp [pull], fun v => rfl⟩ }
  have hS : ∀ y, S y = F y := fun _ => rfl
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y y'
    constructor
    · rintro ⟨n, b, b', rfl, rfl, hN, hρ⟩
      rw [hS]
      refine pullWD_eq _ _ _ _ b b' (.refl _ _) (fun σ v => ?_) (fun v => by simp [hN])
      have := hρ (c.symm σ) σ ((hc _ _).mpr (by simp))
      simp [this]
    · rintro rfl
      obtain ⟨n, b, rfl⟩ := WD.exists_rep y
      refine ⟨n, b, pull c.symm.toMonoidHom hd1 hq.symm hs1 b, rfl, (hF b).symm, rfl, fun σ σ' hσ => ?_⟩
      rw [← (hc σ σ').mp hσ]
      simp [pull]
  · intro y
    induction y using WD.ind with
    | hP n a => rw [hS, hF, WD.lpDim_mk, WD.lpDim_mk]
  · rw [hS]
    exact pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => Subsingleton.elim _ _) (fun v => Subsingleton.elim _ _)
  · intro y z
    induction y using WD.ind with
    | hP n a =>
    induction z using WD.ind with
    | hP m b =>
      rw [hS, hS, hS, WD.lpSum_mk, hF, hF, hF, WD.lpSum_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => rfl, fun v => rfl⟩
  · intro y z
    induction y using WD.ind with
    | hP n a =>
    induction z using WD.ind with
    | hP m b =>
      rw [hS, hS, hS, WD.lpChar_mk, hF, hF, hF, WD.lpChar_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => rfl, fun v => rfl⟩
  · intro y s
    induction y using WD.ind with
    | hP n a =>
      rw [hS, hS, WD.lpTw_mk, hF, hF, WD.lpTw_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => by simp [pull, hd1', hq], fun v => rfl⟩
  · intro n
    rw [hS]
    exact pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => by simp [WDRep.spEig, hd1', hq]) (fun v => rfl)
  · intro y
    constructor
    · rintro ⟨n, b, hb, hirr⟩
      refine ⟨n, pull c.toMonoidHom hd2 hq hs2 b, ?_, isIrreducible_comp b.ρ _ c.surjective hirr⟩
      rw [← hB, hb]
      exact S.left_inv y
    · rintro ⟨n, a, rfl, hirr⟩
      exact ⟨n, pull c.symm.toMonoidHom hd1 hq.symm hs1 a, (hF a).symm,
        isIrreducible_comp a.ρ _ c.symm.surjective hirr⟩
  · intro ξ hξ ξ' hξ' hξξ
    rw [hS]
    refine pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => ?_) (fun v => rfl)
    have := hξξ (c.symm σ) σ ((hc _ _).mpr (by simp))
    simp [this]

end GlobalTheory.WDTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_over_transport_ring_iso_symm : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ S : WD h ≃ WD h', (∀ y y', WDRel φ y y' ↔ S y = y') ∧ (∀ y, (S y).lpDim = y.lpDim) ∧ S (WD.lpZero (h := h)) = WD.lpZero (h := h') ∧ (∀ y z, S (y.lpSum z) = (S y).lpSum (S z)) ∧ (∀ y z, S (y.lpChar z) = (S y).lpChar (S z)) ∧ (∀ y (s : ℝ), S (y.lpTw s) = (S y).lpTw s) ∧ (∀ n, S (WD.lpSp (h := h) n) = WD.lpSp (h := h') n) ∧ (∀ y, IsIrrWD (S y) ↔ IsIrrWD y) ∧ ∀ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (ξ' : Weil h' →* ℂˣ) (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ'), (∀ σ σ', WeilRel φ σ σ' → ξ σ = ξ' σ') → S (WD.lpOfChar h ξ hξ) = WD.lpOfChar h' ξ' hξ' := by
  exact @GlobalTheory.WDTransport.exists_equiv_wd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.SphSupport

theorem toral_of_isSpherical (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (k : Type) [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k))
    (hs : IsSpherical x.rep) :
    ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, ∃ (χ : kˣ →* ℂˣ) (hχ : IsUnram χ), y = IrrGL.ofChar χ
      (isSmoothChar_of_isUnram hχ) := by
  have hadm : IsAdmissible x.rep := (hBZ k).1 (Fin x.1) x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr
  have hI : fixed x.rep (iwahori k (Fin x.1)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm x.2.rep.irr hI
  have hχ : ∀ i, IsSmoothChar (unrChar k (α i)) := fun i =>
    isSmoothChar_of_isUnram (isUnram_unrChar k (α i))
  have H : IsCuspSupport x.rep (fun _ : Fin x.1 => 1) fun a => detRep (Fin 1) (unrChar k (α a)) :=
    ⟨x.2.rep.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k x.1 fun i => unrChar k (α i))⟩
  refine ⟨_, hasSupport_of_isCuspSupport H, ?_⟩
  intro y hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨unrChar k (α i), isUnram_unrChar k (α i), rfl⟩

theorem toral_and_good_of_isSpherical : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)),
      IsSpherical x.rep → Toral x ∧ Good x := by
  intro hBZ k _ _ _ _ x hs
  obtain ⟨s, hsup, hs1⟩ := toral_of_isSpherical hBZ k x hs
  have h1 : ∀ y ∈ s, y.1 = 1 := fun y hy => by
    obtain ⟨χ, -, rfl⟩ := hs1 y hy
    rfl
  exact ⟨⟨s, hsup, h1⟩, ⟨s, hsup, fun y hy => Or.inl (h1 y hy)⟩⟩

end GlobalTheory.SphSupport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChangeOfSplittingPair
set_option autoImplicit false

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum Formalism.IndefR.Lift

noncomputable section

namespace GlobalTheory.SplitChange

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW ν : (AE D)ˣ →* Circle}
  {om om' : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

theorem resEta_zero_of_triv {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hF : ∀ a, ν (idF D a) = 1) :
    ResEta D ν 0 :=
  ⟨h.1, fun η _ a => by rw [hF, pow_zero]⟩

theorem exists_twist_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g x y, IsDetRoot V h x → IsDetRoot W g y →
      om' (h, g) = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ ho.std V W χV χW ν ν om ho hν hν
    (resEta_zero_of_triv ho.resS hF) (resEta_zero_of_triv ho.resS hF)
  refine ⟨o, h1, fun h g x y hx hy => ?_⟩
  rw [h2 h g x y hx hy, Circle.coe_mul, Circle.coe_inv, mul_comm]

theorem twist_eq_root (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {h : GA D V} {g : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V h x) (hy : IsDetRoot W g y) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (((ν y : Circle) : ℂ) * ((ν x : Circle) : ℂ)⁻¹) • om (h, g) f := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  calc
    om' (h, g) f = o (h, g) f :=
      GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W _ _ om' o ho' h1 (h, g) f hf
    _ = _ := by rw [h2 h g x y hx hy, LinearMap.smul_apply]

theorem exists_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV) (hW : MuVal W ν nW) :
    ∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g) := by
  obtain ⟨o, h1, h2⟩ := exists_twist_root ho hν hF
  refine ⟨o, h1, fun h g => ?_⟩
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [h2 h g x y hx hy, hV.2 h x hx, hW.2 g y hy]

theorem twist_eq (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f := by
  obtain ⟨x, hx⟩ := hV.1 h
  obtain ⟨y, hy⟩ := hW.1 g
  rw [twist_eq_root ho hν hF ho' hx hy hf, hV.2 h x hx, hW.2 g y hy]

theorem thetaKO_twist (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1)
    (ho' : IsWeilDatumO ψ V W (χV * ν) (χW * ν) om') {nV : GA D V → ℂ} {nW : GA D W → ℂ} (hV : MuVal V ν nV)
    (hW : MuVal W ν nW) (h : GA D V) (g : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    thetaKO om' h g f = nW g * (nV h)⁻¹ * thetaKO om h g f := by
  unfold thetaKO
  rw [twist_eq ho hν hF ho' hV hW h g hf, Pi.smul_apply, smul_eq_mul]

theorem chrTh_tup {C : Type*} [CommGroup C] (μ : ℕ → C) (η ν : C) (j : ℕ) :
    chrTh (tup μ ν) η j = ((chrTh μ η j).1 * ν, (chrTh μ η j).2 * ν) := by
  unfold chrTh Formalism.IndefR.Lift.tup
  rw [mul_right_comm]

theorem change_of_splitting_pair (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW ν : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ho : IsWeilDatumO ψ V W χV χW om) (hν : IsHeckeChar D ν)
    (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' ∧ ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (χV * ν) (χW * ν) om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W χV χW om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  refine ⟨?_, fun nV nW hV hW => ⟨exists_twist ho hν hF hV hW, fun om' ho' h g f hf => twist_eq ho hν hF ho' hV hW h g hf⟩,
    fun om₁ h1 => GlobalTheory.WeilUniq.weilDatum_unique D ψ ho.std V W χV χW om₁ om h1 ho⟩
  obtain ⟨nV, hV, -⟩ := GlobalTheory.Member.exists_muVal D V ν hν hF
  obtain ⟨nW, hW, -⟩ := GlobalTheory.Member.exists_muVal D W ν hν hF
  exact ⟨nV, nW, hV, hW⟩

theorem change_of_splitting (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (μ : ℕ → (AE D)ˣ →* Circle)
    (η ν : (AE D)ˣ →* Circle) (j : ℕ) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (ho : IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om) (hν : IsHeckeChar D ν) (hF : ∀ a, ν (idF D a) = 1) :
    (∃ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV ∧ MuVal W ν nW) ∧
    (∀ (nV : GA D V → ℂ) (nW : GA D W → ℂ), MuVal V ν nV → MuVal W ν nW →
      (∃ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' ∧
        ∀ h g, om' (h, g) = (nW g * (nV h)⁻¹) • om (h, g)) ∧
      ∀ om', IsWeilDatumO ψ V W (chrTh (tup μ ν) η j).1 (chrTh (tup μ ν) η j).2 om' → ∀ h g f, IsThetaFunO ψ V W f →
        om' (h, g) f = (nW g * (nV h)⁻¹) • om (h, g) f) ∧
    ∀ om₁, IsWeilDatumO ψ V W (chrTh μ η j).1 (chrTh μ η j).2 om₁ → ∀ p f, IsThetaFunO ψ V W f → om₁ p f = om p f := by
  rw [chrTh_tup]
  exact change_of_splitting_pair D ψ V W _ _ ν om ho hν hF

end GlobalTheory.SplitChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionPreservesCuspidal
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.CuspExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (GlobalTheory.LocLanglands.sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [GlobalTheory.LocLanglands.sumList, charPol_lpZero]
  | cons b l ih =>
    have : GlobalTheory.LocLanglands.sumList (b :: l) =
        WD.lpSum b (GlobalTheory.LocLanglands.sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r : IrrGL (k := w.adicCompletion E) → WD h}

end GlobalTheory.LocLanglands.CuspExt

namespace GlobalTheory.LocLanglands

end GlobalTheory.LocLanglands

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def Maps (V : Submodule ℂ (Sm E a)) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Type :=
  {f : σ.V →ₗ[ℂ] Sm E a // (∀ v, f v ∈ V) ∧ ∀ g v, f (σ.ρ g v) = finRep E a (locGL E a w g) (f v)}

theorem iSup_range_eq (V : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable V) (hi : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) : ⨆ f : Maps V w σ, LinearMap.range f.1 = V := by
  have comm : ∀ o : Op E a, (∀ g, act o * finRep E a (locGL E a w g) = finRep E a (locGL E a w g) * act o) →
      ∀ (f : Maps V w σ) v, act o (f.1 v) ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 := fun o ho f v =>
    Submodule.mem_iSup_of_mem (⟨act o ∘ₗ f.1, fun v => hs o _ (f.2.1 v), fun g v => by
      rw [LinearMap.comp_apply, f.2.2]; exact LinearMap.congr_fun (ho g) _⟩ : Maps V w σ) ⟨v, rfl⟩
  refine (hi _ (iSup_le fun f => ?_) fun o φ hφ => ?_).resolve_left fun hb => ?_
  · rintro _ ⟨v, rfl⟩; exact f.2.1 v
  · have : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (⨆ f : Maps V w σ, LinearMap.range f.1).comap (act o) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      cases o with
      | fin k =>
        let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
        have h1 := comm (.fin (k * (locGL E a w g)⁻¹)) (fun g' => by
          change finRep E a _ * _ = _ * finRep E a _
          rw [← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w
            (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])]) f (σ.ρ g v)
        have h2 : act (.fin (k * (locGL E a w g)⁻¹)) (f.1 (σ.ρ g v)) = act (.fin k) (f.1 v) := by
          rw [f.2.2, act, act, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
        rwa [h2] at h1
      | cpt k =>
        refine comm (.cpt k) (fun g => ?_) f v
        have h2 := congrArg (rt E a) (infGL_comm (Unitary.toUnits k) (locGL E a w g))
        rw [map_mul, map_mul] at h2
        exact h2
      | lie X => exact comm (.lie X) (fun g => lie_rt_fin X (locGL E a w g)) f v
    exact this hφ
  · obtain ⟨f, h0, h1, hf⟩ := h
    refine h0 (LinearMap.ext fun v => ?_)
    have : f v ∈ ⨆ f : Maps V w σ, LinearMap.range f.1 :=
      Submodule.mem_iSup_of_mem (⟨f, h1, hf⟩ : Maps V w σ) ⟨v, rfl⟩
    rw [hb] at this
    exact this

theorem exists_comp_ne_zero (V : Submodule ℂ (Sm E a)) (hs : _root_.GlobalTheory.CuspRep.IsStable V) (hi : ∀ W ≤ V, _root_.GlobalTheory.CuspRep.IsStable W → W = ⊥ ∨ W = V)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (h : GlobalTheory.UnitaryBC.IsLocCompGL V w σ) {X : Type} [AddCommGroup X] [Module ℂ X] (β : V →ₗ[ℂ] X) (hβ : β ≠ 0) :
    ∃ f : Maps V w σ, β ∘ₗ f.1.codRestrict V f.2.1 ≠ 0 := by
  by_contra hc
  push Not at hc
  refine hβ (LinearMap.ext fun φ => ?_)
  have hle : (⨆ f : Maps V w σ, LinearMap.range f.1) ≤ (LinearMap.ker β).map V.subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨f.1 v, f.2.1 v⟩, LinearMap.congr_fun (hc f) v, rfl⟩
  rw [iSup_range_eq V hs hi w σ h] at hle
  obtain ⟨ψ, h1, h2⟩ := hle φ.2
  obtain rfl : ψ = φ := Subtype.ext h2
  exact h1

end GlobalTheory.LocDual
end
end
