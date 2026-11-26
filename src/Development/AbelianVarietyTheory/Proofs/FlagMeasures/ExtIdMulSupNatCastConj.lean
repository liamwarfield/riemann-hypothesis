module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassOfTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassTermsLeOverlatticeMasses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMovePreservesFrameLatticeLevels
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWtEqMulNuStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem extId_eq_map_psi (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, e⟩
    exact ⟨a, ha, Subtype.ext e.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem extId_mul_sup_natCast_conj : ∀ (I : AutInst), (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), extId I (𝔞 * 𝔟) = extId I 𝔞 * extId I 𝔟) ∧ (∀ 𝔞 𝔟 : Ideal (𝓞 I.E), 𝔞 ⊔ 𝔟 = ⊤ → extId I 𝔞 ⊔ extId I 𝔟 = ⊤) ∧ (∀ m : ℕ, extId I (Ideal.span {(m : 𝓞 I.E)}) = Ideal.span {(m : IntAf I.F I.E)}) ∧ (∀ w : HeightOneSpectrum (𝓞 I.E), ∃ w', IsConj I w w') ∧ (∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w' w) ∧ (∀ w w' w'' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → IsConj I w w'' → w' = w'') ∧ ∀ w w' : HeightOneSpectrum (𝓞 I.E), IsConj I w w' → ∀ z ∈ extId I w.asIdeal, ∃ z' ∈ extId I w'.asIdeal, (z' : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.sigR I.cm.sig (Af I.F) z := by
  intro I
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  have hsig : ∀ z ∈ IntAf I.F I.E, Formalism.UG.sigR I.cm.sig (Af I.F) z ∈ IntAf I.F I.E :=
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2
  refine ⟨fun a b => ?_, fun a b h => ?_, fun m => ?_, fun w => ?_, fun w w' h => ?_,
    fun w w' w'' h h' => ?_, fun w w' h z hz => ?_⟩
  · simp only [extId_eq_map_psi, Ideal.map_mul]
  · simp only [extId_eq_map_psi, ← Ideal.map_sup, h, Ideal.map_top]
  · rw [extId_eq_map_psi, Ideal.map_span, Set.image_singleton, map_natCast]
  · refine ⟨w.comap st hsurj, fun a b hab => ?_⟩
    have : b = st a := RingOfIntegers.ext hab
    subst this
    show _ ↔ st (st a) ∈ w.asIdeal
    rw [hst2]
  · intro a b hab
    exact (h b a (by rw [hab, star_star])).symm
  · refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    have e : (b : I.E) = star (st b : I.E) := by rw [hst, star_star]
    exact (h (st b) b e).symm.trans (h' (st b) b e)
  · have key : (⟨_, hsig z z.2⟩ : IntAf I.F I.E) ∈ extId I w'.asIdeal := by
      unfold extId at hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, e⟩ := hx
        refine Ideal.subset_span ⟨st a, (h a (st a) (hst a)).1 ha, ?_⟩
        show Formalism.UG.sigR I.cm.sig (Af I.F) x = _
        rw [e]
        rfl
      | zero =>
        convert (extId I w'.asIdeal).zero_mem using 1
        exact Subtype.ext (map_zero _)
      | add x y _ _ hx hy =>
        convert add_mem hx hy using 1
        exact Subtype.ext (map_add _ _ _)
      | smul a x _ hx =>
        convert Ideal.mul_mem_left _ ⟨_, hsig a a.2⟩ hx using 1
        exact Subtype.ext (map_mul _ _ _)
    exact ⟨_, key, rfl⟩

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbits
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordAmp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ} {P : LocNG.FPair H r} {S : Frames M.L r k}

private lemma tsum_transversal_eq_tsum_orbits_lemma {T X G R : Type*} [Group G] [MulAction G X]
    [AddCommMonoid R] [TopologicalSpace R] (St : Subgroup G)
    (rel : T → T → Prop) (A B : Set T) (hB : _root_.Formalism.MainNotions.S.LocNG.IsTransv rel A B) (ℓ : T → X) (term : X → Prop)
    (p : T → Prop) (Q : X → Prop)
    (hterm : ∀ t ∈ A, term (ℓ t)) (hsurj : ∀ Λ, term Λ → ∃ t ∈ A, ℓ t = Λ)
    (hrel : ∀ t t', rel t t' ↔ ∃ g ∈ St, ℓ t' = g • ℓ t)
    (hinv : ∀ Λ, term Λ → ∀ g ∈ St, term (g • Λ))
    (hpQ : ∀ t ∈ A, (p t ↔ Q (ℓ t))) (hQ : ∀ Λ, term Λ → ∀ g ∈ St, Q Λ → Q (g • Λ))
    (f : X → R) (hf : ∀ Λ, term Λ → ∀ g ∈ St, f (g • Λ) = f Λ)
    (val : T → R) (hval : ∀ t ∈ A, val t = f (ℓ t)) :
    ∑' t : {t // t ∈ B ∧ p t}, val t.1
      = ∑' o : MulAction.orbitRel.Quotient St X,
          if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0 := by
  obtain ⟨hBA, hcover, huniq⟩ := hB
  have key : ∀ Λ : X, ∃ g ∈ St,
      Quotient.out (Quotient.mk (MulAction.orbitRel St X) Λ) = g • Λ := fun Λ => by
    obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.mk_out (s := MulAction.orbitRel St X) Λ
    exact ⟨g, hg, hgx.symm⟩
  let toFun : {t // t ∈ B ∧ p t} →
      ↥{o : MulAction.orbitRel.Quotient St X | term (Quotient.out o) ∧ Q (Quotient.out o)} :=
    fun t => ⟨Quotient.mk _ (ℓ t.1), by
      obtain ⟨g, hg, he⟩ := key (ℓ t.1)
      have h1 := hterm _ (hBA t.2.1)
      show term (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
        ∧ Q (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
      rw [he]
      exact ⟨hinv _ h1 g hg, hQ _ h1 g hg ((hpQ _ (hBA t.2.1)).1 t.2.2)⟩⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ heq
      have h2 : Quotient.mk (MulAction.orbitRel St X) (ℓ t) = Quotient.mk _ (ℓ t') :=
        congrArg Subtype.val heq
      obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.exact h2
      have : rel t' t := (hrel t' t).2 ⟨g, hg, hgx.symm⟩
      exact Subtype.ext (huniq _ ht'.1 _ ht.1 this).symm
    · rintro ⟨o, ho⟩
      obtain ⟨t0, ht0A, ht0⟩ := hsurj _ ho.1
      obtain ⟨y, hyB, hy⟩ := hcover t0 ht0A
      obtain ⟨g, hg, hgy⟩ := (hrel y t0).1 hy
      have hyA := hBA hyB
      have hQy : Q (ℓ y) := by
        have := hQ (ℓ t0) (hterm _ ht0A) g⁻¹ (inv_mem hg) (by rw [ht0]; exact ho.2)
        rwa [hgy, inv_smul_smul] at this
      refine ⟨⟨y, hyB, (hpQ y hyA).2 hQy⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (ℓ y) = o
      rw [← Quotient.out_eq o, ← ht0, hgy]
      exact Quotient.sound ⟨⟨g⁻¹, inv_mem hg⟩, inv_smul_smul g _⟩
  let e := Equiv.ofBijective toFun hbij
  have hR : (∑' o : MulAction.orbitRel.Quotient St X,
      if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0)
      = ∑' o : ↥{o : MulAction.orbitRel.Quotient St X |
          term (Quotient.out o) ∧ Q (Quotient.out o)}, f (Quotient.out o.1) := by
    refine Eq.trans ?_ (tsum_subtype _ (fun o => f (Quotient.out o))).symm
    refine tsum_congr fun o => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hR, ← e.tsum_eq]
  refine tsum_congr fun t => ?_
  show val t.1 = f (Quotient.out (Quotient.mk _ (ℓ t.1)))
  obtain ⟨g, hg, he⟩ := key (ℓ t.1)
  rw [he, hf _ (hterm _ (hBA t.2.1)) g hg, hval _ (hBA t.2.1)]

theorem _root_.GlobalTheory.HL.CoordAmp.sums_eq (hM : M.OK) (c : _root_.GlobalTheory.HL.Coord P S)
    (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P)
    (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : Submodule M.L.O S.V → Prop)
    (hpQ : ∀ t, _root_.Formalism.MainNotions.S.LocNG.IsTermOver P d t → (p t ↔ Q (c.lat t.abelian₂)))
    (hQ : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St, Q Λ → Q (h • Λ)) :
    _root_.Formalism.MainNotions.S.LocNG.amp R d p = S.amp (c.dat d) Q ∧
      (∑' t : {t // t ∈ R.RT d ∧ p t}, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) Q := by
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨-, -, hbij, hlatg, -, hmu⟩ := _root_.GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, -, hSt, -⟩ := _root_.GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨hcorr, hex, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hB := R.hRT d
  have hrel : ∀ t t', _root_.Formalism.MainNotions.S.LocNG.TRel P t t' ↔ ∃ g ∈ S.St,
      c.lat t'.abelian₂ = g • c.lat t.abelian₂ := by
    intro t t'
    unfold _root_.Formalism.MainNotions.S.LocNG.TRel
    constructor
    · rintro ⟨s, hs, he⟩
      exact ⟨c.grp s, (hSt s).1 hs, by rw [he, hlatg]⟩
    · rintro ⟨g, hg, he⟩
      refine ⟨c.grp.symm g, (hSt _).2 (by simpa using hg), hbij.1 ?_⟩
      rw [hlatg, MulEquiv.apply_symm_apply, he]
  have hterm_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St, S.IsTerm (c.dat d) (g • Λ) :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).1
  have hom_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.om (c.dat d) (g • Λ) = S.om (c.dat d) Λ :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).2.1
  have hmu_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.mu (g • Λ) = S.mu Λ :=
    fun Λ h g hg => ((_root_.GlobalTheory.HL.volSt M.L r k S).1 Λ
      (_root_.GlobalTheory.HL.TermBasic.term_basic M.L r k S _ Λ h).1.1).2.2 g hg
  constructor
  · unfold _root_.Formalism.MainNotions.S.LocNG.amp _root_.GlobalTheory.HL.Frames.amp
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => (S.mu Λ : ℂ) * S.om (c.dat d) Λ)
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg, hom_inv Λ h g hg])
      (fun t => (_root_.Formalism.MainNotions.S.LocNG.mu P t : ℂ) * _root_.Formalism.MainNotions.S.LocNG.om P t)
      (fun t ht => by simp only [hmu t, (hcorr d t ht).2.1])
  · unfold _root_.GlobalTheory.HL.Frames.mass
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => ENNReal.ofReal (S.mu Λ))
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg])
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t))
      (fun t _ => by simp only [hmu t])

theorem _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P),
    _root_.Formalism.MainNotions.S.LocNG.amp R d (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H)) = S.amp (c.dat d)
        (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t) = S.amp (c.dat d)
        (S.BBzero (c.dat d)) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧
      (∑' t : R.RT d, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) (fun _ => True) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hcorr, -, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hBB : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St,
        (S.BBzero (c.dat d) (h • Λ)
          ↔ S.BBzero (c.dat d) Λ) :=
    fun Λ hΛ h hh => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ hΛ h hh).2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => (hcorr d t ht).2.2)
      (fun Λ hΛ h hh hq => by rwa [hBB Λ hΛ h hh])).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => by rw [(hcorr d t ht).2.2, not_not])
      (fun Λ hΛ h hh hq => (hBB Λ hΛ h hh).2 hq)).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).1
  · rw [← (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).2]
    exact ((Equiv.subtypeEquivRight (fun t => by simp)).tsum_eq
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))).symm

end GlobalTheory.HL.CoordAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbitsStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePair_amplitude_mass_reps_eq_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d : LocNG.Datum P), LocNG.amp R d (LocNG.BBne (H := H)) = S.amp (c.dat d) (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧ LocNG.amp R d (fun t => ¬ LocNG.BBne (H := H) t) = S.amp (c.dat d) (S.BBzero (c.dat d)) ∧ LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧ (∑' t : R.RT d, ENNReal.ofReal (LocNG.mu P t.1)) = S.mass (c.dat d) (fun _ => True) := by
  first | exact @GlobalTheory.HL.CoordAmp.amp_mass_eq | exact GlobalTheory.HL.CoordAmp.amp_mass_eq | (intros; apply GlobalTheory.HL.CoordAmp.amp_mass_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumEqOfSameLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumEqOfSameLattice
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LatUniq

theorem datum_of_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → d = d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP d d' τ τ' hτ hτ' hL
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  have h1 := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d τ hτ).1
  have h2 := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d' τ' hτ').1
  rw [← hL] at h2
  have e := (GlobalTheory.HL.TermBasic.term_basic M.L r k S (c.dat d) (c.lat τ.abelian₂) h1).2.2.2.2.2.2.2 (c.dat d') h2
  exact ((GlobalTheory.HL.CoordDatum.transport M hM H r k P S c).1 e).symm

end GlobalTheory.HL.LatUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumEqOfSameLatticeStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDatum_eq_of_same_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → d = d' := by
  first | exact @GlobalTheory.HL.LatUniq.datum_of_lattice | exact GlobalTheory.HL.LatUniq.datum_of_lattice | (intros; apply GlobalTheory.HL.LatUniq.datum_of_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbits
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSum

theorem tsum_reps_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0
  obtain ⟨-, -, hrel, -, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, -, hex⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  refine ⟨κ, hκ0, fun φ hφ hφ0 => ?_⟩

  have hmove : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm δ Λ) → ∃ Λ, S.IsTerm (h • δ) Λ := by
    rintro h hh δ ⟨Λ, hΛ⟩
    exact ⟨h • Λ, (GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh).1⟩

  have hψ0 : ∀ δ : S.Datum, (¬ ∃ Λ, S.IsTerm δ Λ) → ENNReal.ofReal (S.nu δ) * φ δ = 0 := by
    intro δ hδ
    rw [hφ0 δ hδ, mul_zero]
  have hterm : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1) =
      ENNReal.ofReal κ * (ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) := by
    intro d
    by_cases hd : ∃ Λ, S.IsTerm (c.dat d.1) Λ
    · obtain ⟨Λ, hΛ⟩ := hd
      rw [hκ d.1 Λ hΛ, ENNReal.ofReal_mul hκ0, mul_assoc]
    · rw [hφ0 _ hd, mul_zero, mul_zero, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1

  let A : Set R.RD := {a | ∃ Λ, S.IsTerm (c.dat a.1) Λ}
  have h1 : ∑' a : A, ENNReal.ofReal (S.nu (c.dat a.1.1)) * φ (c.dat a.1.1) =
      ∑' d : R.RD, ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1) := by
    refine tsum_subtype_eq_of_support_subset (f := fun d : R.RD => ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) ?_
    intro a ha
    by_contra hn
    exact ha (hψ0 _ hn)
  have hT : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ Λ, S.IsTerm (g • x) Λ :=
    fun g x hx => hmove g g.2 x hx
  have hι : ∀ a : A, ∃ Λ, S.IsTerm (c.dat a.1.1) Λ := fun a => a.2
  have hsurj : ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ a : A, ∃ g : S.H0, g • c.dat a.1.1 = x := by
    intro x hx
    obtain ⟨Λ, hΛ⟩ := hx
    obtain ⟨d, rfl⟩ := hex x Λ hΛ
    obtain ⟨y, hyR, hy⟩ := R.hRD.2.1 d (Set.mem_univ d)
    obtain ⟨h, hh, hhy⟩ := (hrel y d).1 hy
    have hTy : ∃ Λ, S.IsTerm (c.dat y) Λ := by
      have h' := hmove h⁻¹ (S.H0.inv_mem hh) _ ⟨Λ, hΛ⟩
      rwa [← hhy, inv_smul_smul] at h'
    exact ⟨⟨⟨y, hyR⟩, hTy⟩, ⟨h, hh⟩, hhy⟩
  have hinj : ∀ a b : A, (∃ g : S.H0, g • c.dat a.1.1 = c.dat b.1.1) → a = b := by
    rintro a b ⟨g, hg⟩
    have hr : LocNG.Datum.Rel a.1.1 b.1.1 := (hrel _ _).2 ⟨g, g.2, hg⟩
    exact Subtype.ext (Subtype.ext (R.hRD.2.2 _ a.1.2 _ b.1.2 hr))
  have hinv : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) →
      ENNReal.ofReal (S.nu (g • x)) * φ (g • x) = ENNReal.ofReal (S.nu x) * φ x := by
    rintro g x ⟨Λ, hΛ⟩
    show ENNReal.ofReal (S.nu ((g : S.GLV) • x)) * φ ((g : S.GLV) • x) = _
    rw [(GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S x Λ hΛ).2 g g.2, hφ g g.2 x]
  have h2 := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.H0) (X := S.Datum) (A := A)
    (fun a => c.dat a.1.1) (fun x => ∃ Λ, S.IsTerm x Λ) hT hι hsurj hinj).2
    (fun x => ENNReal.ofReal (S.nu x) * φ x) hinv
  rw [← h1, h2]
  show _ = ∑' o : MulAction.orbitRel.Quotient S.H0 S.Datum, ENNReal.ofReal (S.nu o.out) * φ o.out
  refine tsum_congr fun o => ?_
  split_ifs with ho
  · rfl
  · exact (hψ0 _ ho).symm

end GlobalTheory.HL.CoordSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbitsStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePair_tsum_reps_eq_const_mul_orbits : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  first | exact @GlobalTheory.HL.CoordSum.tsum_reps_eq | exact GlobalTheory.HL.CoordSum.tsum_reps_eq | (intros; apply GlobalTheory.HL.CoordSum.tsum_reps_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesDefectOrderShareLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesDefectOrderShareLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DefectShare

lemma tsum_subtype_le {α : Type} (P : α → Prop) (s : Set α) (hs : ∀ a, P a → a ∈ s) (f : α → ℝ≥0∞)
    (c N : ℝ≥0∞) (hf : ∀ a, P a → f a ≤ c) (hN : (s.encard : ℝ≥0∞) ≤ N) :
    ∑' a : {a // P a}, f a ≤ N * c := by
  calc ∑' a : {a // P a}, f a ≤ ∑' _ : ({a | P a} : Set α), c :=
        ENNReal.tsum_le_tsum fun a => hf a.1 a.2
    _ = (({a | P a} : Set α).encard : ℝ≥0∞) * c := ENNReal.tsum_set_const _ _
    _ ≤ N * c := by
        gcongr
        refine le_trans ?_ hN
        exact_mod_cast Set.encard_le_encard (fun a ha => hs a ha)

theorem share_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (C : Set S.FrP) (hC : S.IsCls C) (β : ℕ) (_hβ : 1 ≤ β) :
    (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤
      ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) *
        S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  by_cases h : ∃ d Λ, S.IsTerm d Λ ∧ S.Fr d Λ = C
  swap
  · have h0 : (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) = 0 := by
      unfold Frames.sumData
      refine ENNReal.tsum_eq_zero.2 fun o => ?_
      have : ({Λ | S.IsTerm o.out Λ ∧ S.be o.out Λ = β ∧ S.Fr o.out Λ = C} :
          Set (Submodule L.O S.V)) = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, h3⟩
        exact h ⟨_, _, h1, h3⟩
      simp [Frames.nT, this]
    rw [h0]
    exact zero_le
  obtain ⟨d, Λ, hT, hFr⟩ := h
  obtain ⟨hSD, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have ha : 0 ≤ S.a := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).1
  have hp : (S.fr d Λ, S.fr' d Λ) ∈ C := by
    rw [← hFr]
    exact (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDualHermitianLattice_mass_of_trace L r k S (by omega) ⟨Λ, hSD⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S C hC _ hp
  have h3 := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC _ hp ha
  have hlow : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.Mof (S.fr d Λ) (S.fr' d Λ)) := by
    have := (hU C hC _ hp _ le_rfl (fun x hx => (hM hx).2)
      (fun x hx y hy => (hSD.2 y).2 (hM hy).1 x (hM hx).1)).1
    simpa using this
  rw [h2]
  refine (h1 fun n => n = β).trans ?_
  refine (tsum_subtype_le _ _ (fun Mh hMh => ?_) S.massSig
    (ENNReal.ofReal (2 * κ * ((β : ℝ) ^ (k - 1))⁻¹)) _ (fun Mh hMh => ?_) h3).trans ?_
  · exact ⟨hMh.1, hMh.2.1, hMh.2.2.1⟩
  · have := (hU C hC _ hp Mh hMh.1 hMh.2.1 hMh.2.2.1).2
    rw [hMh.2.2.2] at this
    exact this
  · refine le_trans (le_of_eq ?_) (mul_le_mul_right hlow _)
    have hz : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = (S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2)) := by
      rw [← zpow_natCast]
      congr 1
      push_cast
      rw [Int.toNat_of_nonneg ha]
    have hq : (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) =
        ENNReal.ofReal ((S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    rw [hz, hq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

end GlobalTheory.HL.DefectShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesDefectOrderShareLeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_defectOrder_share_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ C, S.IsCls C → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) * S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  first | exact @GlobalTheory.HL.DefectShare.share_le | exact GlobalTheory.HL.DefectShare.share_le | (intros; apply GlobalTheory.HL.DefectShare.share_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DefectShare

theorem mass_defect_order_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β hβ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ
  swap
  · have h0 : (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) = 0 := by
      have : ∀ d Λ, ¬ S.IsTerm d Λ := fun d Λ h => hex ⟨d, Λ, h⟩
      simp [Frames.sumData, Frames.mass, this]
    rw [h0]; exact zero_le
  obtain ⟨d0, Λ0, h0⟩ := hex
  obtain ⟨-, -, -, hq, -⟩ := GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d0 Λ0 h0
  have hconst : 4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹ ≤
      (4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹ := by
    have e : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = ((S.q : ℝ) ^ S.a) ^ (4 * (r + 1)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e]
    have hn : (0 : ℝ) ≤ (S.q : ℝ) ^ S.a := zpow_nonneg (Nat.cast_nonneg _) _
    gcongr
  have s1 := (GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun d Λ => S.be d Λ = β) (fun h hh d Λ hT hP => by
    have := (GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.1
    exact this.trans hP)).1
  have s2 := (GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)).1
  unfold Frames.nn
  rw [s1, s2]
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with hC
  · rw [mul_left_comm]
    refine mul_le_mul_right ?_ _
    refine (GlobalTheory.T.hermitianFrames_defectOrder_share_le L r k S hk _ hC.1 β hβ).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) ?_
    unfold Frames.sumData
    refine ENNReal.tsum_le_tsum fun o' => mul_le_mul' le_rfl ?_
    unfold Frames.nT
    exact ENat.toENNReal_le.mpr (Set.encard_le_encard fun Λ h => ⟨h.1, trivial, h.2.2⟩)
  · exact zero_le

end GlobalTheory.DefectShare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumData_mass_be_eq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  first | exact @GlobalTheory.DefectShare.mass_defect_order_le | exact GlobalTheory.DefectShare.mass_defect_order_le | (intros; apply GlobalTheory.DefectShare.mass_defect_order_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacter
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MoveTerm
open GlobalTheory.HL.Eichler

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem cj_mem_O {c : E} (hc : c ∈ L.O) : L.cj c ∈ L.O := by
  rw [L.O_def] at hc ⊢
  exact hc.map (L.cj.toAlgHom.restrictScalars 𝒪[F])

theorem top_coord (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (w : S.GLV) (hw : w ∈ S.Nof g) (j : Fin r) (x : S.V) (hx : x ∈ S.spanTo g (j + 1))
    (al : Fin (r + 1) → E) (e : x = ∑ i, al i • w (g i)) :
    S.h x (gs j) = al j.castSucc := by
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf] at hw
  obtain ⟨⟨-, h1⟩, -⟩ := hw
  have e' : x = w (∑ i, al i • g i) := by simp [e]
  have hz : ∑ i, al i • g i ∈ S.spanTo g (j + 1) := ((h1 j).1 _).1 (e' ▸ hx)
  have hB := (h1 j).2 _ hz
  have hK : S.spanTo g j ≤ LinearMap.ker (FramePsi.pairL L S.Hm (gs j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    change hf L S.Hm (g i) (gs j) = 0
    rw [hd, if_neg]
    rintro rfl
    simp at hi
  have h2 := LinearMap.mem_ker.1 (hK hB)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e', map_sub, map_sum, sub_eq_zero] at h2
  have h3 : ∀ i, FramePsi.pairL L S.Hm (gs j) (al i • g i) = if i = j.castSucc then al i else 0 := by
    intro i
    rw [map_smul]
    change al i * hf L S.Hm (g i) (gs j) = _
    rw [hd]
    split_ifs <;> simp
  simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  exact h2

theorem psi'_eq_one (n : S.GLV) (hn : ∀ v ∈ perp L S.Hm S.X', n v = v) : S.psi' n = 1 := by
  have h : ∀ j, S.coef S.f' S.es' n j = 0 := by
    intro j
    have hp : S.f' j.succ ∈ perp L S.Hm S.X' := by
      refine FramePsi.hf_span_right L S.Hm _ _ ?_
      rintro _ ⟨i, hi, rfl⟩
      rw [S.gram', if_neg]
      rintro ⟨-, rfl⟩
      simp at hi
    rw [Frames.coef, hn _ hp, Frames.h, S.dual', if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [Frames.psi', Frames.psiOf, h]

theorem perp_left {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm A := fun y hy => hu y (Submodule.mem_sup_left hy)

theorem perp_right {A B : Submodule E S.V} {u : S.V} (hu : u ∈ perp L S.Hm (A ⊔ B)) :
    u ∈ perp L S.Hm B := fun y hy => hu y (Submodule.mem_sup_right hy)

end

theorem move_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s ∧ S.IsTerm d Λ₁ ∧ S.moved Λ₁ x (-u) (L.cj s) = Λ ∧ (S.InFF β (j + 1) βJ d Λ₁ → S.IsMove (j + 1) d Λ₁ x x' (-u) (L.cj s)) ∧ ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → S.om d Λ₁ = S.om d Λ * L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', e₀, e₀i, e₀', f'', hset, hW⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨t1, t2, -, -, -, -, -, hux, -, -, -⟩ := GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hFF x x' u s hM
  obtain ⟨hT₁, hY⟩ := GlobalTheory.T.hermitianMove_preserves_frameLattice_levels L r k S j β βJ d Λ hT hFF x x' u s hM _ hset
  obtain ⟨hx, hx', hth, hlev, hu, hup, ⟨c, hc, hsc⟩, hs⟩ := hM
  have hb : x + x' ∈ S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1) := Submodule.add_mem_sup hx hx'
  have hmem : ∀ v, v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ eich L S.Hm x u s v ∈ Λ := fun v =>
    Set.ext_iff.1 hset v
  refine ⟨n₀⁻¹ • Λ, hset, hT₁, ?_, fun _ => ⟨hx, hx', ?_, ?_, ?_, (perp L S.Hm _).neg_mem hup, ?_, ?_⟩,
    fun al al' ex ex' => ?_⟩
  · ext v
    change eich L S.Hm x (-u) (L.cj s) v ∈ (n₀⁻¹ • Λ : Submodule L.O S.V) ↔ v ∈ Λ
    rw [hmem, ← e₀, ← e₀i]
    rw [show n₀ (n₀⁻¹ v) = v from n₀.apply_symm_apply v]
  · obtain ⟨y, hy, e⟩ := hth
    refine ⟨y, (hY y ?_).1 hy, e⟩
    have : y = algebraMap F E S.th⁻¹ • (x + x') := by
      rw [e, smul_smul, WitIndep.th_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hb
  · rw [(hY _ hb).2.2, hlev]
  · refine Submodule.neg_mem _ ((hmem u).2 ?_)
    have : eich L S.Hm x u s u = u + s • x + L.cj s • x := by
      have h1 : hf L S.Hm u x = 0 := hux
      have h2 : hf L S.Hm u u = s + L.cj s := hs.symm
      rw [eich, h1, h2]
      module
    rw [this]
    exact Λ.add_mem (Λ.add_mem hu t1) t2
  · exact ⟨L.cj c, cj_mem_O hc, by rw [hsc, map_mul, AlgEquiv.commutes]⟩
  · rw [L.cj_cj, Frames.h, hf_neg_l, hf_neg_r, neg_neg, add_comm]
    exact hs
  · have K := (TermBasic.term_basic L r k S d Λ hT).2.1
    have hw := K.2.2.1
    have hw' := K.2.2.2.1
    obtain ⟨p1, p2, p3, p4⟩ := FramePsi.psi_unitary_character L r k S
    obtain ⟨m, -, em, -, -, pm⟩ := EichlerUnip.eichler_mem_unip L r k S S.f S.es (.inl ⟨rfl, rfl⟩) j x u s
      hx (perp_left S hup) hs
    obtain ⟨m', -, em', -, -, pm'⟩ := EichlerUnip.eichler_mem_unip L r k S S.f' S.es' (.inr ⟨rfl, rfl⟩)
      j x' u s hx' (perp_right S hup) hs
    obtain rfl : m = n₀ := LinearEquiv.ext fun v => (em v).trans (e₀ v).symm
    obtain rfl : m' = n₀' := LinearEquiv.ext fun v => (em' v).trans (e₀' v).symm
    have q := pm _ hw
    have q' := pm' _ hw'
    rw [top_coord S S.f S.es S.dual _ hw j x hx al ex] at q
    rw [top_coord S S.f' S.es' S.dual' _ hw' j x' hx' al' ex'] at q'
    have a1 := p1 m hn₀ _ (mul_mem (inv_mem hn₀) hw)
    rw [mul_inv_cancel_left] at a1
    have a2 := p2 _ (mul_mem hn'' hn₀') _ hw'
    rw [p2 _ hn'' _ hn₀', psi'_eq_one S n'' f'', one_mul] at a2
    have z1 : S.psi m ≠ 0 := fun h => by simpa [h] using (p3 m).1
    have z2 : S.psi' m' ≠ 0 := fun h => by simpa [h] using (p3 m').2
    have hchi : L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ +
        al' j.castSucc • S.fr' d Λ j.succ) u)) = (S.psi m * S.psi' m')⁻¹ := by
      rw [AddChar.map_neg_eq_inv]
      congr 1
      change _ = S.psiOf S.f S.es m * S.psiOf S.f' S.es' m'
      rw [q, q', ← AddChar.map_add_eq_mul, Frames.h, hf_add_l, hf_smul_l, hf_smul_l, mul_add]
      rfl
    rw [(WitIndep.witness_independence L r k S _ _ _ _ hW).1, hchi, a2, Frames.om, a1]
    field_simp

end GlobalTheory.HL.MoveTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacterStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s ∧ S.IsTerm d Λ₁ ∧ S.moved Λ₁ x (-u) (L.cj s) = Λ ∧ (S.InFF β (j + 1) βJ d Λ₁ → S.IsMove (j + 1) d Λ₁ x x' (-u) (L.cj s)) ∧ ∀ al al' : Fin (r + 1) → E, x = ∑ i, al i • S.fr d Λ i → x' = ∑ i, al' i • S.fr' d Λ i → S.om d Λ₁ = S.om d Λ * L.psi0 (-(algebraMap F E S.th⁻¹ * S.h (al j.castSucc • S.fr d Λ j.succ + al' j.castSucc • S.fr' d Λ j.succ) u)) := by
  first | exact @GlobalTheory.HL.MoveTerm.move_term | exact GlobalTheory.HL.MoveTerm.move_term | (intros; apply GlobalTheory.HL.MoveTerm.move_term <;> assumption)
end
end
