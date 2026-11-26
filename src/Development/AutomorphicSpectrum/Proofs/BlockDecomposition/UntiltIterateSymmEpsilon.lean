module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import GroundTheory.AutomorphicForms.GL2.GodementSection
public import GroundTheory.GlobalFields.TateThesis.TateMain

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltIterateSymmEpsilon
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsRootProof

variable {l : ℕ} [hl : Fact l.Prime]

theorem iterate_symm_ofCompatible (y : ℕ → OC l) (hy : ∀ k, y (k + 1) ^ l = y k) (n : ℕ) :
    ((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (IsPerfectoidField.ofCompatible l y hy) =
      IsPerfectoidField.ofCompatible l (fun k => y (k + n))
        (fun k => by rw [show k + 1 + n = (k + n) + 1 by omega]; exact hy (k + n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, AInf.frobeniusEquiv_symm_ofCompatible]
    congr 1
    funext k
    exact congrArg y (by omega)

theorem iterate_symm_pow (x : Ob l) (n : ℕ) :
    (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) x) ^ l ^ n = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

theorem untilt_iterate_symm_epsilon (n : ℕ) :
    PreTilt.untilt (((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l)) = rootSeqInt l n := by
  rw [epsilon, iterate_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible, zero_add]

theorem sharp_s_eq_oC_untilt (A : PAlg l) (x : Ob l) : A.sharp (A.s x) = A.oC (PreTilt.untilt x) := by
  have h : WittVector.teichmuller l (A.s x) = A.sW (WittVector.teichmuller l x) :=
    (WittVector.map_teichmuller l A.s x).symm
  change A.th (WittVector.teichmuller l (A.s x)) = _
  rw [h, ← PAlg.oC_theta0]
  exact congrArg A.oC (WittVector.fontaineTheta_teichmuller _)

theorem epsRoot : CrystallineSemistableComparison.E.EpsRoot := by
  intro l _ n
  exact ⟨((_root_.frobeniusEquiv (Ob l) l).symm^[n]) (epsilon l), iterate_symm_pow _ n, fun A => by
    rw [sharp_s_eq_oC_untilt, untilt_iterate_symm_epsilon]⟩

end GlobalTheory.CompanionTheory.EpsRootProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisZeroImageDividedPower
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogEpsP

variable {l : ℕ} [Fact l.Prime]

theorem cris_eq_zero (A : PAlg l) (n : ℕ) {y : Acris l}
    (hy : y ∈ Ideal.span {(l : Acris l)} ^ n) : A.cris n y = 0 := by
  rw [Ideal.span_singleton_pow] at hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul, map_pow, map_natCast, PAlg.pow_l_acr, mul_zero]

theorem cris_log (A : PAlg l) (n : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.log hx) = ∑ k ∈ Finset.range (l * n), A.cris n (ACris.logTerm hx k) := by
  obtain ⟨N, hN⟩ := ACris.isAdicSum_log hx n
  have h2 := cris_eq_zero A n (hN (max N (l * n)) (le_max_left _ _))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_eq_zero, map_sum,
    ← Finset.sum_range_add_sum_Ico _ (le_max_right N (l * n)),
    Finset.sum_eq_zero (s := Finset.Ico (l * n) (max N (l * n))) (fun k hk =>
      cris_eq_zero A n (ACris.logTerm_mem hx (Finset.mem_Ico.1 hk).1)), add_zero] at h2
  exact h2

theorem cris_logTerm (A : PAlg l) (n k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.logTerm hx k) =
      (-1) ^ k * (k.factorial : A.Acr n) * A.mkAcr n (A.cris0 (ACris.dpowZero hx (k + 1))) := by
  rw [ACris.logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    PAlg.cris_of, ACris.logTermZero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

theorem acrisZero_image_divided_power (A : PAlg l) (k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    (A.cris0 (ACris.dpowZero hx k)).1 = dpw k (WittVector.map A.s x) :=
  awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) x

theorem map_mu (A : PAlg l) (e : Ob l) :
    WittVector.map A.s (AInf.mu (K := ℂ_[l]) (p := l) e) = WittVector.teichmuller l (A.s e) - 1 := by
  rw [AInf.mu, map_sub, map_one, WittVector.map_teichmuller]

end GlobalTheory.CompanionTheory.LogEpsP

theorem GlobalTheory.CompanionTheory.LogEpsP.logEps : CrystallineSemistableComparison.E.LogEps := by
  intro l _ A n
  refine ⟨fun k => A.cris0 (ACris.dpowZero (ACris.mu_mem_ker (untilt_epsilon (p := l))) k), fun k => ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LogEpsP.acrisZero_image_divided_power, GlobalTheory.CompanionTheory.LogEpsP.map_mu]
  · rw [ACris.periodT, GlobalTheory.CompanionTheory.LogEpsP.cris_log]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.CompanionTheory.LogEpsP.cris_logTerm A n k _
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwUgCompAlgebraMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwUg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem twUg_map (σ : Gal(PadicAlgCl l/K)) {A B : PAlg l} (f : A ⟶ B) :
    (twUg σ B).comp (PAlg.mapUg (PAlg.twMap σ f)) = (PAlg.mapUg f).comp (twUg σ A) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (l : (PAlg.tw σ A).U)) (RingHom.ext fun x => ?_)
  change twUg σ B (PAlg.mapUg (PAlg.twMap σ f) (algebraMap _ _ x)) = PAlg.mapUg f (twUg σ A (algebraMap _ _ x))
  rw [PAlg.mapUg_algebraMap, twUg_algebraMap, twUg_algebraMap, PAlg.mapUg_algebraMap, PAlg.twU_mapU]

theorem twUg_cToUg (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : ℂ_[l]) :
    twUg σ A ((PAlg.tw σ A).cToUg x) = A.cToUg (galCp σ x) := by
  have h : ((twUg σ A).comp (PAlg.tw σ A).cToUg).comp
        ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) =
      (A.cToUg.comp (galCp σ : ℂ_[l] →+* ℂ_[l])).comp ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l : Localization.Away (l : OC l) →+* ℂ_[l])) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : OC l)) (RingHom.ext fun y => ?_)
    have e : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y) = (y : ℂ_[l]) :=
      (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).commutes y
    have e2 : ((galOC σ y : OC l) : ℂ_[l]) = galCp σ (y : ℂ_[l]) := rfl
    change twUg σ A ((PAlg.tw σ A).cToUg ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y))) =
      A.cToUg (galCp σ ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l) (algebraMap _ _ y)))
    rw [e, PAlg.cToUg_coe, twUg_algebraMap, PAlg.twU_oC, ← e2, PAlg.cToUg_coe]
  obtain ⟨y, rfl⟩ := (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).surjective x
  exact RingHom.congr_fun h y

theorem twUg_kb (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (x : PadicAlgCl l) :
    twUg σ A (kb (PAlg.tw σ A) x) = kb A (σ x) := by
  change twUg σ A ((PAlg.tw σ A).cToUg (clToC l x)) = A.cToUg (clToC l (σ x))
  rw [twUg_cToUg]
  exact congrArg A.cToUg (galCp_coe σ x)

theorem twUg_comp_algebraMap (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) :
    ((twUg σ A).comp (algebraMap (PAlg.tw σ A).U (PAlg.tw σ A).Ug)).comp (PAlg.twUEquiv σ A).symm.toRingHom =
      algebraMap A.U A.Ug := by
  refine RingHom.ext fun x => ?_
  change twUg σ A (algebraMap _ _ ((PAlg.twUEquiv σ A).symm x)) = algebraMap A.U A.Ug x
  rw [twUg_algebraMap]
  exact congrArg (algebraMap A.U A.Ug) ((PAlg.twUEquiv σ A).apply_symm_apply x)

theorem geomPt_galMap (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (y : M.P.obj A) :
    geomPt M A y ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q σ =
      Spec.map (CommRingCat.ofHom (twUg σ A)) ≫
        geomPt M (PAlg.tw σ A) ((pxTw M.p (okToOC l K) σ (galOC_okToOC σ)).app A y) := by
  refine gb_ext M ?_ ?_
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst_assoc, geomPt_fst, geomPt_fst]
    change _ = _ ≫ _ ≫ Spec.map (CommRingCat.ofHom (PAlg.twUEquiv σ A).symm.toRingHom) ≫ y.1
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, twUg_comp_algebraMap]
  · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, geomPt_snd, ← Category.assoc, geomPt_snd,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext fun x => twUg_kb σ A x).symm

end GlobalTheory.CompanionTheory.TwUg

theorem GlobalTheory.CompanionTheory.TwUg.twUg_prop : CrystallineSemistableComparison.E.TwUg := fun _ _ _ σ =>
  ⟨fun _ _ f => GlobalTheory.CompanionTheory.TwUg.twUg_map σ f, fun A x => GlobalTheory.CompanionTheory.TwUg.twUg_kb σ A x,
    fun M A y => GlobalTheory.CompanionTheory.TwUg.geomPt_galMap M σ A y⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobIdem
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FrobLc

variable {l : ℕ} [Fact l.Prime]

theorem frob_idem (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) : A.frob e = e := by
  change e ^ l = e
  have h := IsIdempotentElem.pow_succ_eq (l - 1) he
  rwa [Nat.sub_add_cancel (Fact.out : l.Prime).one_lt.le] at h

theorem lcRes_id (A : PAlg l) (n : ℕ) (f : LocallyConstant (SU A) (ZMod (l ^ n))) :
    lcRes (l ^ n) (Spec.map (CommRingCat.ofHom (RingHom.id A.Ug))) f = f := by
  have e : Spec.map (CommRingCat.ofHom (RingHom.id A.Ug)) = 𝟙 (SU A) := by
    change Spec.map (𝟙 (CommRingCat.of A.Ug)) = 𝟙 _
    exact Spec.map_id _
  rw [e]
  ext x
  rfl

theorem phi_lcA (hN : LcNat) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ)
    (f : LocallyConstant (SU A) (ZMod (l ^ n))) : A.phi n (lcA A n f) = lcA A n f := by
  have h := (hN l H A hA n).1 A hA A.frob A.pdOk_frob (RingHom.id A.Ug)
    (fun e he => by rw [frob_idem A e he]; rfl) f
  rw [lcRes_id] at h
  exact h

section Gen
universe w w' u v u' v'
variable {R R' S : Type} [CommRing R] [CommRing R'] [CommRing S] {C : Type u} [Category.{v} C]
  {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'}
  {σ : R →+* R'} {ρ : R' →+* R'}

theorem cls_congr {K : CrystallineSemistableComparison.Cx.{w} R} {k : ℕ} {x y : K.X k} (h : x = y) (hx : K.d k x = 0) (hy : K.d k y = 0) :
    K.cls x hx = K.cls y hy := by
  subst h; rfl

theorem pull_fix (m : Mor F F' σ) (p : Mor F' F' ρ) (j : ℕ) (h : ∀ z, p.pullC j (m.pullC j z) = m.pullC j z)
    (c : CH.H F j) : p.pull j (m.pull j c) = m.pull j c := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact cls_congr (h z) _ _
end Gen

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    Mor (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L (modF (AcrEl M.P n)) (Int.castRingHom (Acris l)) :=
  lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n

theorem phi_lcM (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n j : ℕ)
    (z : Cn (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).L j) :
    (phiMor M.P n).pullC j ((lcM hN H r M n).pullC j z) = (lcM hN H r M n).pullC j z := by
  funext s
  exact phi_lcA hN H _ (s.obj (Fin.last j)).1.property n _

theorem fPhi : CrystallineSemistableComparison.E.FPhi := fun hN l _ H r K M n j x =>
  pull_fix (lcM hN H r M n) (phiMor M.P n) j (phi_lcM hN H r M n j) ((pts H r M (𝟭 _) n).et 0 j x)

end GlobalTheory.CompanionTheory.FrobLc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLogUnique
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.CrisLog

variable {l : ℕ} [Fact l.Prime]

theorem dpw_mul' {R : Type} [CommRing R] (k : ℕ) (c x : WittVector l R) :
    dpw k (c * x) = algebraMap _ (WL l R) c ^ k * dpw k x := by
  simp only [dpw, map_mul, mul_pow]; ring

theorem dpw_idem {R : Type} [CommRing R] (k : ℕ) {e x x' : WittVector l R} (he : IsIdempotentElem e)
    (h : e * x = e * x') :
    algebraMap _ (WL l R) e * dpw (k + 1) x = algebraMap _ (WL l R) e * dpw (k + 1) x' := by
  have key : e * x ^ (k + 1) = e * x' ^ (k + 1) := by
    have hp : e ^ (k + 1) = e := he.pow_succ_eq k
    calc e * x ^ (k + 1) = (e * x) ^ (k + 1) := by rw [mul_pow, hp]
      _ = (e * x') ^ (k + 1) := by rw [h]
      _ = e * x' ^ (k + 1) := by rw [mul_pow, hp]
  have key' := congrArg (algebraMap _ (WL l R)) key
  rw [map_mul, map_mul, map_pow, map_pow] at key'
  simp only [dpw]
  rw [mul_left_comm, key', mul_left_comm]

theorem dpw_mem (A : PAlg l) {x : A.W} (hx : A.th x = 0) (k : ℕ) : dpw k x ∈ A.Acr0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
  rw [dpw_mul']
  exact mul_mem (pow_mem (Subalgebra.algebraMap_mem _ c) k) (A.dpw_xi_mem k)

theorem isLog_exists (A : PAlg l) (n : ℕ) (w : A.W) (hw : A.th w = 1) : ∃ y, IsLog A n w y := by
  have h0 : A.th (w - 1) = 0 := by rw [map_sub, hw, map_one, sub_self]
  exact ⟨_, fun k => ⟨dpw k (w - 1), dpw_mem A h0 k⟩, fun _ => rfl, rfl⟩

theorem isLog_unique (A : PAlg l) (n : ℕ) (w : A.W) (y y' : A.Acr n) (h : IsLog A n w y)
    (h' : IsLog A n w y') : y = y' := by
  obtain ⟨g, hg, rfl⟩ := h
  obtain ⟨g', hg', rfl⟩ := h'
  have e : g = g' := funext fun k => Subtype.ext ((hg k).trans (hg' k).symm)
  rw [e]

theorem isLog_local (A : PAlg l) (n : ℕ) (e w w' : A.W) (y y' : A.Acr n) (he : IsIdempotentElem e)
    (h : e * w = e * w') (hy : IsLog A n w y) (hy' : IsLog A n w' y') :
    A.toAcr n e * y = A.toAcr n e * y' := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have h1 : e * (w - 1) = e * (w' - 1) := by rw [mul_sub, mul_sub, h]
  have h2 : ∀ k, algebraMap A.W A.Acr0 e * g (k + 1) = algebraMap A.W A.Acr0 e * g' (k + 1) := fun k =>
    Subtype.ext (by
      change algebraMap A.W (WL l A.A) e * (g (k + 1)).1 = algebraMap A.W (WL l A.A) e * (g' (k + 1)).1
      rw [hg, hg']
      exact dpw_idem k he h1)
  have h3 : ∀ k, A.toAcr n e * A.mkAcr n (g (k + 1)) = A.toAcr n e * A.mkAcr n (g' (k + 1)) := fun k => by
    have := congrArg (A.mkAcr n) (h2 k)
    rwa [map_mul, map_mul] at this
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h3 k, mul_left_comm]

theorem logEx : CrystallineSemistableComparison.E.LogEx := fun l _ A n =>
  ⟨isLog_exists A n, fun w y y' => isLog_unique A n w y y', fun e w w' y y' => isLog_local A n e w w' y y'⟩

end GlobalTheory.CompanionTheory.CrisLog
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSquare
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FResProof

theorem pull_square {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] {σ : R₀ →+* R₁} {C₀ C₁ : Type 1}
    [Category.{0} C₀] [Category.{0} C₁] {F₀ : C₀ ⥤ ModuleCat.{0} R₀} {F₁ : C₀ ⥤ ModuleCat.{0} R₁}
    {F₀' : C₁ ⥤ ModuleCat.{0} R₀} {F₂ : C₁ ⥤ ModuleCat.{0} R₁} (m₁ : Mor F₀ F₁ σ) (e : Mor F₁ F₂ (RingHom.id R₁))
    (a : Mor F₀ F₀' (RingHom.id R₀)) (m₂ : Mor F₀' F₂ σ) (j : ℕ)
    (h : ∀ z : Cn F₀ j, e.pullC j (m₁.pullC j z) = m₂.pullC j (a.pullC j z)) (y : CH.H F₀ j) :
    e.pull j (m₁.pull j y) = m₂.pull j (a.pull j y) := by
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z))

theorem lcRes_id (q : ℕ) {U : Scheme.{0}} (f : LocallyConstant U (ZMod q)) : lcRes q (𝟙 U) f = f := by
  ext x; rfl

theorem primRes_id {q : ℕ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : primRes (𝟙 U) ζ = ζ :=
  Subtype.ext (by
    change (𝟙 U : U ⟶ U).appTop.hom ζ.1 = ζ.1
    simp)

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def mG (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) :
    Mor (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L (probe H r (G ⋙ CategoryOfElements.π _) n).L
      (RingHom.id ℤ) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem square (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P)
    (n j : ℕ) (y : CH.H (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).L j) :
    (Mor.restrict (modF (AcrEl M.P n)) G).pull j ((lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n).pull j y) =
      (lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j ((mG H r M G n).pull j y) :=
  pull_square (lcMor hN H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n) (Mor.restrict (modF (AcrEl M.P n)) G)
    (mG H r M G n) (lcMor hN H r (G ⋙ CategoryOfElements.π _) n) j (fun z => rfl) y

theorem pull_sch_id (q : ℕ) (i : ℤ) (j : ℕ) (X : Scheme.{0}) (x : Ht q (sch.obj X) j i) :
    pull _ (sch.map (𝟙 X)) _ j x = x := by
  rw [CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]


set_option maxHeartbeats 1000000 in
theorem et_restrict (hE : EtNat) (hg : InGen) (H : RIn l) (r : Roots l) (M : Model l K) {C : Type 1} [Category.{0} C]
    (G : C ⥤ El M.P) (n : ℕ) (i : ℤ) (j : ℕ) (x : Ht (l ^ n) (sch.obj (gb M)) j i) :
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    (mG H r M G n).pull j ((pts H r M (𝟭 _) n).et i j x) = (pts H r M G n).et i j x := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine (hE hg (l ^ n) (El M.P) C (probe H r ((𝟭 (El M.P)) ⋙ CategoryOfElements.π _) n)
    (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M) (gb M) (pts H r M (𝟭 _) n) (pts H r M G n) (𝟙 _)
    (mG H r M G n) (fun c => 𝟙 _) (fun φ => ?_)
    (fun c f => (lcRes_id _ f).symm) (fun c => ?_) i
    (Or.inr fun c => primRes_id _) j x).trans (congrArg _ (pull_sch_id _ _ _ _ x))
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

end GlobalTheory.CompanionTheory.FResProof

theorem GlobalTheory.CompanionTheory.FResProof.fRes : CrystallineSemistableComparison.E.EtNat → CrystallineSemistableComparison.E.FRes := by
  intro hE E hN l _ H r K M C _ G n i j x
  exact (GlobalTheory.CompanionTheory.FResProof.square hN H r M G n j _).trans
    (congrArg _ (GlobalTheory.CompanionTheory.FResProof.et_restrict hE E.gen H r M G n i j x))
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimResZetaX
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.FRootCls

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem rho_succ (r : Roots l) (n : ℕ) : (r.ρ n).1 = (r.ρ (n + 1)).1 ^ l := by
  apply (clToC l).injective
  rw [map_pow, r.hρ, r.hρ, rootSeq_succ_pow]

theorem pow_div_succ (n : ℕ) : l ^ (n + 1) / l ^ n = l := by
  have h : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  rw [pow_succ, Nat.mul_comm, Nat.mul_div_cancel _ h]

theorem zetaX_succ (r : Roots l) (M : Model l K) (n : ℕ) :
    (r.zetaX M n).1 = (r.zetaX M (n + 1)).1 ^ (l ^ (n + 1) / l ^ n) := by
  rw [pow_div_succ]
  change (pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1) =
    ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ (n + 1)).1)) ^ l
  rw [rho_succ r n, map_pow, map_pow]

theorem primRes_zetaX (r : Roots l) (M : Model l K) (n : ℕ) (A : PAlg l) (y : M.P.obj A) :
    primRes (geomPt M A y) (r.zetaX M n) = r.zeta A n := by
  refine Subtype.ext ?_
  change (geomPt M A y).appTop.hom ((pullback.snd _ _ : gb M ⟶ Spec (CommRingCat.of (PadicAlgCl l))).appTop.hom (toΓ _ (r.ρ n).1)) =
    toΓ A.Ug (kb A (r.ρ n).1)
  rw [← toΓ_nat (kb A), ← geomPt_snd M A y, Scheme.Hom.comp_appTop]
  rfl

def lcRing (hL : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) : LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hL l H A hA n).2.1
  map_mul' := (hL l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_one (hL : LcSpec) (hM : MorCup) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) :
    (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0
      (oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))) = oneH (AcrEl M.P n) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) (El M.P) (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n))
    (AcrEl M.P n) (lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n)
    (fun c => lcRing hL H c.1.obj c.1.property n) (fun _ _ => rfl)).1

def rootSys (hO : InOp) (hR : InRed) (hRR : RedRoot) (r : Roots l) (M : Model l K) (i : ℤ) : Hl l (sch.obj (gb M)) (0 : ℕ) i :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  ⟨fun n => rootClass i (r.zetaX M n), fun n =>
    hRR hO hR (l ^ (n + 1)) (l ^ n) (pow_dvd_pow l n.le_succ) i (gb M) (r.zetaX M (n + 1)) (r.zetaX M n) (zetaX_succ r M n)⟩

theorem etVal (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    (pts H r M (𝟭 _) n).et i 0 (rootClass i (r.zetaX M n)) =
      oneH (lcF (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).S (l ^ n)) :=
  hEt hg (l ^ n) (El M.P) (probe H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n) (gb M) (pts H r M (𝟭 _) n)
    (r.zetaX M n) (fun c => primRes_zetaX r M n _ _) i

theorem eM_root (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hg : InGen) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ) (i : ℤ) [NeZero (l ^ n)] :
    eM hN H r M n i 0 (rootClass i (r.zetaX M n)) = oneH (AcrEl M.P n) := by
  refine Eq.trans (congrArg ((lcMor hN H r (𝟭 (El M.P) ⋙ CategoryOfElements.π _) n).pull 0) (etVal hEt hg hN H r M n i)) ?_
  exact lcMor_one hL hM hN H r M n

theorem eM_rootSys (hL : LcSpec) (hM : MorCup) (hEt : EtRoot) (hRR : RedRoot) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) (i : ℤ) (n : ℕ) : eM hN H r M n i 0 ((rootSys E.op E.red hRR r M i).1 n) = oneH (AcrEl M.P n) :=
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  eM_root hL hM hEt E.gen hN H r M n i

theorem froot : CrystallineSemistableComparison.E.EtRoot → CrystallineSemistableComparison.E.RedRoot → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FRoot :=
  fun hEt hRR hM hL E hN _ _ H r _ M i => ⟨rootSys E.op E.red hRR r M i, eM_rootSys hL hM hEt hRR E hN H r M i⟩

end GlobalTheory.CompanionTheory.FRootCls
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumToAcrTeichmuller
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LcNatProof

theorem natCast_val_castHom {R : Type} [CommRing R] (l n : ℕ) [NeZero (l ^ n)] [NeZero (l ^ (n + 1))]
    (h : (l : R) ^ n = 0) (a : ZMod (l ^ (n + 1))) :
    (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : R) = (a.val : R) := by
  have key : (((ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))) a).val : ZMod (l ^ n)) =
      (a.val : ZMod (l ^ n)) := by
    rw [ZMod.natCast_zmod_val, ← map_natCast (ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n))),
      ZMod.natCast_zmod_val]
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 key)
  have e := congrArg (Int.cast : ℤ → R) hc
  push_cast at e
  rw [h, zero_mul, sub_eq_zero] at e
  exact e.symm

variable {l : ℕ} [Fact l.Prime]

theorem sum_toAcr_teichmuller (A : PAlg l) {ι : Type} [Fintype ι] {e : ι → A.A}
    (he : CompleteOrthogonalIdempotents e) (n : ℕ) :
    ∑ a, A.toAcr n (WittVector.teichmuller l (e a)) = 1 := by
  have hO : OrthogonalIdempotents (fun a => (WittVector.teichmuller l (e a) : A.W)) :=
    { idem := fun a => by
        change WittVector.teichmuller l (e a) * WittVector.teichmuller l (e a) = WittVector.teichmuller l (e a)
        rw [← map_mul, (he.idem a).eq]
      ortho := fun i j hij => by
        change WittVector.teichmuller l (e i) * WittVector.teichmuller l (e j) = 0
        rw [← map_mul, he.ortho hij, WittVector.teichmuller_zero] }
  have hE : IsIdempotentElem (∑ a, (WittVector.teichmuller l (e a) : A.W)) := hO.isIdempotentElem_sum
  have hu : IsIdempotentElem (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) := hE.one_sub
  have hc : (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)).coeff 0 = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← WittVector.constantCoeff_apply, map_sub, map_one, map_sum]
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rw [he.complete, sub_self]
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff _).2 hc)
  have ht : IsIdempotentElem (A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W))) := hu.map (A.toAcr n)
  have h0 : A.toAcr n (1 - ∑ a, (WittVector.teichmuller l (e a) : A.W)) = 0 := by
    rw [← ht.pow_succ_eq n, ← hc', map_mul, map_natCast, mul_pow, pow_succ (l : A.Acr n) n, A.pow_l_acr n,
      zero_mul, mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_one, map_sum, sub_eq_zero] at h0
  exact h0.symm

theorem lcNat : LcIdem → LcSpec → LcNat := by
  intro hId hSp l _ H A hA n
  refine ⟨?_, ?_⟩
  · intro B hB φ h g hg f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ n)) f
    have h1 := (hSp l H A hA n).2.2.2 f e he (fun a p => (hcut a p).1)
    have hφ : CompleteOrthogonalIdempotents (φ ∘ e) := he.map φ
    have h2 := (hSp l H B hB n).2.2.2 (lcRes _ (Spec.map (CommRingCat.ofHom g)) f) (φ ∘ e) hφ (fun a p hp => by
      refine (hcut a (PrimeSpectrum.comap g p)).1 fun hm => hp ?_
      have := hg (e a) (he.idem a)
      change algebraMap B.U B.Ug (B.sharp (φ (e a))) ∈ p.asIdeal
      rw [← this]
      exact hm)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, h2, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, PAlg.PdOk.acr_toAcr, WittVector.map_teichmuller, map_natCast]
    rfl
  · intro f
    obtain ⟨e, he, hcut, -⟩ := hId l H A hA (ZMod (l ^ (n + 1))) f
    have h1 := (hSp l H A hA (n + 1)).2.2.2 f e he (fun a p => (hcut a p).1)
    set c := ZMod.castHom (pow_dvd_pow l n.le_succ) (ZMod (l ^ n)) with hcdef
    have hL := (hSp l H A hA n).1 (f.map c)
    have hT : ∀ a, A.toAcr n (WittVector.teichmuller l (e a)) * lcA A n (f.map c) =
        A.toAcr n (WittVector.teichmuller l (e a)) * (a.val : A.Acr n) := fun a => by
      rw [hL (e a) (c a) (he.idem a) (fun p hp => by
        change c (f p) = c a
        rw [(hcut a p).1 hp]), natCast_val_castHom l n (A.pow_l_acr n) a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum, ← one_mul (lcA A n (f.map c)), ← sum_toAcr_teichmuller A he n, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hT a, map_mul, map_natCast]
    rfl

end GlobalTheory.CompanionTheory.LcNatProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationPairEntirePartBound
namespace GlobalTheory.CompanionTheory.EisRk1

open MeasureTheory Set Filter Topology

theorem weakFEPair_norm_Λ₀_le (P : WeakFEPair ℂ) {r M : ℝ}
    (hf : ∀ x : ℝ, 1 ≤ x → ‖P.f x - P.f₀‖ ≤ M * x ^ (-r))
    (hg : ∀ x : ℝ, 1 ≤ x → ‖P.g x - P.g₀‖ ≤ M * x ^ (-r))
    (s : ℂ) (hs₁ : s.re < r) (hs₂ : P.k - s.re < r) :
    ‖P.Λ₀ s‖ ≤ M / (r - s.re) + ‖P.ε‖ * M / (r - (P.k - s.re)) := by
  set σ := s.re with hσ
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (by simpa using hf 1 le_rfl)
  set h : ℝ → ℝ := (Ioi 1).indicator (fun t => M * t ^ (σ - 1 - r)) +
      (Ioo 0 1).indicator (fun t => ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k)) with hh
  have hA : IntegrableOn (fun t : ℝ => M * t ^ (σ - 1 - r)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul M
  have hB : IntegrableOn (fun t : ℝ => ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k)) (Ioo 0 1) :=
    (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := σ - 1 + r - P.k)
      (by linarith)).1).mono_set Ioo_subset_Ioc_self).const_mul _
  have hA' := hA.integrable_indicator measurableSet_Ioi
  have hB' := hB.integrable_indicator measurableSet_Ioo
  have hint : Integrable h (volume.restrict (Ioi 0)) := (hA'.add hB').restrict
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ h t := by
    intro t ht
    rw [mem_Ioi] at ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
    rcases lt_trichotomy t 1 with h1 | rfl | h1
    · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).2 h1
      have e := P.hf_modif_FE t⁻¹ (inv_pos.2 ht)
      rw [one_div, inv_inv] at e
      have hg' : P.g_modif t⁻¹ = P.g t⁻¹ - P.g₀ := by
        simp [WeakFEPair.g_modif, indicator_of_mem (mem_Ioi.2 hinv),
          indicator_of_notMem (notMem_Ioo_of_ge hinv.le)]
      have hval : h t = ‖P.ε‖ * M * t ^ (σ - 1 + r - P.k) := by
        simp [hh, indicator_of_notMem (notMem_Ioi.2 h1.le), indicator_of_mem (mem_Ioo.2 ⟨ht, h1⟩)]
      rw [hval, e, hg', norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (inv_pos.2 ht) _), Real.inv_rpow ht.le]
      have hb := hg t⁻¹ hinv.le
      rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv] at hb
      have key : t ^ (σ - 1 + r - P.k) = t ^ (σ - 1) * (t ^ P.k)⁻¹ * t ^ r := by
        rw [sub_eq_add_neg (σ - 1 + r), Real.rpow_add ht, Real.rpow_add ht, Real.rpow_neg ht.le]
        ring
      rw [key]
      have hpos : 0 ≤ t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹ := by positivity
      calc t ^ (σ - 1) * (‖P.ε‖ * (t ^ P.k)⁻¹ * ‖P.g t⁻¹ - P.g₀‖)
          = (t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹) * ‖P.g t⁻¹ - P.g₀‖ := by ring
        _ ≤ (t ^ (σ - 1) * ‖P.ε‖ * (t ^ P.k)⁻¹) * (M * t ^ r) := mul_le_mul_of_nonneg_left hb hpos
        _ = ‖P.ε‖ * M * (t ^ (σ - 1) * (t ^ P.k)⁻¹ * t ^ r) := by ring
    · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
      have hval : h 1 = 0 := by simp [hh]
      rw [h0, hval, norm_zero, mul_zero]
    · have hfm : P.f_modif t = P.f t - P.f₀ := by
        simp [WeakFEPair.f_modif, indicator_of_mem (mem_Ioi.2 h1),
          indicator_of_notMem (notMem_Ioo_of_ge h1.le)]
      have hval : h t = M * t ^ (σ - 1 - r) := by
        simp [hh, indicator_of_mem (mem_Ioi.2 h1), indicator_of_notMem (notMem_Ioo_of_ge h1.le)]
      rw [hfm, hval]
      have hb := hf t h1.le
      have key : t ^ (σ - 1 - r) = t ^ (σ - 1) * t ^ (-r) := by
        rw [sub_eq_add_neg (σ - 1), Real.rpow_add ht]
      rw [key]
      calc t ^ (σ - 1) * ‖P.f t - P.f₀‖ ≤ t ^ (σ - 1) * (M * t ^ (-r)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = M * (t ^ (σ - 1) * t ^ (-r)) := by ring
  have hI : ∫ t in Ioi (0 : ℝ), h t = M / (r - σ) + ‖P.ε‖ * M / (r - (P.k - σ)) := by
    rw [hh, integral_add' hA'.restrict hB'.restrict, setIntegral_indicator measurableSet_Ioi,
      setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.2 (Ioi_subset_Ioi zero_le_one), Set.inter_eq_right.2 Ioo_subset_Ioi_self,
      integral_const_mul, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    have hne : σ - 1 + r - P.k + 1 ≠ 0 := by linarith
    rw [Real.one_rpow, Real.one_rpow, Real.zero_rpow hne]
    have h1 : r - σ ≠ 0 := by linarith
    have h2 : r - (P.k - σ) ≠ 0 := by linarith
    have h3 : σ - 1 - r + 1 ≠ 0 := by linarith
    field_simp
    ring
  calc ‖P.Λ₀ s‖ = ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t‖ := rfl
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), h t :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hpt))
    _ = _ := hI

end GlobalTheory.CompanionTheory.EisRk1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorialAcr
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogMulPf

def ratHom {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) : ℚ →+* S :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom S) (fun y => by
    have hy : (y : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    have h := hu _ (Int.natAbs_ne_zero.2 hy)
    rcases Int.natAbs_eq (y : ℤ) with e | e
    · rw [e]; simpa using h
    · rw [e]; simpa using h)

theorem inv_smul_eq {S : Type} [CommRing S] [Algebra ℚ S] (m : ℕ) (hm : m ≠ 0) (x : S) :
    ((m : ℚ)⁻¹) • x = Ring.inverse (m : S) * x := by
  have h1 : (m : S) * algebraMap ℚ S (m : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ S), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]
  have h : IsUnit (m : S) := IsUnit.of_mul_eq_one _ h1
  apply h.mul_left_cancel
  rw [Algebra.smul_def, ← mul_assoc, ← mul_assoc, h1, Ring.mul_inverse_cancel _ h]

theorem core (hLA : LogAlg) {S : Type} [CommRing S] (hu : ∀ m : ℕ, m ≠ 0 → IsUnit (m : S)) (T : Subring S) (x y : S)
    (hx : ∀ k : ℕ, Ring.inverse (k.factorial : S) * x ^ k ∈ T)
    (hy : ∀ k : ℕ, Ring.inverse (k.factorial : S) * y ^ k ∈ T) :
    (∀ k : ℕ, Ring.inverse (k.factorial : S) * (x + y + x * y) ^ k ∈ T) ∧ ∀ N : ℕ, ∃ c ∈ T,
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) *
          (Ring.inverse ((k + 1).factorial : S) * (x + y + x * y) ^ (k + 1)) =
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * x ^ (k + 1)) +
        ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (Ring.inverse ((k + 1).factorial : S) * y ^ (k + 1)) +
          (N.factorial : S) * c := by
  letI : Algebra ℚ S := (ratHom hu).toAlgebra
  have e : ∀ (k : ℕ) (z : S), ((k.factorial : ℚ)⁻¹) • z ^ k = Ring.inverse (k.factorial : S) * z ^ k :=
    fun k z => inv_smul_eq _ k.factorial_ne_zero _
  have := hLA S T (fun k z => ((k.factorial : ℚ)⁻¹) • z ^ k) (fun _ _ => rfl) x y
    (fun k => by simp only [e]; exact hx k) (fun k => by simp only [e]; exact hy k)
  simpa only [e] using this

theorem sum_eq_of_coe {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (T : Subalgebra R S) (f f' f'' : ℕ → T)
    (N : ℕ) (c : T)
    (e : ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f'' (k + 1) : S) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f (k + 1) : S) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * (f' (k + 1) : S) + (N.factorial : S) * (c : S)) :
    ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f'' (k + 1) =
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f (k + 1) +
      ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : T) * f' (k + 1) + (N.factorial : T) * c := by
  apply Subtype.ext
  push_cast
  exact e

variable {l : ℕ} [Fact l.Prime]

theorem factorial_acr (A : PAlg l) (n : ℕ) : (((l * n).factorial : ℕ) : A.Acr n) = 0 := by
  obtain ⟨d, hd⟩ := ACris.pow_dvd_factorial (p := l) (le_refl (l * n))
  rw [hd, Nat.cast_mul, Nat.cast_pow, A.pow_l_acr, zero_mul]

theorem isLog_mul (hLA : LogAlg) (A : PAlg l) (n : ℕ) (w w' : A.W) (y y' : A.Acr n)
    (hy : IsLog A n w y) (hy' : IsLog A n w' y') : IsLog A n (w * w') (y + y') := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨g', hg', rfl⟩ := hy'
  have hab : algebraMap A.W (WL l A.A) (w * w' - 1) =
      algebraMap A.W (WL l A.A) (w - 1) + algebraMap A.W (WL l A.A) (w' - 1) +
        algebraMap A.W (WL l A.A) (w - 1) * algebraMap A.W (WL l A.A) (w' - 1) := by
    simp only [map_sub, map_mul, map_one]; ring
  obtain ⟨hT, hN⟩ := core hLA (fun m hm => A.isUnit_natCast hm) A.Acr0.toSubring
    (algebraMap A.W (WL l A.A) (w - 1)) (algebraMap A.W (WL l A.A) (w' - 1))
    (fun k => by have h := (g k).2; rw [hg k] at h; exact h)
    (fun k => by have h := (g' k).2; rw [hg' k] at h; exact h)
  have hmem : ∀ k, dpw k (w * w' - 1) ∈ A.Acr0 := fun k => by
    rw [dpw, hab]; exact hT k
  obtain ⟨c, hc, e⟩ := hN (l * n)
  refine ⟨fun k => ⟨dpw k (w * w' - 1), hmem k⟩, fun _ => rfl, ?_⟩
  have e0 := sum_eq_of_coe A.Acr0 g g' (fun k => ⟨dpw k (w * w' - 1), hmem k⟩) (l * n) ⟨c, hc⟩ (by
    simp only [hg, hg']
    simp only [dpw, hab]
    exact e)
  have e1 := congrArg (A.mkAcr n) e0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, map_neg, map_one, map_natCast] at e1
  rw [e1, factorial_acr, zero_mul, add_zero]

theorem logMul : CrystallineSemistableComparison.E.LogAlg → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.LogMul :=
  fun h _ _ _ A n w w' y y' _ _ hy hy' => isLog_mul h A n w w' y y' hy hy'

end GlobalTheory.CompanionTheory.LogMulPf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIdem
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TiltIdem

variable {B R : Type} [CommRing B] [CommRing R]

theorem idem_eq (i : B →* R)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {x y : B} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (h : ∀ p : PrimeSpectrum R, i x ∉ p.asIdeal ↔ i y ∉ p.asIdeal) : x = y := by
  have hix : IsIdempotentElem (i x) := by
    change i x * i x = i x
    rw [← map_mul, hx.eq]
  have hiy : IsIdempotentElem (i y) := by
    change i y * i y = i y
    rw [← map_mul, hy.eq]
  have hb : PrimeSpectrum.basicOpen (i x) = PrimeSpectrum.basicOpen (i y) := by
    ext p
    exact h p
  have e : i x = i y := PrimeSpectrum.basicOpen_injOn_isIdempotentElem hix hiy hb
  exact (hidem (i y) hiy).unique ⟨hx, e⟩ ⟨hy, rfl⟩

theorem exists_idem (i : B →* R) (h0 : i 0 = 0)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {ι : Type} [Fintype ι] (f : LocallyConstant (PrimeSpectrum R) ι) :
    ∃ e : ι → B, CompleteOrthogonalIdempotents e ∧
      (∀ (a : ι) (p : PrimeSpectrum R), i (e a) ∉ p.asIdeal ↔ f p = a) ∧
      ∀ (e' : B) (a : ι), IsIdempotentElem e' →
        (∀ p : PrimeSpectrum R, i e' ∉ p.asIdeal → f p = a) → e' * e a = e' := by
  classical
  have hfib : ∀ a : ι, ∃ e : B, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum R, i e ∉ p.asIdeal ↔ f p = a := by
    intro a
    have hc : IsClopen (f ⁻¹' {a}) := f.isLocallyConstant.isClopen_fiber a
    obtain ⟨ε, hε, hs⟩ := PrimeSpectrum.isClopen_iff.1 hc
    obtain ⟨e₀, ⟨he₀, rfl⟩, -⟩ := hidem ε hε
    refine ⟨e₀, he₀, fun p => ?_⟩
    have : p ∈ f ⁻¹' {a} ↔ p ∈ PrimeSpectrum.basicOpen (i e₀) := by rw [hs]; rfl
    exact this.symm
  choose e he hp using hfib
  have hnot0 : ∀ p : PrimeSpectrum R, ¬ (i 0 ∉ p.asIdeal) := fun p h => h (by rw [h0]; exact p.asIdeal.zero_mem)
  have hmul : ∀ (x y : B) (p : PrimeSpectrum R), i (x * y) ∉ p.asIdeal ↔ i x ∉ p.asIdeal ∧ i y ∉ p.asIdeal := by
    intro x y p
    rw [map_mul, p.isPrime.mul_mem_iff_mem_or_mem]
    tauto
  have hort : OrthogonalIdempotents e := by
    refine ⟨he, fun a b hab => ?_⟩
    refine idem_eq i hidem ((he a).mul (he b)) IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    obtain ⟨h1, h2⟩ := (hmul _ _ p).1 h
    exact hab (((hp a p).1 h1).symm.trans ((hp b p).1 h2))
  have hsum : IsIdempotentElem (∑ a, e a) := hort.isIdempotentElem_sum
  have hc : IsIdempotentElem (1 - ∑ a, e a) := hsum.one_sub
  have hce : ∀ a, (1 - ∑ b, e b) * e a = 0 := by
    intro a
    rw [sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single a, (he a).eq, sub_self]
    · exact fun b _ hb => hort.ortho hb
    · exact fun h => absurd (Finset.mem_univ a) h
  have hone : 1 - ∑ a, e a = 0 := by
    refine idem_eq i hidem hc IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    have h1 : i (e (f p)) ∉ p.asIdeal := (hp (f p) p).2 rfl
    have h2 := (hmul _ _ p).2 ⟨h, h1⟩
    rw [hce] at h2
    exact hnot0 p h2
  refine ⟨e, ⟨hort, (sub_eq_zero.1 hone).symm⟩, hp, fun e' a he' h => ?_⟩
  refine idem_eq i hidem (he'.mul (he a)) he' fun p => ?_
  rw [hmul]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', (hp a p).2 (h p h')⟩⟩

theorem sharp_zero' {l : ℕ} [Fact l.Prime] (A : PAlg l) : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem lcIdem : CrystallineSemistableComparison.E.LcIdem := by
  intro l _ H A hA ι _ f
  let i : A.A →* A.Ug := (algebraMap A.U A.Ug : A.U →* A.Ug).comp A.sharp
  have h0 : i 0 = 0 := by
    change algebraMap A.U A.Ug (A.sharp 0) = 0
    rw [sharp_zero', map_zero]
  let f' : LocallyConstant (PrimeSpectrum A.Ug) ι := ⟨f, f.isLocallyConstant⟩
  exact exists_idem i h0 (H.idem A hA) f'

end GlobalTheory.CompanionTheory.TiltIdem
end
