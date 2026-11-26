module

public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.TorEtPf
noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf

namespace LateralTheory.E.TorEtPf

def LocalGlue : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap S C))

def LocF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) f) ≃ₐ[S] (ZMod q → Localization.Away f))

def LocG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Nonempty (Localization.Away (algebraMap S (Tor f g hε) g) ≃ₐ[S] (ZMod q → Localization.Away g))

theorem surj_local (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) (p : PrimeSpectrum S) (hp : f ∉ p.asIdeal) :
    ∃ Q : PrimeSpectrum C, PrimeSpectrum.comap (algebraMap S C) Q = p := by
  have hr : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact hp
  obtain ⟨P, hP⟩ := hr
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨PrimeSpectrum.comap (algebraMap C (Localization.Away (algebraMap S C f)))
    (PrimeSpectrum.comap (e : Localization.Away (algebraMap S C f) →+* (ι → Localization.Away f))
      (PrimeSpectrum.comap (Pi.evalRingHom _ i) P)), ?_⟩
  rw [← hP]
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have : (e (algebraMap C (Localization.Away (algebraMap S C f)) (algebraMap S C x))) i = algebraMap S (Localization.Away f) x := by
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]; rfl
  simp only [RingHom.coe_coe, Pi.evalRingHom_apply, this]

theorem TorEt_of (hL : LocalGlue) (hF : LocF) (hG : LocG) : TorEt := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  exact hL S (Tor f g hε) (ZMod q) f g hfg (hF q S f g hfg ε hε) (hG q S f g hfg ε hε)

theorem surj_glue (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Nonempty ι] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (ef : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (eg : Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) := by
  intro p
  by_cases hf : f ∈ p.asIdeal
  · have hg : g ∉ p.asIdeal := by
      intro hg
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hfg, Ideal.span_le]
      rintro x (rfl | rfl) <;> assumption
    exact surj_local S C ι g eg p hg
  · exact surj_local S C ι f ef p hf

def LocalEF : Prop := ∀ (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] [Fintype ι] [Nonempty ι] (f g : S),
  Ideal.span {f, g} = ⊤ →
  Nonempty (Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) →
  Nonempty (Localization.Away (algebraMap S C g) ≃ₐ[S] (ι → Localization.Away g)) →
  Algebra.Etale S C ∧ Module.Finite S C

theorem localGlue_of (h : LocalEF) : LocalGlue := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  obtain ⟨h1, h2⟩ := h S C ι f g hfg ⟨ef⟩ ⟨eg⟩
  exact ⟨h1, h2, surj_glue S C ι f g hfg ef eg⟩

theorem TorEt_of' (hE : LocalEF) (hF : LocF) (hG : LocG) : TorEt := TorEt_of (localGlue_of hE) hF hG

theorem awayMap_eq (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f)) :
    Localization.awayMap (algebraMap S C) f =
      (e.symm : (ι → Localization.Away f) →+* Localization.Away (algebraMap S C f)).comp
        (algebraMap (Localization.Away f) (ι → Localization.Away f)) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext s
  simp only [RingHom.comp_apply]
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have h1 : algebraMap (Localization.Away f) (ι → Localization.Away f) (algebraMap S (Localization.Away f) s)
      = algebraMap S (ι → Localization.Away f) s := rfl
  rw [h1, RingHom.coe_coe, AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply S C (Localization.Away (algebraMap S C f)) s)

theorem away_prop (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop) (hP : RingHom.RespectsIso @P)
    (S C ι : Type) [CommRing S] [CommRing C] [Algebra S C] (f : S)
    (e : Localization.Away (algebraMap S C f) ≃ₐ[S] (ι → Localization.Away f))
    (hb : P (algebraMap (Localization.Away f) (ι → Localization.Away f))) :
    P (Localization.awayMap (algebraMap S C) f) := by
  rw [awayMap_eq S C ι f e]
  exact hP.1 _ e.symm.toRingEquiv hb

theorem localEF_of : LocalEF := by
  intro S C ι _ _ _ _ _ f g hfg ⟨ef⟩ ⟨eg⟩
  have key : ∀ (P : ∀ {R S : Type} [CommRing R] [CommRing S], (R →+* S) → Prop), RingHom.RespectsIso @P →
      RingHom.OfLocalizationSpan @P →
      (∀ h : S, P (algebraMap (Localization.Away h) (ι → Localization.Away h))) → P (algebraMap S C) := by
    intro P hP hL hb
    apply hL (algebraMap S C) {f, g} hfg
    rintro ⟨r, hr⟩
    rcases hr with rfl | rfl
    · exact away_prop P hP S C ι _ ef (hb _)
    · exact away_prop P hP S C ι _ eg (hb _)
  refine ⟨?_, ?_⟩
  · rw [← RingHom.etale_algebraMap]
    exact key _ RingHom.Etale.respectsIso RingHom.Etale.ofLocalizationSpan
      (fun h => RingHom.etale_algebraMap.mpr inferInstance)
  · rw [← RingHom.finite_algebraMap]
    exact key _ RingHom.finite_respectsIso RingHom.finite_ofLocalizationSpan
      (fun h => RingHom.finite_algebraMap.mpr inferInstance)

theorem TorEt_of'' (hF : LocF) (hG : LocG) : TorEt := TorEt_of' localEF_of hF hG

def pr1 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away f) :=
  (RingHom.fst _ _).comp (Tor f g hε).subtype

def ProjF : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) f) (ZMod q → Localization.Away f)

theorem locF_of (h : ProjF) : LocF := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr1 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) f))
    (Localization.Away (algebraMap S (Tor f g hε) f)) (ZMod q → Localization.Away f)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) f)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) f)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

def pr2 {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}
    (hε : CompleteOrthogonalIdempotents ε) : Tor f g hε →+* (ZMod q → Localization.Away g) :=
  (RingHom.snd _ _).comp (Tor f g hε).subtype

def ProjG : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  IsLocalization.Away (algebraMap S (Tor f g hε) g) (ZMod q → Localization.Away g)

theorem locG_of (h : ProjG) : LocG := by
  intro q _ S _ f g hfg ε hε
  letI := (torMap f g hε).toAlgebra
  letI := (pr2 f g hε).toAlgebra
  haveI := h q S f g hfg ε hε
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap S (Tor f g hε) g))
    (Localization.Away (algebraMap S (Tor f g hε) g)) (ZMod q → Localization.Away g)
  refine ⟨AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun s => ?_)⟩
  have h1 : algebraMap S (Localization.Away (algebraMap S (Tor f g hε) g)) s =
      algebraMap (Tor f g hε) (Localization.Away (algebraMap S (Tor f g hε) g)) (torMap f g hε s) := rfl
  rw [AlgEquiv.coe_ringEquiv, h1, AlgEquiv.commutes]
  rfl

theorem TorEt_of_proj (hF : ProjF) (hG : ProjG) : TorEt := TorEt_of'' (locF_of hF) (locG_of hG)

end LateralTheory.E.TorEtPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.UnitExistence
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneExistsPf

open LateralTheory.E.CupProductRingLaws

def LeafUnitSec : Prop := ∀ (q : ℕ) [NeZero q], ∃ one : ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Sec (tw q 0) U,
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : IsUnit (q : Γ(U, ⊤))) (hV : IsUnit (q : Γ(V, ⊤))),
    Sec.res g (one U hU) = one V hV) ∧
  ∀ (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (ζ : Prim q Γ(U, ⊤)), one U hU = twGen 0 ζ

def LeafCocycleOfSec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U),
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) →
  ∃ α : Cocycle ((chains R).obj E) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α.1 0 0 (by simp) U x = Sec.map (resι R F) (s U ⟨x⟩)

theorem LeafOneExists_of (hU : LeafUnitSec) (hC : LeafCocycleOfSec) : LateralTheory.E.LeafOneSpecPf.LeafOneExists := by
  intro q _ E hE
  obtain ⟨one, hnat, hone⟩ := hU q
  obtain ⟨α, hα⟩ := hC (ZMod q) (tw q 0) E (fun U h => one U (hE U h))
    (fun V U g hU' hV' => hnat V U g _ _)
  refine ⟨α, fun U x ζ => ?_⟩
  rw [hα U x, hone U _ ζ]
  rfl

end LateralTheory.E.LeafOneExistsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGeoVCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoVCut

def FamilyVe {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

def LeafCurveV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
    genericPoint X ∈ Set.range e ∧ ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X

theorem surj_of_generic {Y X : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [IsProper f]
    (hη : genericPoint X ∈ Set.range f) : Surjective f := by
  have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have h1 : closure ({genericPoint X} : Set X) ⊆ Set.range f :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hc
  rw [(genericPoint_spec X).def] at h1
  exact ⟨fun x => h1 (Set.mem_univ x)⟩

end LateralTheory.E.LeafGeoVCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LFactorPf
noncomputable section
open Polynomial

namespace LateralTheory.E.LFactorPf

def LEtaleLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ ψ : A' →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp ψ = φ

theorem LFactor_of (hE : LEtaleLift) : LateralTheory.E.HensIdemCut.LFactor := by
  intro A _ I _ f g₀ h₀ hf hg hh hgh e
  rcases subsingleton_or_nontrivial (A ⧸ I) with hs | hs
  · have hI : I = ⊤ := Ideal.Quotient.subsingleton_iff.mp hs
    have h1 : (1 : A) ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson_bot]
      exact HenselianRing.jac (I := I) (hI ▸ Submodule.mem_top)
    have hu := Ideal.mem_jacobson_bot.mp h1 (-1)
    have hA : Subsingleton A := by
      simp at hu
      exact subsingleton_of_zero_eq_one (by simpa using hu)
    refine ⟨1, 1, monic_one, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hn : f.natDegree = g₀.natDegree + h₀.natDegree := by
    rw [← hg.natDegree_mul hh, ← e, hf.natDegree_map]
  let p : MonicDegreeEq A f.natDegree := .mk f hf rfl
  have e' : g₀ * h₀ = p.1.map (algebraMap A (A ⧸ I)) := e.symm
  let φ := (UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) _ _ hn p).symm
    ⟨(.mk g₀ hg rfl, .mk h₀ hh rfl), e', hgh⟩
  obtain ⟨ψ, hψ⟩ := hE A I _ φ
  let q := UniversalCoprimeFactorizationRing.homEquiv A _ _ hn p ψ
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, ?_, ?_⟩
  · have := q.2.1
    simpa [p] using this.symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_fst A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm
  · have := UniversalCoprimeFactorizationRing.homEquiv_comp_snd A _ _ hn p ψ (Ideal.Quotient.mkₐ A I)
    rw [hψ, Equiv.apply_symm_apply] at this
    exact congr($(this).1).symm

end LateralTheory.E.LFactorPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FibClosedPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf

namespace LateralTheory.E.FibClosedPf

abbrev fm {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    pullback (c ≫ p) (cpt A) ⟶ pullback p (cpt A) :=
  pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp)

def FibQCQS : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A))
  [QuasiCompact c] [QuasiSeparated c], QuasiCompact (fm c p) ∧ QuasiSeparated (fm c p)

def FibStalk : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.map (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s) (𝟙 _)
      ((pullback p (cpt A)).fromSpecStalk s) (fm c p) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem FibClosed_of (hZ : ZLG) (h0 : HZero) (hA : AICAcyc) (hQ : FibQCQS) (hS : FibStalk) : FibClosed := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB
  obtain ⟨_, _⟩ := hQ A c p
  obtain ⟨_, _⟩ := qcqs_of (pullback.snd p (cpt A))
  have hu : IsUnit (q : Γ(pullback p (cpt A), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  exact hZ H q (fm c p) (𝟙 _) hu i (hS H h0 hA q i A hq c p hZs hSs hB)

theorem fm_isPullback {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    IsPullback (fm c p) (pullback.fst (c ≫ p) (cpt A)) (pullback.fst p (cpt A)) c := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p (cpt A)) (h₂₂ := p) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p (cpt A)).flip
  have e : fm c p ≫ pullback.snd p (cpt A) = pullback.snd (c ≫ p) (cpt A) := by
    unfold fm; rw [pullback.map]; erw [pullback.lift_snd]; simp
  rw [e]
  exact (IsPullback.of_hasPullback (c ≫ p) (cpt A)).flip

theorem fibQCQS : FibQCQS := by
  intro A _ _ Z S c p _ _
  exact ⟨MorphismProperty.of_isPullback (P := @QuasiCompact) (fm_isPullback c p).flip ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (fm_isPullback c p).flip ‹_›⟩

end LateralTheory.E.FibClosedPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ProdAcycPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ProdAcycPf

theorem zero_acyc (H : LateralTheory.E.t_E2Cut.Hyp) (q : ℕ) (A : Type) [CommRing A] [Subsingleton A] : Acyc q (sp A) := by
  intro n i hn
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : Ht q (sp A) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, -, -, hx⟩ := H.a5 (ZMod q) (Spec (CommRingCat.of A)) (tw q i) n hn x
    have : IsEmpty (Spec (CommRingCat.of A)) := inferInstanceAs (IsEmpty (PrimeSpectrum A))
    have : IsIso (sch.map f) := inferInstance
    have hy : pull _ (inv (sch.map f)) _ _ (pull _ (sch.map f) _ _ x) = x := by
      rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    rw [← hy, hx, map_zero]
  rw [h0 x, h0 y]

def Bin : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1],
  Nonempty (A ≃+* R0 × R1) → Acyc q (sp R0) → Acyc q (sp R1) → Acyc q (sp A)

def splitFirst (n : ℕ) (R : Fin (n + 1) → Type) [∀ k, CommRing (R k)] :
    (∀ k, R k) ≃+* R 0 × ∀ k : Fin n, R k.succ where
  toFun f := (f 0, fun k => f k.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem prod_of (hB : Bin) : LateralTheory.E.QuotAcycCut.ProdAcyc := by
  intro H q A _ n
  induction n generalizing A with
  | zero =>
    intro R _ ⟨e⟩ _
    have : Subsingleton A := e.injective.subsingleton
    exact zero_acyc H q A
  | succ n ih =>
    intro R _ ⟨e⟩ hR
    refine hB H q A (R 0) (∀ k : Fin n, R k.succ) ⟨e.trans (splitFirst n R)⟩ (hR 0) ?_
    exact ih (∀ k : Fin n, R k.succ) (fun k => R k.succ) ⟨RingEquiv.refl _⟩ fun k => hR k.succ

end LateralTheory.E.ProdAcycPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CxDescPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CxDescPf

abbrev tr {R : Type} [CommRing R] (K : Cx R) (N : ℕ) : Cx R :=
  K.stupidTrunc (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

abbrev trm {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (N : ℕ) : tr K N ⟶ tr L N :=
  HomologicalComplex.stupidTruncMap g (ComplexShape.embeddingUpIntGE (-(N : ℤ)))

def Good {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (I : Cx R) (m : ℤ) : Prop :=
  (∀ j : ℤ, j < m → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I m)

def stupid : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ((∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
    ∀ j : ℤ, Function.Bijective (cpull (trm g 0) I j)) ∧
  ∀ (m : ℤ) (N : ℕ), m + 1 ≤ (N : ℤ) → Good (trm g N) I m → Good g I m

def long : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ) (N : ℕ),
  Good ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) I m →
  Good (trm g N) I m → Good (trm g (N + 1)) I m

def shift : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (p : ℕ) (j : ℤ),
  (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j)) ∧
  (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - p)) →
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map φ) I j))

theorem CxDesc_of (hS : stupid) (hL : long) (hH : shift) : LateralTheory.E.DescStepPf.CxDesc := by
  intro R _ I _ hI K L _ _ g n hlow hn h0
  obtain ⟨hb, hlim⟩ := hS R I hI g
  have base : Good (trm g 0) I (n + 1) := ⟨fun j _ => hb h0 j, (hb h0 (n + 1)).1⟩
  have step : ∀ N : ℕ, Good (trm g N) I (n + 1) := by
    intro N
    induction N with
    | zero => exact base
    | succ N ih =>
      refine hL R I hI g (n + 1) N ⟨fun j hj => ?_, ?_⟩ ih
      · exact (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) j).1 (hlow (N + 1) (j - ((N + 1 : ℕ) : ℤ)) (by omega))
      · apply (hH R I (g.f (-((N + 1 : ℕ) : ℤ))) (N + 1) (n + 1)).2
        rcases Nat.eq_zero_or_pos N with h | h
        · subst h
          have e : n + 1 - ((0 + 1 : ℕ) : ℤ) = n := by omega
          rw [e]; exact hn (0 + 1)
        · exact (hlow (N + 1) _ (by omega)).1
  have hg := hlim (n + 1) (n + 2).toNat (by omega) (step _)
  exact ⟨hg.1, hg.2⟩

end LateralTheory.E.CxDescPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CompPf
noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.CompPf
open LateralTheory.E.t_E3Cut

section
variable {R D : Type} [CommRing R] [CommRing D] (h : R →+* D)

theorem eval_map_rr (p : R[X]) (x : D) :
    (p.map h.rangeRestrict).eval₂ h.range.subtype x = p.eval₂ h x := by
  rw [eval₂_map]; rfl

theorem alg_of (x : D) (p : R[X]) (n : ℕ) (hn : h (p.coeff n) ≠ 0) (hp : p.eval₂ h x = 0) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra;
    IsAlgebraic h.range x := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  refine ⟨p.map h.rangeRestrict, ?_, ?_⟩
  · intro h0
    apply hn
    have h1 := congrArg (fun q => ((q.coeff n : h.range) : D)) h0
    simpa using h1
  · rw [aeval_def]; exact (eval_map_rr h p x).trans hp

theorem of_alg (x : D) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra;
    IsAlgebraic h.range x → ∃ p : R[X], (∃ n, h (p.coeff n) ≠ 0) ∧ p.eval₂ h x = 0 := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  rintro ⟨q, hq0, hq⟩
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective h.rangeRestrict h.rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simpa using hc n
  · rw [aeval_def] at hq; exact (eval_map_rr h p x).symm.trans hq
end

theorem Comp_of : LateralTheory.E.AlgResPropsPf.Comp := by
  intro A B C f g hf hg Q hQ c
  haveI := hQ
  let gB : B →+* C ⧸ Q := (Ideal.Quotient.mk Q).comp g.hom
  let fA : A →+* C ⧸ Q := gB.comp f.hom
  have hle : fA.range ≤ gB.range := by rintro _ ⟨a, rfl⟩; exact ⟨f.hom a, rfl⟩
  letI : Algebra fA.range (C ⧸ Q) := fA.range.subtype.toAlgebra
  letI : Algebra gB.range (C ⧸ Q) := gB.range.subtype.toAlgebra
  letI : Algebra fA.range gB.range := (Subring.inclusion hle).toAlgebra
  haveI : IsScalarTower fA.range gB.range (C ⧸ Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI h1 : Algebra.IsAlgebraic fA.range gB.range := ⟨by
    rintro ⟨_, b, rfl⟩
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap g.hom) (hQ.comap _) b
    have hb := alg_of fA (gB b) p n (by
        intro h0; apply hn; rw [Ideal.mem_comap]; exact Ideal.Quotient.eq_zero_iff_mem.mp h0)
      (by
        have h5 : (Ideal.Quotient.mk Q) (g.hom (p.eval₂ f.hom b)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂, hom_eval₂] at h5; exact h5)
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom fA.range gB.range (C ⧸ Q)) Subtype.val_injective).mp hb⟩
  haveI h2 : Algebra.IsAlgebraic gB.range (C ⧸ Q) := ⟨by
    intro x
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hg Q hQ c'
    exact alg_of gB _ p n (fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      (by
        have h5 : (Ideal.Quotient.mk Q) (p.eval₂ g.hom c') = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂] at h5; exact h5)⟩
  have h3 := (Algebra.IsAlgebraic.trans fA.range gB.range (C ⧸ Q)).1 (Ideal.Quotient.mk Q c)
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := of_alg fA _ h3
  refine ⟨p, ⟨n, fun hm => hn (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hom_eval₂]; exact hp

end LateralTheory.E.CompPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairHtpyPf

def LeafTwTensExists : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTensFactor : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor →
  ∀ ν : Pair I J K, ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T),
  τ.IsTensor → IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResHtpy : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∀ u u' : T ⟶ res _ (tw q k), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

theorem secMap_add {R : Type} [CommRing R] {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem secMap_id_f {R : Type} [CommRing R] (I : Cx R) (s : ℤ) {U : Scheme.{0}} (x : Sec (I.X s) U) :
    Sec.map ((𝟙 I : I ⟶ I).f s) x = x := by
  rw [HomologicalComplex.id_f]; rfl

theorem secMap_addx {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ x y

theorem secMap_usmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℤˣ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem hom_reindex {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (Hh : ∀ i j, T.X i ⟶ K.X j)
    (U : Scheme.{0}) (s t v n : ℤ) (hv : v + 1 = n) (hs : s + t = n) (hs' : s + t = v + 1)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (Hh (v + 1) v) (τ.mul U s t (v + 1) hs' a b) = Sec.map (Hh n v) (τ.mul U s t n hs a b) := by
  subst hv; rfl

theorem pairHtpy_of_homotopy {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (μ μ' : Pair I J K) (u u' : T ⟶ K)
    (hu : τ.Compat μ (𝟙 I) (𝟙 J) u) (hu' : τ.Compat μ' (𝟙 I) (𝟙 J) u') (H : Homotopy u u') :
    LateralTheory.E.LeafTwPairUniquePf.PairHtpy μ μ' := by
  refine ⟨fun U s t w hw => (τ.mul U s t (w + 1) hw).compr₂ (((H.hom (w + 1) w).hom.app (op U)).hom), ?_, ?_⟩
  · intro V U g s t w hw a b
    simp only [LinearMap.compr₂_apply]
    rw [← τ.nat g s t (w + 1) hw a b]
    exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) (τ.mul _ s t (w + 1) hw a b)) ((H.hom (w + 1) w).hom.naturality g.op)).symm
  · intro U s t w hw a b
    simp only [LinearMap.compr₂_apply]
    have e1 := hu U s t w hw a b
    have e2 := hu' U s t w hw a b
    rw [secMap_id_f, secMap_id_f] at e1 e2
    rw [← e1, ← e2]
    have hc := H.comm w
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel w (w + 1) by simp),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel (w - 1) w by simp)] at hc
    rw [hc, secMap_add, secMap_add, secMap_comp, secMap_comp]
    have e3 := hom_reindex τ H.hom U s t (w - 1) w (by omega) hw (by omega) a b
    have e3' : (ModuleCat.Hom.hom ((H.hom (w - 1 + 1) (w - 1)).hom.app (op U))) (τ.mul U s t (w - 1 + 1) (by omega) a b) =
        Sec.map (H.hom w (w - 1)) (τ.mul U s t w hw a b) := e3
    rw [e3']
    rw [τ.leibniz, secMap_addx, secMap_usmul]
    dsimp only [Sec.map]
    abel

end LateralTheory.E.LeafTwPairHtpyPf

open LateralTheory.E.LeafTwPairHtpyPf in
theorem LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of (hE : LeafTwTensExists) (hF : LeafTensFactor) (hR : LeafTwTensRes)
    (hH : LeafTwResHtpy) : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := by
  intro q _ i j μ μ' hμ hμ'
  obtain ⟨T, τ, hτ⟩ := hE q i j
  obtain ⟨u, hu⟩ := hF (ZMod q) τ hτ μ
  obtain ⟨u', hu'⟩ := hF (ZMod q) τ hτ μ'
  obtain ⟨H⟩ := hH q (i + j) _ (hR q i j τ hτ) u u' (fun U ζ => by
    have a1 := hu U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    have a2 := hu' U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [secMap_id_f, secMap_id_f] at a1 a2
    rw [a1, a2, hμ U ζ, hμ' U ζ])
  exact pairHtpy_of_homotopy τ μ μ' u u' hu hu' H
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem resGen_res' {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (ζ.map g.appTop.hom) := by
  have h1 : Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ 1) :
        (twF q i).obj Γ(U, ⊤)))
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    simp only [ModuleCat.hom_comp] at h
    refine h.symm.trans (congrArg (fun x => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom x) ?_)
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold resGen
  rw [← h1]
  exact congrArg (fun f => f.hom (twGen i ζ)) (((resι _ (tw q i)).hom.naturality g.op)).symm

def UnitPairLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → ν.mul U 0 t t (zero_add t) a b = b

theorem sec_eq_of_loc {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x y : Sec F U)
    (h : Loc U fun V g => Sec.res g x = Sec.res g y) : x = y := by
  obtain ⟨S, hS, hP⟩ := h
  have hsh := (F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS).isSeparatedFor
  let fx : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)
  let fy : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have hxy : fx = fy := by
    refine hsh.ext (fun V g hg => ?_)
    change fx ≫ F.obj.map g.op = fy ≫ F.obj.map g.op
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (F.obj.map g.op).hom (fx.hom 1) = (F.obj.map g.op).hom (fy.hom 1)
    simpa [fx, fy] using hP V g hg
  have := congrArg (fun f => f.hom 1) hxy
  simpa [fx, fy] using this

def LeafUnitPairG : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U),
    ν.mul U 0 t t (zero_add t) (resGen 0 ζ) b = b

theorem unitPairLoc_of (h : LeafUnitPairG) : UnitPairLoc := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  refine ⟨ν, fun U t a b ha => sec_eq_of_loc _ _ _ ?_⟩
  obtain ⟨S, hS, hP⟩ := ha
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ, hζ⟩ := hP V g hg
  rw [ν.nat g 0 t t (zero_add t) a b, hζ, hν]

theorem leafUnitPair_of_loc (h : UnitPairLoc) : LeafUnitPair := by
  intro q _ i
  obtain ⟨ν, hν⟩ := h q i
  have key : ∀ k (_ : i = k), ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)),
      ∀ U s t w (hw : s + t = w) a b, HEq (μ.mul U s t w hw a b) (ν.mul U s t w hw a b) := by
    rintro k rfl
    exact ⟨ν, fun _ _ _ _ _ _ _ => HEq.rfl⟩
  obtain ⟨μ, hμ⟩ := key (0 + i) (zero_add i).symm
  have gen : ∀ U t w w' (h1 : 0 + t = w) (h2 : 0 + t = w') (_ : w = w') a b,
      HEq (ν.mul U 0 t w h1 a b) (ν.mul U 0 t w' h2 a b) := by
    intro U t w w' h1 h2 e a b
    subst e
    rfl
  have hgen : ∀ k (_ : k = i) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), HEq (resGen k ζ) (resGen i ζ) := by
    rintro k rfl U ζ
    rfl
  refine ⟨μ, ?_, ?_⟩
  · intro U ζ
    have hloc : Loc U (fun V g => ∃ ζ' : Prim q Γ(V, ⊤), Sec.res g (resGen 0 ζ) = resGen 0 ζ') :=
      ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ g _ => ⟨_, resGen_res' 0 g ζ⟩⟩
    exact eq_of_heq ((hμ U 0 0 0 _ _ _).trans ((heq_of_eq (hν U 0 _ _ hloc)).trans (hgen _ (zero_add i) U ζ).symm))
  · intro U t w hw a b ha
    exact (hμ U 0 t w hw a b).trans ((gen U t w t hw (zero_add t) (by omega) a b).trans (heq_of_eq (hν U t a b ha)))

theorem LeafUnitPair_of (h : LeafUnitPairG) : LeafUnitPair := leafUnitPair_of_loc (unitPairLoc_of h)

end LateralTheory.E.LeafUnitPairPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CoverPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.CoverPf

def EmptyVan : Prop := A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ) (S : Type) [CommRing S], Subsingleton S →
  ∀ x : Ht q (sp S) (n + 1) i, x = 0

theorem pull_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) (q : ℕ) (m i : ℤ)
    (x : Ht q (sp A) m i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  have : spMap (g.comp f) = spMap g ≫ spMap f := by simp [spMap]
  rw [this, pull_comp]

theorem dies_of_factor {S : Type} [CommRing S] {q : ℕ} {m i : ℤ} (x : Ht q (sp S) m i) (f : S)
    (hx : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    {T : Type} [CommRing T] (φ : S →+* T) (hu : IsUnit (φ f)) : pull _ (spMap φ) _ _ x = 0 := by
  have e : φ = (IsLocalization.Away.lift f (S := Localization.Away f) hu).comp (algebraMap S (Localization.Away f)) :=
    (IsLocalization.Away.lift_comp f (S := Localization.Away f) hu).symm
  rw [e, pull_comp', hx, map_zero]

theorem dies_add (hQ : QAClosed) (hM : MV) (h1 : A1) {q : ℕ} {i n : ℤ} (hk : MVHyp q i n)
    {S : Type} [CommRing S] (hS : QA S) (hq : IsUnit (q : S)) (x : Ht q (sp S) (n + 1) i) (f g : S)
    (hf : pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0)
    (hg : pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0) :
    pull _ (spMap (algebraMap S (Localization.Away (f + g)))) _ _ x = 0 := by
  set T := Localization.Away (f + g)
  set φ := algebraMap S T
  have hT : QA T := (hQ S hS).2.1 (f + g)
  have hqT : IsUnit (q : T) := by simpa using hq.map φ
  have hspan : Ideal.span {φ f, φ g} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := T) (f + g)
    have hmem : φ (f + g) ∈ Ideal.span {φ f, φ g} := by
      rw [map_add (f := _)]
      exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
    have : (1 : T) = ((u⁻¹ : Tˣ) : T) * φ (f + g) := by
      change (1 : T) = ((u⁻¹ : Tˣ) : T) * algebraMap S T (f + g)
      rw [← hu]; simp
    rw [this]; exact Ideal.mul_mem_left _ _ hmem
  have key := hM h1 (ZMod q) (tw q i) T (φ f) (φ g) hspan n (hk T hT hqT (φ f) (φ g) hspan)
    (pull _ (spMap φ) _ _ x)
  apply key
  · rw [← pull_comp']
    exact dies_of_factor x f hf _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ f)) (φ f))
  · rw [← pull_comp']
    exact dies_of_factor x g hg _ (by
      simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (φ g)) (φ g))

theorem Cover_of (hE : EmptyVan) : LateralTheory.E.AcycQAPf.Cover := by
  intro hQ hM h1 q _ i n hk S _ hS hq x hloc
  let I : Set S := {g | pull _ (spMap (algebraMap S (Localization.Away g))) _ _ x = 0}
  have hmul : ∀ a g, g ∈ I → a * g ∈ I := by
    intro a g hg
    refine dies_of_factor x g hg _ ?_
    exact isUnit_of_mul_isUnit_right (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a * g)) (a * g)
      |>.map (RingHom.id _) |> fun h => by simpa [map_mul] using h)
  have hadd : ∀ f g, f ∈ I → g ∈ I → f + g ∈ I := fun f g hf hg => dies_add hQ hM h1 hk hS hq x f g hf hg
  have hspan : Ideal.span I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM', hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hfM, hf⟩ := hloc ⟨M, hM'.isPrime⟩
    exact hfM (hle (Ideal.subset_span hf))
  have hP : ∀ y ∈ Ideal.span I, y ∈ I ∨ y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Or.inl hy
    | zero => exact Or.inr rfl
    | add a b _ _ ha hb =>
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (hadd a b ha hb)
      · subst hb; simpa using Or.inl ha
      · subst ha; simpa using Or.inl hb
      · subst ha; subst hb; simp
    | smul a b _ hb =>
      rcases hb with hb | hb
      · exact Or.inl (hmul a b hb)
      · subst hb; simp
  rcases hP 1 (by rw [hspan]; trivial) with h | h
  · have := dies_of_factor x 1 h (RingHom.id S) isUnit_one
    have e : spMap (RingHom.id S) = 𝟙 _ := by simp [spMap]
    rwa [e, pull_id] at this
  · have : Subsingleton S := subsingleton_of_zero_eq_one h.symm
    exact hE h1 q i n S inferInstance x

end LateralTheory.E.CoverPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SepTensorPf
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SepTensorPf

theorem SepTensor_of : LateralTheory.E.SHTensorPf.SepTensor := by
  intro A X B Z x b u v hp _ hX _ hb _ hZ
  obtain ⟨_, hXs⟩ := hX
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  let f : X →+* IsLocalRing.ResidueField Z := (IsLocalRing.residue Z).comp u.hom
  have hf : f.IsIntegral := RingHom.IsIntegral.trans u.hom (IsLocalRing.residue Z) hu
    (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective)
  let _ : Algebra X (IsLocalRing.ResidueField Z) := f.toAlgebra
  have : Algebra.IsIntegral X (IsLocalRing.ResidueField Z) := ⟨hf⟩
  have : Algebra.IsIntegral (IsLocalRing.ResidueField X) (IsLocalRing.ResidueField Z) :=
    Algebra.IsIntegral.tower_top X
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField X)

end LateralTheory.E.SepTensorPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwTensResPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwTensResPf

def LeafTensTwres : Prop := LateralTheory.EtaleFoundations.EtaleTensorPairTwistResolutionMul

def LeafResFlat : Prop := ∀ (q : ℕ) [NeZero q] (j t : ℤ), FlatS ((res (ZMod q) (tw q j)).X t)

instance resGE (q : ℕ) (i : ℤ) : (res (ZMod q) (tw q i)).IsStrictlyGE 0 := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem res_isTwRes (q : ℕ) [NeZero q] (i : ℤ) :
    IsTwRes q i (res (ZMod q) (tw q i)) (fun _ ζ => resGen i ζ) := by
  refine ⟨resGE q i, resAug (tw q i), ?_, fun U ζ => ?_⟩
  · unfold resAug
    exact (inferInstance : QuasiIso (injectiveResolution (tw q i)).ι')
  · simp only [resGen, resι, sglι, Sec.map]
    rfl

theorem leafTwTensRes_of (h1 : LeafTensTwres) (h2 : LeafResFlat) : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensRes := by
  intro q _ i j T τ hτ
  exact h1 q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) (res_isTwRes q i) (res_isTwRes q j) (h2 q j) τ hτ

end LateralTheory.E.LeafTwTensResPf
end
end
