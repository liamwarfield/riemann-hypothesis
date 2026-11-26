module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.EtaleSheaves.LineHigh

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafKillCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKillCut

open LateralTheory.E.E4

def LeafOne : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → ∀ x : Ht q (sch.obj C) m i,
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m x = 0

theorem goal_of (hOne : LeafOne) : LateralTheory.E.E4.LeafKill := by
  intro hy q _ Ω _ _ hq C c hc m i hm hfin
  classical
  have key : ∀ s : Finset (Ht q (sch.obj C) m i), ∃ (C' : Scheme.{0}) (γ : C' ⟶ C),
      IsCurve (γ ≫ c) ∧ Surjective γ ∧ ∀ x ∈ s, pl q i γ m x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨C, 𝟙 C, by simpa using hc, inferInstance, by simp⟩
    | insert a s ha IH =>
      obtain ⟨C1, γ1, h1, s1, k1⟩ := IH
      obtain ⟨C2, γ2, h2, s2, k2⟩ := hOne hy q Ω hq (γ1 ≫ c) h1 m i hm (pl q i γ1 m a)
      have := s1
      have := s2
      refine ⟨C2, γ2 ≫ γ1, by simpa [Category.assoc] using h2, inferInstance, ?_⟩
      intro x hx
      rw [pl_comp]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact k2
      · rw [k1 x hx, map_zero]
  have := Fintype.ofFinite (Ht q (sch.obj C) m i)
  obtain ⟨C', γ, h1, h2, h3⟩ := key Finset.univ
  exact ⟨C', γ, h1, h2, AddMonoidHom.ext fun x => by simpa using h3 x (Finset.mem_univ x)⟩

end LateralTheory.E.LeafKillCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafKumCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafKumCut

def LeafTwist : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Nonempty (Prim q B) →
  ∀ n i j : ℤ, Nonempty (Ht q (sp B) n i ≃+ Ht q (sp B) n j)

def EtaleFirstCohomologyMultiplicativeGroupPicard : Prop := Hyps → DivisorPicardCompatibility

def LeafKumSeq : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ (a : Additive (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) →+ Ht q (sp B) 1 1)
    (b : Ht q (sp B) 1 1 →+ H ℤ (sp B) Gm 1), Function.Exact a b

theorem prim_of_isAlgClosed (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k)) :
    Nonempty (Prim q k) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k (NeZero.pos q)))
  refine ⟨⟨ζ, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ

theorem finite_of_exact {A M N : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup N] [Finite A]
    (a : A →+ M) (b : M →+ N) (h : Function.Exact a b) (hb : Finite b.range) : Finite M := by
  have hK : Finite b.ker := by
    have : (b.ker : Set M) = Set.range a := by ext x; exact h x
    have hf : (Set.range a).Finite := Set.finite_range a
    rw [← this] at hf
    exact hf.to_subtype
  have hQ : Finite (M ⧸ b.ker) := Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange b).symm.toEquiv
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup b.ker
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  have : Nonempty (M ⧸ b.ker) := ⟨0⟩
  exact Nat.mul_ne_zero (Nat.card_pos).ne' (Nat.card_pos).ne'

theorem goal_of (hT : LeafTwist) (hG : EtaleFirstCohomologyMultiplicativeGroupPicard) (hS : LeafKumSeq) : LeafKum := by
  intro hy q _ k B _ _ _ _ hq hU hP i
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  obtain ⟨ζ⟩ := prim_of_isAlgClosed q k hq
  obtain ⟨e⟩ := hT hy q B ⟨ζ.map (algebraMap k B)⟩ 1 i 1
  obtain ⟨a, b, hab⟩ := hS hy q B hqB
  obtain ⟨E⟩ := hG hy B
  have hr : Finite b.range := by
    refine Finite.of_injective (β := {c : CommRing.Pic B // c ^ q = 1})
      (fun y => ⟨Additive.toMul (E y.1), ?_⟩) ?_
    · obtain ⟨x, hx⟩ := y.2
      have h0 : q • x = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_self, zero_smul]
      have : q • E y.1 = 0 := by rw [← hx, ← map_nsmul, ← map_nsmul, h0, map_zero, map_zero]
      rw [← toMul_nsmul, this, toMul_zero]
    · intro y z h
      apply Subtype.ext
      apply E.injective
      apply Additive.toMul.injective
      exact congrArg Subtype.val h
  have : Finite (Ht q (sp B) 1 1) := finite_of_exact a b hab hr
  exact Finite.of_equiv _ e.symm.toEquiv

end LateralTheory.E.LeafKumCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGhostCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostCut
open LateralTheory.E.E4

def rmap (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) : mappingCone ((chains R).map f') ⟶ mappingCone ((chains R).map f) :=
  mappingCone.map _ _ ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])

abbrev fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) : Hrel R f F n →+ H R E F n :=
  HK.pull R (mappingCone.inr ((chains R).map f)) F n

abbrev rpull (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (F : Shv R) (n : ℤ) : Hrel R f F n →+ Hrel R f' F n :=
  HK.pull R (rmap R f f' u e comm) F n

abbrev rpl (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (comm : f' ≫ e = u ≫ f) (n : ℤ) : Hrel (ZMod q) (sch.map f) (tw q i) n →+ Hrel (ZMod q) (sch.map f') (tw q i) n :=
  rpull (ZMod q) (sch.map f) (sch.map f') (sch.map u) (sch.map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (tw q i) n

def LeafRelExact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (x : H R E F n),
  pull R f F n x = 0 → ∃ y : Hrel R f F n, fgt R f F n y = x

def LeafRelNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n),
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y)

def LeafGhostRel : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (y : Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n),
    ∃ c : Hrel (ZMod q) (sch.map ι) (tw q i) n,
      rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y =
        rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p) pullback.condition n c

open CochainComplex.HomComplex in
theorem relExact : LeafRelExact := by
  intro R _ F U E f n x hx
  obtain ⟨z, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add n)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m, hm, β, hβ⟩ := hx
  refine ⟨CohomologyClass.mk (mappingCone.descCocycle _ (n.negOnePow • β) z hm ?_), ?_⟩
  · rw [δ_units_smul, hβ]
    simp [zcomp]
  · refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp [zcomp]

open CochainComplex.HomComplex in
theorem relNat : LeafRelNat := by
  intro R _ F U E U' E' f f' u e comm n y
  have key : mappingCone.inr ((chains R).map f') ≫ rmap R f f' u e comm =
      (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [rmap, mappingCone.map]
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, key, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

theorem goal_of_all (hEx : LeafRelExact) (hNat : LeafRelNat) (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n a ha
  obtain ⟨y, rfl⟩ := hEx (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) n a ha
  obtain ⟨c, hc⟩ := hCore hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA n y
  refine ⟨fgt (ZMod q) (sch.map ι) (tw q i) n c, ?_⟩
  have e1 := hNat (ZMod q) (tw q i) (sch.map ι) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.snd (g2 ≫ g1 ≫ p) ι)) (sch.map (g2 ≫ g1 ≫ p))
    (by rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]) n c
  have hsq : pullback.fst (g2 ≫ g1 ≫ p) ι ≫ (g2 ≫ g1) =
      pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp) ≫ pullback.fst p ι := (pullback.lift_fst _ _ _).symm
  have e2 := hNat (ZMod q) (tw q i) (sch.map (pullback.fst p ι)) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι))
    (sch.map (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp))) (sch.map (g2 ≫ g1))
    (by rw [← Functor.map_comp, ← Functor.map_comp, hsq]) n y
  change pull _ _ _ _ _ = pull _ _ _ _ _
  rw [← e1, ← e2]
  exact congrArg _ hc.symm

theorem goal_of (hCore : LeafGhostRel) : LateralTheory.E.E4.LeafGhost := goal_of_all relExact relNat hCore

end LateralTheory.E.LeafGhostCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CoprodPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.CoprodPf

def FreeCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (X : ι → Scheme.{0}),
  Nonempty (IsColimit (Cofan.mk ((free R).obj (yoneda.obj (∐ X))) fun j => (free R).map (yoneda.map (Sigma.ι X j))))

def ChainsDiscCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q),
  Nonempty (IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))

def HKCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (K : ι → Cx R) (c : Cofan K), IsColimit c →
  ∀ (F : Shv R) (n : ℤ), Function.Bijective fun (x : HK R c.pt F n) (j : ι) => HK.pull R (c.inj j) F n x

theorem Coprod_of (h1 : FreeCoprod) (h2 : ChainsDiscCoprod) (h3 : HKCoprod) : LateralTheory.E.t_E3Cut.Coprod := by
  intro R _ F ι X n
  obtain ⟨hc⟩ := h2 R (fun j => yoneda.obj (X j)) (yoneda.obj (∐ X)) (fun j => yoneda.map (Sigma.ι X j)) (h1 R X)
  exact h3 R _ _ hc F n

end LateralTheory.E.CoprodPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SHExistsPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SHExistsPf

def SHLoc : Prop := ∀ (A : CommRingCat.{0}) [IsLocalRing A],
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O), IE f ∧ SH O ∧ IsLocalHom f.hom

def LocAt : Prop := ∀ (A : CommRingCat.{0}) (r : Ideal A) [r.IsPrime],
  IE (CommRingCat.ofHom (algebraMap A (Localization.AtPrime r)))

def Comp : Prop := ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), IE f → IE g → IE (f ≫ g)

theorem SHExists_of (hL : SHLoc) (hA : LocAt) (hC : Comp) : t_E3Cut.SHExists := by
  intro A r hr
  let L : CommRingCat.{0} := CommRingCat.of (Localization.AtPrime r)
  let g : A ⟶ L := CommRingCat.ofHom (algebraMap A (Localization.AtPrime r))
  haveI : IsLocalRing L := inferInstanceAs (IsLocalRing (Localization.AtPrime r))
  obtain ⟨O, h, hIE, hSH, hloc⟩ := hL L
  refine ⟨O, g ≫ h, hC g h (hA A r) hIE, hSH, fun a => ?_⟩
  have key : IsUnit (algebraMap A (Localization.AtPrime r) a) ↔ a ∈ r.primeCompl :=
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime r) r a
  have e : (g ≫ h).hom a = h.hom (algebraMap A (Localization.AtPrime r) a) := rfl
  rw [e]
  constructor
  · intro ha hu
    have := (key.1 (isUnit_of_map_unit h.hom _ hu))
    exact this ha
  · intro hn
    by_contra ha
    exact hn ((key.2 ha).map h.hom)

end LateralTheory.E.SHExistsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinEtSectionPf

def Pieces : Prop := LateralTheory.E.t_E1Cut.EtLift → LateralTheory.E.t_E1Cut.EtAIC → ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C], LateralTheory.E.t_E1Cut.QA S →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))))

def FinOpen : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C), IsIdempotentElem e →
  IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) →
  ∃ ε : S, IsIdempotentElem ε ∧
    Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum S)) ∧
    ∃ h : Localization.Away e →+* Localization.Away ε,
      h.comp ((algebraMap C (Localization.Away e)).comp (algebraMap S C)) = algebraMap S (Localization.Away ε)

def Glue : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] (n : ℕ) (e : Fin n → C),
  CompleteOrthogonalIdempotents e → Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) →
  ∀ ε : Fin n → S, (∀ j, IsIdempotentElem (ε j)) →
  (∀ j, Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S))) →
  (∀ j, ∃ h : Localization.Away (e j) →+* Localization.Away (ε j),
      h.comp ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C)) = algebraMap S (Localization.Away (ε j))) →
  Nonempty (C →ₐ[S] S)

theorem FinEtSection_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) (hP : Pieces) (hF : FinOpen) (hG : Glue) : LateralTheory.E.t_E1Cut.FinEtSection := by
  intro S C _ _ _ _ _ hQA hsurj
  obtain ⟨n, e, he, hoi⟩ := hP hL hA S C hQA
  choose ε hε hr hh using fun j => hF S C (e j) (he.idem j) (hoi j)
  exact hG S C n e he hsurj ε hε hr hh

end LateralTheory.E.FinEtSectionPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.AlgResPropsPf
open LateralTheory.E.t_E3Cut

theorem cancel {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : AlgRes (f ≫ g)) : AlgRes g := by
  intro Q hQ c
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := h Q hQ c
  refine ⟨p.map f.hom, ⟨n, ?_⟩, ?_⟩
  · rw [Polynomial.coeff_map]; simpa using hn
  · rw [Polynomial.eval₂_map]; simpa using hp

theorem integral {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.IsIntegral) : AlgRes f := by
  intro Q hQ c
  obtain ⟨p, hm, hp⟩ := h c
  refine ⟨p, ⟨p.natDegree, ?_⟩, ?_⟩
  · rw [← Polynomial.leadingCoeff, hm.leadingCoeff, map_one]
    exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  · rw [hp]; exact Q.zero_mem

theorem loc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] :
    AlgRes (CommRingCat.ofHom (algebraMap A B)) := by
  intro Q hQ c
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
  refine ⟨Polynomial.C (s : A) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
  · have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    intro hm
    apply hQ.ne_top
    apply Q.eq_top_of_isUnit_mem hm
    simpa [Polynomial.coeff_C, Polynomial.coeff_X] using hu
  · have := IsLocalization.mk'_spec B a s
    simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [mul_comm, this, sub_self]; exact Q.zero_mem

def Comp : Prop :=
  ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)

def Push : Prop :=
  ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v

def EtAlg : Prop := ∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f

theorem AlgResProps_of (h1 : Comp) (h2 : Push) (h3 : EtAlg) : LateralTheory.E.t_E3Cut.AlgResProps :=
  ⟨fun f g hf hg => h1 f g hf hg, fun f g h => cancel f g h, fun f g u v h hf => h2 f g u v h hf,
    fun f h => h3 f h, fun f h => integral f h, fun A B _ _ _ S _ => loc A B S⟩

end LateralTheory.E.AlgResPropsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwPairExistsPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwPairExistsPf

variable {R : Type} [CommRing R]

theorem res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using h.symm

theorem map_map {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

def post {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (Sec.map (u.f w) _) = Sec.map (u.f w) _
    rw [res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) _) =
      Sec.map (u.f (w + 1)) _ + s.negOnePow • Sec.map (u.f (w + 1)) _
    rw [map_map, u.comm w (w + 1), ← map_map, μ.leibniz]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit]

theorem post_mul {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : (post μ u).mul U s t w h a b = Sec.map (u.f w) (μ.mul U s t w h a b) := rfl

def LeafTwTensEx : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ),
  ∃ (T : Cx (ZMod q)) (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor

def LeafTwTensRes : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ) (T : Cx (ZMod q))
  (τ : Pair (res _ (tw q i)) (res _ (tw q j)) T), τ.IsTensor →
    IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ))

def LeafTwResExt : Prop := ∀ (q : ℕ) [NeZero q] (k : ℤ) (T : Cx (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
  IsTwRes q k T e → ∃ u : T ⟶ res _ (tw q k), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen k ζ

theorem LeafTwPairExists_of (h1 : LeafTwTensEx) (h2 : LeafTwTensRes) (h3 : LeafTwResExt) :
    LateralTheory.E.CupProductRingLaws.LeafTwPairExists := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 q i j
  obtain ⟨u, hu⟩ := h3 q (i + j) T _ (h2 q i j T τ hτ)
  exact ⟨post τ u, fun U ζ => by rw [post_mul]; exact hu U ζ⟩

end LateralTheory.E.LeafTwPairExistsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LineOneCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineOneCut

abbrev fib {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Scheme.{0} :=
  pullback p (cpt A)

def fibMap {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fib (ι ≫ p) ⟶ fib p :=
  pullback.map (ι ≫ p) (cpt A) p (cpt A) ι (𝟙 _) (𝟙 _) (by simp) (by simp)

def Charts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ

def FibCover : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A))
  (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  IsOpenImmersion (fibMap p ι₁) ∧ IsOpenImmersion (fibMap p ι₂) ∧ Set.range (fibMap p ι₁) ∪ Set.range (fibMap p ι₂) = Set.univ

def ChartAcyc : Prop := Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] {Z U : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z), IsOpenImmersion ι → IsAffine U → AICSch Z → IsUnit (q : A) →
  Acyc q (sch.obj (fib (ι ≫ p)))

def ChartSurj : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
    w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
      pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b

theorem goal_of (hMV : MV) (hC : Charts) (hF : FibCover) (hA : ChartAcyc) (hS : ChartSurj) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := hS H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.LineOneCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

def PolyPO : Prop := ∀ {A B : CommRingCat.{0}} (b : A ⟶ B),
  IsPushout (pC A) b (CommRingCat.ofHom (Polynomial.mapRingHom b.hom)) (pC B)

def IECob : Prop := ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D),
  IsPushout f g u v → IE f → IE v

def FracAIC : Prop := ∀ (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K], AIC T → AIC K

def FracOf : Prop := ∀ (B C : Type) [CommRing B] [CommRing C] [IsDomain C] (j : B →+* C), Function.Injective j →
  (∀ z : C, ∃ s y : B, s ≠ 0 ∧ j s * z = j y) →
  @IsFractionRing B _ (FractionRing C) _ ((algebraMap C (FractionRing C)).comp j).toAlgebra

theorem ULAStalk_of (hI : IntClos) (hT : SHTensor) (hA : AICSH) (hE : SHEqv) (hC3 : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial)
    (p1 : PolyPO) (p2 : IECob) (p3 : FracAIC) (p4 : FracOf) : ULAStalk := by
  intro H q _ i A X h hq hA' hX hh hloc C c _ _ hCa hCr Y' w φ' sq
  obtain ⟨B, b, j, hbj, hbint, hjinj, hBloc, hBaic, hfr⟩ := hI c hA' hCa hCr
  have : IsDomain B := Function.Injective.isDomain j.hom hjinj
  let K := FractionRing C
  let l : C ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap C K)
  let algBK : Algebra B K := ((algebraMap C K).comp j.hom).toAlgebra
  have : IsFractionRing B K := p4 B C j.hom hjinj hfr
  have hKsh : SH K := hA K (p3 C K hCa)
  have hBsh : SH B := hA B hBaic
  have hCsh : SH C := hA C hCa
  have hqB : IsUnit (q : B) := by simpa using hq.map b.hom
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom

  let mB : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial B) := CommRingCat.ofHom (Polynomial.mapRingHom b.hom)
  have sB : IsPushout h mB (pushout.inl h mB) (pushout.inr h mB) := IsPushout.of_hasPushout _ _
  have hBIE : IE (pushout.inr h mB) := p2 _ _ _ _ sB hh
  have sBA : IsPushout (pC A ≫ h) b (pushout.inl h mB) (pC B ≫ pushout.inr h mB) := (p1 b).paste_horiz sB
  let ZB : CommRingCat.{0} := pushout h mB
  have hZBsh : SH ZB := hT _ _ _ _ sBA hA' hX hloc hbint hBloc
  have r1 : RE q i (pC B ≫ pushout.inr h mB) := hE H q i _ hqB hBsh hZBsh
  let bl : B ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap B K)
  have sL : IsPushout (pC B ≫ pushout.inr h mB) bl (pushout.inl _ bl) (pushout.inr _ bl) := IsPushout.of_hasPushout _ _
  have r2 : RE q i (pushout.inl (pC B ≫ pushout.inr h mB) bl) :=
    hC3 H q i B K hBaic hqB (pushout h mB) (pushout.inr h mB) hBIE _ _ _ sL.flip
  have r3 : RE q i bl := hE H q i bl hqB hBsh hKsh
  have r4 : RE q i (pushout.inr (pC B ≫ pushout.inr h mB) bl) :=
    RE.of_comp_left r3 (by rw [← pushout.condition]; exact r1.comp r2)

  let mC : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial C) := CommRingCat.ofHom (Polynomial.mapRingHom c.hom)
  let hC : CommRingCat.of (Polynomial C) ⟶ Y' := (p1 c).desc (h ≫ w) φ' (by rw [← Category.assoc]; exact sq.w)
  have e1 : mC ≫ hC = h ≫ w := (p1 c).inl_desc _ _ _
  have e2 : pC C ≫ hC = φ' := (p1 c).inr_desc _ _ _
  have sC : IsPushout h mC w hC := IsPushout.of_left (by rw [e2]; exact sq) e1.symm (p1 c)
  have hCIE : IE hC := p2 _ _ _ _ sC hh
  have sq' : IsPushout l (pC C ≫ hC) (pushout.inr φ' l) (pushout.inl φ' l) := by
    rw [e2]; exact (IsPushout.of_hasPushout φ' l).flip
  have r5 : RE q i (pushout.inl φ' l) := hC3 H q i C K hCa hqC Y' hC hCIE _ _ _ sq'
  have r6 : RE q i l := hE H q i l hqC hCsh hKsh
  have ebl : b ≫ bl = c ≫ l := by rw [← hbj]; rfl
  have PZ : IsPushout (pC A ≫ h) (c ≫ l) (pushout.inl h mB ≫ pushout.inl (pC B ≫ pushout.inr h mB) bl)
      (pushout.inr (pC B ≫ pushout.inr h mB) bl) := by
    rw [← ebl]; exact sBA.paste_vert sL
  have PZ' : IsPushout (pC A ≫ h) (c ≫ l) (w ≫ pushout.inl φ' l) (pushout.inr φ' l) :=
    sq.paste_vert (IsPushout.of_hasPushout φ' l)
  have r7 : RE q i (pushout.inr φ' l) := by
    rw [← PZ.inr_isoIsPushout_hom _ _ PZ']; exact r4.comp (RE.of_isIso q i _)
  exact RE.of_comp_right r5 (by rw [pushout.condition]; exact r6.comp r7)

end LateralTheory.E.ULAStalkPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf
section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationNaturalInRestriction
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCochainEvaluationNaturalInRestriction : Prop :=
  ∀ {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U),
    ev (R := R) α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) =
      Sec.res g (ev (R := R) α p s h U x)

theorem freeGen_nat {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up (P.map g.op x)) := by
    simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]; erw [ModuleCat.free_map_apply]; rfl
  exact h.symm.trans (congrArg (toSheafify Scheme.etaleTopology ((freeP R).obj P) |>.app (op V)).hom hm)

theorem ev_nat_pf : EtaleCochainEvaluationNaturalInRestriction := by
  intro R _ E I n α p s h V U g x
  unfold ev
  rw [← freeGen_nat]
  have key := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at key
  exact key

end LateralTheory.EtaleFoundations
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneSpecPf

open LateralTheory.E.CupProductRingLaws

theorem res_neg_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) := by
  unfold res
  unfold InjectiveResolution.cochainComplex
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change ((i : ℤ)) < 0 at hn
  omega
theorem chains_pos_zero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) := by
  unfold chains
  simp only [Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj]
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change 0 < -((i : ℤ)) at hn
  omega
theorem free_hom_ext (R : Type) [CommRing R] (P : PSh) (G : Shv R) (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) :
    f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down
theorem cochain0_ext (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (α β : Cochain ((chains R).obj E) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α 0 0 (by simp) U x = ev (R := R) β 0 0 (by simp) U x) : α = β := by
  apply Cochain.ext
  intro p q hpq
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact (res_neg_zero R F q (by omega)).eq_of_tgt _ _
  · have key : (chainsXIso R E 0).inv ≫ α.v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).inv ≫ β.v (-((0 : ℕ) : ℤ)) 0 (by simp) :=
      free_hom_ext R _ _ _ _ (fun U x => h U x)
    obtain rfl : q = 0 := by omega
    simpa using key
  · exact (chains_pos_zero R E p hp).eq_of_src _ _

def LeafCochain0Ext : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (α β : Cochain ((chains R).obj E) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α 0 0 (by simp) U x = ev (R := R) β 0 0 (by simp) U x) → α = β

theorem leafCochain0Ext_pf : LeafCochain0Ext := fun R _ F E α β h => cochain0_ext R F E α β h

def LeafOneExists : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α, IsOneCocycle q E α

def LeafPrimCover : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Nonempty (Prim q Γ(V, ⊤))

def LeafSecPrimLocal : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (q : ℕ) [NeZero q] (U : Scheme.{0}) (a b : Sec F U),
  IsUnit (q : Γ(U, ⊤)) → (∀ (V : Scheme.{0}) (g : V ⟶ U), Nonempty (Prim q Γ(V, ⊤)) → Sec.res g a = Sec.res g b) → a = b

theorem sec_sep (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (a b : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g a = Sec.res g b) : a = b := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem leafSecPrimLocal_of (hP : LeafPrimCover) : LeafSecPrimLocal := by
  intro R _ F q _ U a b hq h
  obtain ⟨S, hS, hSP⟩ := hP q U hq
  exact sec_sep R F U S hS a b fun V g hg => h V g (hSP V g hg)

theorem one_cocycle_eq (hB : LeafCochain0Ext) (hC : LeafSecPrimLocal) (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : IsOneCocycle q E α) (hβ : IsOneCocycle q E β) :
    α = β := by
  apply Subtype.ext
  apply hB (ZMod q) (tw q 0) E α.1 β.1
  intro U x
  refine hC (ZMod q) _ q U _ _ (hE U ⟨x⟩) ?_
  rintro V g ⟨ζ⟩
  rw [← LateralTheory.EtaleFoundations.ev_nat_pf α.1 0 0 (by simp) g x, ← LateralTheory.EtaleFoundations.ev_nat_pf β.1 0 0 (by simp) g x]
  exact (hα V _ ζ).trans (hβ V _ ζ).symm

theorem LeafOneSpec_of (hA : LeafOneExists) (hP : LeafPrimCover) : LeafOneSpec := by
  have hB := leafCochain0Ext_pf
  have hC := leafSecPrimLocal_of hP
  intro q _ E hE
  refine ⟨hA q E hE, fun α hα => ?_⟩
  obtain ⟨α₀, h₀⟩ := hA q E hE
  obtain ⟨α₁, h₁, hα₁⟩ := pick_spec (P := fun c : Ht q E 0 0 => ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    CohomologyClass.mk α = c ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)),
      ev (R := ZMod q) α.1 0 0 (by simp) U x = resGen 0 ζ) ⟨CohomologyClass.mk α₀, α₀, rfl, h₀⟩
  change pick _ = _
  rw [← h₁, one_cocycle_eq hB hC q E hE α₁ α hα₁ hα]

end LateralTheory.E.LeafOneSpecPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafCompPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def LeafCoprod : Prop := Hyps → ∀ (q : ℕ) (n i : ℤ) (m : ℕ) (Z : Fin m → Scheme.{0}),
  (∀ j, Finite (Ht q (sch.obj (Z j)) n i)) → Finite (Ht q (sch.obj (∐ Z)) n i)

def LeafCompGeom : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p],
  ∃ (m : ℕ) (Z : Fin m → Scheme.{0}) (ι : ∀ j, Z j ⟶ X), (∀ j, IsClosedImmersion (ι j) ∧ IsIntegral (Z j)) ∧
    IsProper (Sigma.desc ι) ∧ Surjective (Sigma.desc ι)

theorem LeafComp_of (hC : LeafCoprod) (hG : LeafCompGeom) : LeafComp := by
  intro hH q k _ X p _ n i hZ
  obtain ⟨m, Z, ι, hι, hP, hS⟩ := hG k p
  exact ⟨∐ Z, Sigma.desc ι, hP, hS, hC hH q n i m Z (fun j => hZ (Z j) (ι j) (hι j).1 (hι j).2)⟩

end LateralTheory.E.E4
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SHSectionPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHSectionPf

def SHAlgSec : Prop := ∀ (A R : CommRingCat.{0}) (f : A ⟶ R), SH A → f.hom.Etale →
  (∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal) → ∃ σ : R ⟶ A, f ≫ σ = 𝟙 A

def EtAffNbhd : Prop := ∀ (A : CommRingCat.{0}) [Nontrivial A] {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ (R : CommRingCat.{0}) (f : A ⟶ R) (ι : Spec R ⟶ V), f.hom.Etale ∧ ι ≫ g = Spec.map f ∧
    ∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal

theorem SHSection_of (h1 : SHAlgSec) (h2 : EtAffNbhd) : LateralTheory.E.t_E3Cut.SHSection := by
  intro A hA V g _ _
  have : Nontrivial A := by obtain ⟨hH, -⟩ := hA; infer_instance
  obtain ⟨R, f, ι, hf, hι, hQ⟩ := h2 A g
  obtain ⟨σ, hσ⟩ := h1 A R f hA hf hQ
  refine ⟨Spec.map σ ≫ ι, ?_⟩
  rw [Category.assoc, hι, ← Spec.map_comp, hσ, Spec.map_id]

end LateralTheory.E.SHSectionPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IntPBPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.IntPBPf

def IntHens : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] [HenselianLocalRing A] (φ : A →+* B), φ.IsIntegral →
  HenselianRing B ((IsLocalRing.maximalIdeal A).map φ)

def IntFib : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)), IsIntegralHom p →
  ∃ (B : Type) (_ : CommRing B) (φ : A →+* B), φ.IsIntegral ∧ ∀ (q : ℕ) (i : ℤ),
    Eqv _ (spMap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map φ))) (tw q i) →
    Eqv _ (sch.map (pullback.fst p (LateralTheory.E.t_E2Cut.cpt A))) (tw q i)

theorem IntPB_of (hH : IntHens) (hF : IntFib) : LateralTheory.E.t_E2Cut.IntPB := by
  intro hyp q i A _ _ hSH hq X p hp
  obtain ⟨hA, -⟩ := hSH
  obtain ⟨B, _, φ, hφ, hE⟩ := hF A p hp
  have : HenselianRing B ((IsLocalRing.maximalIdeal A).map φ) := hH A B φ hφ
  have hqB : IsUnit ((q : ℕ) : B) := by simpa using hq.map φ
  exact hE q i (hyp.e1 q B _ hqB i)

end LateralTheory.E.IntPBPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GlobalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.GlobalPf

def gam {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens) : T ⟶ Γ(X, V) :=
  (Scheme.ΓSpecIso T).inv ≫ p.appLE ⊤ V (by simp)

def Affine : Prop := ∀ (q : ℕ) (i : ℤ) {T K : CommRingCat.{0}} (k : T ⟶ K) {X : Scheme.{0}} (p : X ⟶ Spec T) (V : X.Opens),
  IsAffineOpen V → BC q i k (gam p V) → Eqv _ (sch.map (pullback.fst p (Spec.map k) ∣_ V)) (tw q i)

def LocEt : Prop := ∀ {T : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec T) [Smooth p] (x : X),
  ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧ ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
    ∃ c : CommRingCat.of (MvPolynomial (Fin n) T) ⟶ Γ(X, V), Et c ∧
      CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T) ≫ c = gam p V

theorem Global_of (hZ : ZarLocal) (hA : Affine) (hL : LocEt) : Global := by
  intro H q i T K k hG X p _
  refine hZ H (ZMod q) (tw q i) (pullback.fst p (Spec.map k)) fun x => ?_
  obtain ⟨U, n, hx, hU⟩ := hL p x
  refine ⟨U, hx, fun V hV hVU => ?_⟩
  obtain ⟨c, hc, hcg⟩ := hU V hV hVU
  have hb := hG n _ c hc
  rw [hcg] at hb
  exact hA q i k p V hV hb

end LateralTheory.E.GlobalPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.HZeroPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.HZeroPf

open LateralTheory.E.t_E2Cut

def RootAIC : Prop := ∀ (q : ℕ) (X : Scheme.{0}), AICSch X → IsUnit (q : Γ(X, ⊤)) → Nonempty (Prim q Γ(X, ⊤))

def ResBij : Prop := ∀ (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X), ConnectedSpace Y → ConnectedSpace X →
  Nonempty (Prim q Γ(X, ⊤)) → Function.Bijective (Sec.res (F := tw q i) f)

theorem connected_of_AICSch {X : Scheme.{0}} (h : AICSch X) : ConnectedSpace X := by
  have := h.1
  infer_instance

theorem HZero_of (hR : RootAIC) (hB : ResBij) : LateralTheory.E.t_E2Cut.HZero := by
  intro hyp q Y X f hX hY hq i
  obtain ⟨_, e, he, _⟩ := hyp.a9 (ZMod q) (tw q i)
  have := connected_of_AICSch hX
  have hres := hB q i f hY (connected_of_AICSch hX) (hR q X hX hq)
  have key : (pull (ZMod q) (sch.map f) (tw q i) 0) = (e Y).toAddMonoidHom.comp
      ((AddMonoidHom.mk' (Sec.res (F := tw q i) f) (fun a b => map_add _ a b)).comp (e X).symm.toAddMonoidHom) := by
    ext x
    obtain ⟨s, rfl⟩ := (e X).surjective x
    simp [he]
  rw [key]
  exact (e Y).bijective.comp (hres.comp (e X).symm.bijective)

end LateralTheory.E.HZeroPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ZarLocalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZarLocalPf

def LocSH : Prop := ∀ (S : Type) [CommRing S], AIC S → ∀ p : PrimeSpectrum S, SH (Localization.AtPrime p.asIdeal)

def LocDiag : Prop := ∀ (S : Type) [CommRing S] (p : PrimeSpectrum S),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
    Nonempty (IsColimit c) ∧ (SH (Localization.AtPrime p.asIdeal) → SH c.pt) ∧
    ∃ (j0 : J) (a : S →+* D.obj j0), ∀ (k : J) (m : j0 ⟶ k), ∃ f : S, f ∉ p.asIdeal ∧
      ∃ r : D.obj k →+* Localization.Away f, r.comp ((D.map m).hom.comp a) = algebraMap S (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem ZarLocal_of (hSH : LocSH) (hD : LocDiag) : LateralTheory.E.t_E1Cut.ZarLocal := by
  intro hB1 hB2 q S _ hS hq n i hn x p
  obtain ⟨J, _, _, D, c, ⟨hc⟩, hpt, j0, a, hk⟩ := hD S p
  have hsh : SH c.pt := hpt (hSH S hS p)
  set y := pull _ (spMap a) _ _ x with hy
  have hqa : IsUnit ((q : ℕ) : D.obj j0) := by simpa using hq.map a
  have h0 : pull _ (spMap (c.ι.app j0).hom) _ _ y = 0 := by
    exact @Subsingleton.elim _ (hB2 (ZMod q) c.pt hsh (tw q i) n hn) _ _
  obtain ⟨k, m, hm⟩ := (hB1 q D c hc n i).2 j0 y hqa h0
  obtain ⟨f, hf, r, hr⟩ := hk k m
  refine ⟨f, hf, ?_⟩
  rw [← hr, spMap_comp, pull_comp, spMap_comp, pull_comp, ← hy, hm, map_zero]

end LateralTheory.E.ZarLocalPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPicCut
noncomputable section
open nonZeroDivisors

namespace LateralTheory.E.LeafPicCut

def sel (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (FractionRing B)ˣ :=
  (powMonoidHom q : (FractionalIdeal B⁰ (FractionRing B))ˣ →* _).range.comap (toPrincipalIdeal B (FractionRing B))

abbrev selPow (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (sel B q) :=
  (powMonoidHom q : (FractionRing B)ˣ →* (FractionRing B)ˣ).range.subgroupOf (sel B q)

abbrev selQ (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Type := sel B q ⧸ selPow B q

def LeafSelPic : Prop := ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (q : ℕ) [NeZero q],
  Finite (selQ B q) → Finite {c : ClassGroup B // c ^ q = 1}

end LateralTheory.E.LeafPicCut
end
end
