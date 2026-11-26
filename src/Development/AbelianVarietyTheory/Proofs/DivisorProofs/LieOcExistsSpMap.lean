module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzLieConditionLocallyCutOutByIdealStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal
noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PtClosed

def killIdeal {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop) :
    Ideal A where
  carrier := {a | ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f → f a = 0}
  add_mem' {a b} ha hb R' _ f hf := by rw [map_add (f := _), ha R' f hf, hb R' f hf, add_zero]
  zero_mem' R' _ f _ := map_zero f
  smul_mem' c a ha R' _ f hf := by rw [smul_eq_mul, map_mul, ha R' f hf, mul_zero]

def Represents {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop)
    (J : Ideal A) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f ↔ J ≤ RingHom.ker f

def ptQ {S : Scheme.{0}} (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop) (V : S.Opens)
    (hV : IsAffineOpen V) : ∀ (R' : Type) [CommRing R'], (Γ(S, V) →+* R') → Prop :=
  fun R' _ f ↦ P R' (spMap f ≫ hV.fromSpec)

theorem killIdeal_eq {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    killIdeal Q = J := by
  apply le_antisymm
  · intro a ha
    have := ha (A ⧸ J) (Ideal.Quotient.mk J) ((h _ _).2 (by simp [Ideal.mk_ker]))
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
  · intro a ha R' _ f hf
    exact (h R' f).1 hf ha

theorem represents_killIdeal {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    Represents Q (killIdeal Q) := by
  rw [killIdeal_eq h]; exact h

theorem represents_restrict : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
  (U W : S.Opens) (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (J : Ideal Γ(S, U)),
  Represents (ptQ P U hU) J → Represents (ptQ P W hW) (J.map (S.presheaf.map (homOfLE h).op).hom) := by
  intro S P U W hU hW h J hJ R' _ f
  have e : spMap f ≫ hW.fromSpec =
      spMap (f.comp (S.presheaf.map (homOfLE h).op).hom) ≫ hU.fromSpec := by
    rw [← hU.map_fromSpec hW (homOfLE h).op]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap f ≫ hW.fromSpec) ↔ _
  rw [e, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfLocalIdealPointProperty
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealKilledByRingMapsWithPropertyLeKerApp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealKilledByRingMapsWithPropertyLeKerApp
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem fromSpec_Sp_eq (R' : Type) [CommRing R'] {W : (Sp R').Opens} (hW : IsAffineOpen W) :
    hW.fromSpec = spMap ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
      (Sp R').presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (𝟙 (Sp R')) (isAffineOpen_top (Sp R')) hW le_top
  rw [Category.comp_id, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  rw [← h]
  simp [spMap, Scheme.Hom.appLE]

theorem killIdeal_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  intro S P hP R' _ x hx V hV a ha
  rw [RingHom.mem_ker]
  apply (Sp R').IsSheaf.section_ext
  intro p hp
  obtain ⟨W, hWa, hpW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Sp R').isBasis_affineOpens) hp
  refine ⟨W, hWle, hpW, ?_⟩
  have hW : IsAffineOpen W := hWa
  have e : hW.fromSpec ≫ x = spMap (x.appLE V W hWle).hom ≫ hV.fromSpec := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec x hV hW hWle]; rfl
  have hy : ptQ P V hV _ (x.appLE V W hWle).hom := by
    show P _ (spMap (x.appLE V W hWle).hom ≫ hV.fromSpec)
    rw [← e, fromSpec_Sp_eq]
    exact hP _ _ _ x hx
  have h0 := ha _ _ hy
  rw [map_zero]
  simpa [Scheme.Hom.appLE] using h0

end GlobalTheory.PtClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealKilledByRingMapsWithPropertyLeKerAppStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealKilledByRingMapsWithProperty_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
    P R' x → P R'' (spMap g ≫ x)) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), P R' x →
    ∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom := by
  first | exact @GlobalTheory.PtClosed.killIdeal_le_ker_app | exact GlobalTheory.PtClosed.killIdeal_le_ker_app | (intros; apply GlobalTheory.PtClosed.killIdeal_le_ker_app; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealRepresentsOfAwayCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealRepresentsOfAwayCover
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem exists_pow_mul_eq_zero_of_represents_away {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop}
    (hbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
      Q R' f → Q R'' (g.comp f))
    (a : A) {Ja : Ideal (Localization.Away a)}
    (hJa : Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) Ja)
    {R' : Type} [CommRing R'] (f : A →+* R') (hf : Q R' f) (x : A)
    (hx : algebraMap A (Localization.Away a) x ∈ Ja) : ∃ m : ℕ, f a ^ m * f x = 0 := by
  have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
      (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
  have h1 : Q _ ((algebraMap R' (Localization.Away (f a))).comp f) :=
    hbc _ _ (algebraMap R' (Localization.Away (f a))) f hf
  rw [← e] at h1
  have h2 := (hJa _ (Localization.awayMap f a)).1 h1 hx
  rw [RingHom.mem_ker, ← RingHom.comp_apply, e, RingHom.comp_apply,
    IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))] at h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := h2
  exact ⟨m, hm⟩

theorem represents_of_away_cover : ∀ (A : Type) [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
    Q R' f → Q R'' (g.comp f)) →
  (∀ (R' : Type) [CommRing R'] (f : A →+* R') (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, Q (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) → Q R' f) →
  ∀ (s : Finset A), Ideal.span (s : Set A) = ⊤ →
  (∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
    Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) J) →
  ∃ J : Ideal A, Represents Q J := by
  classical
  intro A _ Q hbc hloc s hs hJ
  choose! J' hJ' using hJ
  refine ⟨⨅ a ∈ s, (J' a).comap (algebraMap A (Localization.Away a)),
    fun R' _ f ↦ ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩⟩
  · intro x hx
    simp only [Submodule.mem_iInf, Ideal.mem_comap] at hx
    rw [RingHom.mem_ker]
    have hspan : Ideal.span ((f : A → R') '' (s : Set A)) = ⊤ := by
      rw [← Ideal.map_span, hs, Ideal.map_top]
    have := Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R' R') _ hspan (f x) ?_
    · simpa using this
    rintro ⟨_, b, hb, rfl⟩
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc b (hJ' b hb) f hf x (hx b hb)
    exact ⟨m, by simpa [smul_eq_mul] using hm⟩
  · apply hloc R' f (s.image f)
    · rw [Finset.coe_image, ← Ideal.map_span, hs, Ideal.map_top]
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hr
    have e : (Localization.awayMap f a).comp (algebraMap A (Localization.Away a)) =
        (algebraMap R' (Localization.Away (f a))).comp f := IsLocalization.map_comp _
    rw [← e]
    refine ((hJ' a ha) _ (Localization.awayMap f a)).2 ?_
    intro j hj
    obtain ⟨⟨y, _, n, rfl⟩, hy⟩ := IsLocalization.surj (Submonoid.powers a) j
    simp only at hy
    have hyJ : algebraMap A (Localization.Away a) y ∈ J' a := hy ▸ Ideal.mul_mem_right _ _ hj
    have hb : ∀ b ∈ s, ∃ m : ℕ, algebraMap A (Localization.Away b) (a ^ m * y) ∈ J' b := by
      intro b hbs
      let p : A →+* (Localization.Away b ⧸ J' b) :=
        (Ideal.Quotient.mk (J' b)).comp (algebraMap A (Localization.Away b))
      have hp : Q _ p := ((hJ' b hbs) _ (Ideal.Quotient.mk (J' b))).2 (by rw [Ideal.mk_ker])
      obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_represents_away hbc a (hJ' a ha) p hp y hyJ
      refine ⟨m, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [p] using hm
    choose! m hm using hb
    have hM : a ^ (s.sup m) * y ∈ ⨅ b ∈ s, (J' b).comap (algebraMap A (Localization.Away b)) := by
      simp only [Submodule.mem_iInf, Ideal.mem_comap]
      intro b hbs
      have : a ^ (s.sup m) * y = a ^ (s.sup m - m b) * (a ^ m b * y) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup hbs)]
      rw [this, map_mul]
      exact Ideal.mul_mem_left _ _ (hm b hbs)
    have h0 := hf hM
    rw [RingHom.mem_ker, map_mul, map_pow] at h0
    rw [RingHom.mem_ker]
    have hu : IsUnit (Localization.awayMap f a (algebraMap A _ (a ^ n))) := by
      rw [← RingHom.comp_apply, e, RingHom.comp_apply, map_pow]
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (f a)) (f a)).pow n
    have h3 : Localization.awayMap f a j * Localization.awayMap f a (algebraMap A _ (a ^ n)) = 0 := by
      rw [← map_mul, hy, ← RingHom.comp_apply, e, RingHom.comp_apply,
        IsLocalization.map_eq_zero_iff (Submonoid.powers (f a))]
      exact ⟨⟨_, s.sup m, rfl⟩, h0⟩
    exact (hu.mul_left_eq_zero).1 h3

end GlobalTheory.PtClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealRepresentsOfAwayCoverStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealRepresents_of_away_cover : ∀ (A : Type) [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (f : A →+* R'),
    Q R' f → Q R'' (g.comp f)) →
  (∀ (R' : Type) [CommRing R'] (f : A →+* R') (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
    (∀ r ∈ t, Q (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) → Q R' f) →
  ∀ (s : Finset A), Ideal.span (s : Set A) = ⊤ →
  (∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
    Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
      Q R' (h.comp (algebraMap A (Localization.Away a)))) J) →
  ∃ J : Ideal A, Represents Q J := by
  first | exact @GlobalTheory.PtClosed.represents_of_away_cover | exact GlobalTheory.PtClosed.represents_of_away_cover | (intros; apply GlobalTheory.PtClosed.represents_of_away_cover; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverIdealRepresents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverIdealRepresents
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

noncomputable section

namespace GlobalTheory.PtClosed

theorem represents_away (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
    (V : S.Opens) (hV : IsAffineOpen V) (a : Γ(S, V)) (J : Ideal Γ(S, S.basicOpen a))
    (hJ : Represents (ptQ P (S.basicOpen a) (hV.basicOpen a)) J) :
    ∃ J' : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J' := by
  let ρ := (S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom
  letI : Algebra Γ(S, V) Γ(S, S.basicOpen a) := ρ.toAlgebra
  haveI : IsLocalization.Away a Γ(S, S.basicOpen a) := hV.isLocalization_basicOpen a
  let e : Localization.Away a ≃ₐ[Γ(S, V)] Γ(S, S.basicOpen a) :=
    IsLocalization.algEquiv (Submonoid.powers a) (Localization.Away a) Γ(S, S.basicOpen a)
  refine ⟨J.map (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a), ?_⟩
  intro R' _ h
  have hc : h.comp (algebraMap Γ(S, V) (Localization.Away a)) =
      (h.comp (e.symm : Γ(S, S.basicOpen a) →+* Localization.Away a)).comp ρ := by
    ext x
    simp only [RingHom.comp_apply]
    congr 1
    have := e.symm.commutes x
    rw [← this]
    rfl
  have hs : ∀ g : Γ(S, S.basicOpen a) →+* R',
      spMap (g.comp ρ) ≫ hV.fromSpec = spMap g ≫ (hV.basicOpen a).fromSpec := by
    intro g
    rw [← hV.map_fromSpec (hV.basicOpen a) (homOfLE (S.basicOpen_le a)).op]
    simp only [ρ, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap _ ≫ hV.fromSpec) ↔ _
  rw [hc, hs, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem affine_local_represents : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∀ (V : S.Opens) (hV : IsAffineOpen V), ∃ s : Finset Γ(S, V), Ideal.span (s : Set Γ(S, V)) = ⊤ ∧
    ∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J := by
  intro S P hcov V hV
  let T : Set Γ(S, V) := {a | ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J}
  have hT : Ideal.span T = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro z hzV
    obtain ⟨U, hU, hzU, K, hK⟩ := hcov z
    obtain ⟨a, b, hab, hz⟩ := exists_basicOpen_le_affine_inter hV hU z ⟨hzV, hzU⟩
    have hle : S.basicOpen a ≤ U := hab ▸ S.basicOpen_le b
    have hJ := represents_restrict S P U (S.basicOpen a) hU (hV.basicOpen a) hle K hK
    have haT : a ∈ T := represents_away S P V hV a _ hJ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, haT⟩, hz⟩
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).1 hT
  exact ⟨s, hs, fun a ha ↦ hsT ha⟩

end GlobalTheory.PtClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverIdealRepresentsStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_cover_idealRepresents : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
    ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∀ (V : S.Opens) (hV : IsAffineOpen V), ∃ s : Finset Γ(S, V), Ideal.span (s : Set Γ(S, V)) = ⊤ ∧
    ∀ a ∈ s, ∃ J : Ideal (Localization.Away a),
      Represents (fun (R' : Type) [CommRing R'] (h : Localization.Away a →+* R') ↦
        ptQ P V hV R' (h.comp (algebraMap Γ(S, V) (Localization.Away a)))) J := by
  first | exact @GlobalTheory.PtClosed.affine_local_represents | exact GlobalTheory.PtClosed.affine_local_represents | (intros; apply GlobalTheory.PtClosed.affine_local_represents; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPropertyOfLeKerApp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPropertyOfLeKerApp
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  intro S P hloc hrep R' _ x hx
  have key : ∀ (V : S.Opens) (hV : IsAffineOpen V) (r : R'),
      (∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V) →
      P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x) := by
    intro V hV r hsub
    have e : (⊤ : (Sp (Localization.Away r)).Opens) ≤
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) ⁻¹ᵁ V := by
      intro q _
      show x.base ((spMap (algebraMap R' (Localization.Away r))).base q) ∈ V
      apply hsub
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit r))
    let g' : Γ(S, V) ⟶ CommRingCat.of (Localization.Away r) :=
      (spMap (algebraMap R' (Localization.Away r)) ≫ x).appLE V ⊤ e ≫ (Scheme.ΓSpecIso _).hom
    have hy : spMap (algebraMap R' (Localization.Away r)) ≫ x = spMap g'.hom ≫ hV.fromSpec := by
      have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (spMap (algebraMap R' (Localization.Away r)) ≫ x) hV
        (isAffineOpen_top (Sp (Localization.Away r))) e
      rw [IsAffineOpen.fromSpec_top] at h1
      rw [(Iso.inv_comp_eq _).1 h1.symm, Scheme.isoSpec_Spec_hom]
      simp only [spMap, CommRingCat.ofHom_hom, g', Spec.map_comp, Category.assoc]
    have hker : killIdeal (ptQ P V hV) ≤ RingHom.ker g'.hom := by
      refine (hx V hV).trans ?_
      intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      have hg : g' = x.app V ≫ ((spMap (algebraMap R' (Localization.Away r))).appLE (x ⁻¹ᵁ V) ⊤ e ≫
          (Scheme.ΓSpecIso _).hom) := by
        simp only [g', Scheme.Hom.comp_appLE, Category.assoc]
      rw [hg, CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
    have := (hrep V hV (Localization.Away r) g'.hom).2 hker
    rw [hy]
    exact this
  let G : Set R' := {r | ∃ V : S.Opens, IsAffineOpen V ∧ ∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V}
  have hG : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum R' := ⟨m, hm.isPrime⟩
    obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
      (show x.base p ∈ (⊤ : S.Opens) from trivial)
    have hpV' : p ∈ (x ⁻¹ᵁ V : TopologicalSpace.Opens (PrimeSpectrum R')) := hpV
    obtain ⟨W, ⟨r, rfl⟩, hpW, hW⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (PrimeSpectrum.isBasis_basic_opens (R := R'))) hpV'
    have hr : r ∈ G := ⟨V, hV, fun q hq => hW (show q ∈ PrimeSpectrum.basicOpen r from hq)⟩
    exact hpW (hle (Ideal.subset_span hr))
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine hloc R' x t hspan fun r hr => ?_
  obtain ⟨V, hV, hsub⟩ := ht hr
  exact key V hV r hsub

end GlobalTheory.PtClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPropertyOfLeKerAppStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affinePointProperty_of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  first | (exact @GlobalTheory.PtClosed.of_le_ker_app) | (exact GlobalTheory.PtClosed.of_le_ker_app) | (intros; apply GlobalTheory.PtClosed.of_le_ker_app  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfLocalIdealPointProperty
noncomputable section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PtClosed

theorem closed_of_points : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S), P R' x → P R'' (spMap g ≫ x)) →
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
     ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
    ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), (∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ P R' x := by
  intro S P hBC hLoc hCov
  have hrep : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      Represents (ptQ P V hV) (killIdeal (ptQ P V hV)) := by
    intro V hV
    obtain ⟨s, hs, hJ⟩ := GlobalTheory.T.exists_basicOpen_cover_idealRepresents S P hCov V hV
    have hQbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'')
        (f : Γ(S, V) →+* R'), ptQ P V hV R' f → ptQ P V hV R'' (g.comp f) := by
      intro R' _ R'' _ g f hf
      have := hBC R' R'' g _ hf
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    have hQloc : ∀ (R' : Type) [CommRing R'] (f : Γ(S, V) →+* R') (t : Finset R'),
        Ideal.span (t : Set R') = ⊤ →
        (∀ r ∈ t, ptQ P V hV (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) →
        ptQ P V hV R' f := by
      intro R' _ f t ht H
      refine hLoc R' _ t ht fun r hr ↦ ?_
      have := H r hr
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    obtain ⟨J, hJ'⟩ := GlobalTheory.T.idealRepresents_of_away_cover Γ(S, V) (ptQ P V hV) hQbc hQloc s hs hJ
    exact represents_killIdeal hJ'
  let I : S.IdealSheafData :=
    { ideal := fun V ↦ killIdeal (ptQ P V.1 V.2)
      map_ideal_basicOpen := fun U f ↦ by
        have h1 := represents_restrict S P U.1 (S.basicOpen f) U.2 (U.2.basicOpen f) (S.basicOpen_le f) _
          (hrep U.1 U.2)
        exact (killIdeal_eq h1).symm }
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun R' _ x ↦ ?_⟩
  have key : I ≤ x.ker ↔ P R' x := by
    rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
    constructor
    · intro h
      exact GlobalTheory.T.affinePointProperty_of_le_ker_app S P hLoc hrep R' x fun V hV ↦ h ⟨V, hV⟩
    · intro h V
      exact GlobalTheory.T.idealKilledByRingMapsWithProperty_le_ker_app S P hBC R' x h V.1 V.2
  rw [← key]
  constructor
  · rintro ⟨y, rfl⟩
    have := y.le_ker_comp I.subschemeι
    rwa [Scheme.IdealSheafData.ker_subschemeι] at this
  · intro h
    exact ⟨IsClosedImmersion.lift I.subschemeι x (by rwa [Scheme.IdealSheafData.ker_subschemeι]),
      IsClosedImmersion.lift_fac _ _ _⟩
end GlobalTheory.PtClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfLocalIdealPointPropertyStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_of_local_ideal_point_property : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S), P R' x → P R'' (spMap g ≫ x)) →
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
     ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
    ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), (∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ P R' x := by
  first | exact @GlobalTheory.PtClosed.closed_of_points | exact GlobalTheory.PtClosed.closed_of_points | (intros; apply GlobalTheory.PtClosed.closed_of_points <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieOc_spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {f g : R₁ →+* R₂} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem lieOc_exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (y : Sp R₂ ⟶ Sp R₁) : ∃ f : R₁ →+* R₂, y = spMap f :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

theorem lieOc_spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem lieHer_closed (b : Base D R) (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : Smooth A.hom) (act : OActN D.O A) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
        ((∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ LieHer b act β x) := by
  let P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop := fun R' _ x =>
    ∀ β : R →+* R', x ≫ s = spMap β → LieHer b act β x
  have hP : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
      (P R' x ↔ LieHer b act β x) := by
    intro R' _ β x hx
    refine ⟨fun h => h β hx, fun h β' hx' => ?_⟩
    have : β' = β := lieOc_spMap_inj (hx'.symm.trans hx)
    subst this; exact h

  have her : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
      P R' x → P R'' (spMap g ≫ x) := by
    intro R' _ R'' _ g x hx β'' hβ''
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ s)
    have e : β'' = g.comp β := lieOc_spMap_inj (by rw [← hβ'', Category.assoc, hβ, lieOc_spMap_comp])
    subst e
    intro R''' _ g'
    have h := hx β hβ R''' (g'.comp g)
    rw [← lieOc_spMap_comp] at h
    simpa [Category.assoc, RingHom.comp_assoc] using h

  have loc : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
      (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x := by
    classical
    intro R' _ x t ht hloc β hβ R'' _ g
    have hloc' : ∀ r ∈ t, LieHer b act ((algebraMap R' (Localization.Away r)).comp β)
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) := fun r hr =>
      hloc r hr _ (by rw [Category.assoc, hβ, lieOc_spMap_comp])
    have key : ∀ r : R', (Localization.awayMap g r).comp (algebraMap R' (Localization.Away r)) =
        (algebraMap R'' (Localization.Away (g r))).comp g := fun r => IsLocalization.map_comp _
    refine ⟨?_, ?_⟩
    · refine GlobalTheory.T.harrisTaylor_lie_condition_of_basicOpen_cover p D R b S A act R'' (g.comp β) (spMap g ≫ x) (t.image g) ?_ ?_
      · rw [Finset.coe_image, ← Ideal.map_span, ht, Ideal.map_top]
      · intro r'' hr''
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr''
        have h := (hloc' r hr (Localization.Away (g r)) (Localization.awayMap g r)).1
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc, key] at h
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc]
        exact h
    · intro k _ _ g' i
      have hex : ∃ r ∈ t, g' (g r) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have : Ideal.span (t : Set R') ≤ RingHom.ker (g'.comp g) :=
          Ideal.span_le.2 fun r hr => by simpa using hcon r hr
        rw [ht] at this
        have h1 : (1 : R') ∈ RingHom.ker (g'.comp g) := this Submodule.mem_top
        simp at h1
      obtain ⟨r, hr, hne⟩ := hex
      let hr' : Localization.Away r →+* k := IsLocalization.Away.lift r (g := g'.comp g) (isUnit_iff_ne_zero.2 hne)
      have hlift : hr'.comp (algebraMap R' (Localization.Away r)) = g'.comp g :=
        IsLocalization.Away.lift_comp r _
      have h := (hloc' r hr (Localization.Away r) (RingHom.id _)).2 k hr' i
      have e1 : spMap hr' ≫ spMap (RingHom.id (Localization.Away r)) ≫ spMap (algebraMap R' (Localization.Away r)) ≫ x =
          spMap g' ≫ spMap g ≫ x := by
        simp only [← Category.assoc, lieOc_spMap_comp]
        rw [RingHom.id_comp, hlift]
      have e2 : hr'.comp ((RingHom.id _).comp ((algebraMap R' (Localization.Away r)).comp β)) = g'.comp (g.comp β) := by
        rw [RingHom.id_comp, ← RingHom.comp_assoc, hlift, RingHom.comp_assoc]
      rw [e1, e2] at h
      exact h
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_of_local_ideal_point_property S P her loc (fun z => by
    obtain ⟨U, hU, hz, K, hK⟩ := GlobalTheory.T.kottwitzLieCondition_locally_cut_out_by_ideal p D R b S s A hA act z
    refine ⟨U, hU, hz, K, fun R' _ f => ?_⟩
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (spMap f ≫ hU.fromSpec ≫ s)
    rw [hP R' β _ (by rw [Category.assoc]; exact hβ)]
    exact hK R' f β hβ)
  exact ⟨Z, i, hi, fun R' _ β x hx => (hZ R' x).trans (hP R' β x hx)⟩

end GlobalTheory.UPel.HT
