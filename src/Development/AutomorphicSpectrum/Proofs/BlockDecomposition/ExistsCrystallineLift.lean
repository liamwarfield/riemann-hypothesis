module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLift
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CLiftEx

theorem thick_isNilpotent {b : Base} {L : b.Fun} (T : Thick L) (x : T.B) (hx : x ∈ T.J) :
    IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨k, hk⟩ := T.adm.2 hp
    refine ⟨k, ?_⟩
    simpa [hk] using Ideal.pow_mem_pow hx k
  · obtain ⟨k, hk⟩ := T.adm.1 hp
    refine ⟨b.p * k, ?_⟩
    have hfac : ((b.p.factorial : ℕ) : T.B) = (b.p : T.B) * ((b.p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, ← T.δ.factorial_mul_dpow_eq_pow hx, hfac, mul_assoc, mul_pow, hk, zero_mul]

theorem unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * c - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hc, Units.mul_inv, map_one, sub_self]
  have hunit : IsUnit (a * c) := by
    have h1 := (hJ _ hmem).isUnit_one_add
    have h2 : (1 : B) + (a * c - 1) = a * c := by ring
    rwa [h2] at h1
  obtain ⟨w, hw⟩ := isUnit_of_mul_isUnit_left hunit
  exact ⟨w, by rw [hw, ha]⟩

theorem nonempty_cLift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  intro O _ X q b ht κ C _ G D h
  classical
  choose p hp using h
  refine ⟨⟨p, hp, fun {T T'} φ =>
    if h : (B.thSp (G.map φ) ≫ p T) ≫ D.f = p T' ≫ D.f then
      (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
          (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose
    else 1, fun {T T'} φ h => ?_⟩⟩
  rw [dite_eq_left h]
  exact (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
      (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose_spec

end GlobalTheory.CompanionTheory.CLiftEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLiftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_lift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  first | exact @GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | exact GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift | (intros; apply GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransfer
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.PolyTfCon

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

section Thickening

variable (T : Thick (nlFun γ 0 X q κ)) {l s : ℕ} (hT : TF l s T)


include hT in
theorem tr_facts : fil (trD T s) s = ⊥ ∧
    (∀ (r : ℕ) (x : trB T s), (l : trB T s) * x ∈ fil (trD T s) r → x ∈ fil (trD T s) r) ∧
    IsNilpotent (trJ T s) :=
  GlobalTheory.CompanionTheory.SiteTr.tr_tf T.δ l s (trD T s) (trD_spec T s).1 hT.1 hT.2

abbrev pT : Thick (nlFun γ 0 X q κ) :=
  polyTr T s ⟨fun h => absurd rfl h, fun _ => (tr_facts T hT).2.2⟩

abbrev jT : T ⟶ pT T hT := homOf _ _ _ _ _ _ _

theorem pT_tf : TF l s (pT T hT) := ⟨(tr_facts T hT).1, (tr_facts T hT).2.1⟩

abbrev xT : trB T s := Ideal.Quotient.mk (trI T s) ((pq T.B).e 1)

theorem e_mem (B : Type) [CommRing B] (J : Ideal B) : (pq B).e 1 ∈ (pq B).ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem xT_mem : xT (s := s) T ∈ trJ T s := Ideal.mem_map_of_mem _ (e_mem _ _)

theorem sum_eq (b : ℕ →₀ T.B) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) =
      Ideal.Quotient.mk (trI T s) (b.sum fun k c => algebraMap T.B (pq T.B).P c * (eta T.δ).dpow k ((pq T.B).e 1)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, (trD_spec T s).1.dpow_comp _ (e_mem _ _)]
  rfl

theorem toNat_sub (r : ℤ) (k : ℕ) : (r - k).toNat = r.toNat - k := by omega

theorem fil_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈ fil (trD T s) r.toNat ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) 0).1

theorem std_coeff (b : ℕ →₀ T.B) (r : ℤ) (hr : r ≤ s) (c : R) :
    (b.sum fun k c => trF T s c * (trD T s).dpow k (xT (s := s) T)) ∈
        fil (trD T s) r.toNat ⊔ Ideal.span {Ideal.Quotient.mk (trI T s) (algebraMap T.B (pq T.B).P (T.i c))} ↔
      ∀ k : ℕ, b k ∈ fil T.δ (r - k).toNat ⊔ Ideal.span {T.i c} := by
  rw [sum_eq]
  simpa only [toNat_sub] using
    (GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit T.δ s (trD T s) (trD_spec T s).1 b r.toNat (by omega) (T.i c)).2

theorem univ_tr {T' : Thick (nlFun γ 0 X q κ)} (hT' : T'.pdPow s = ⊥) (φ : T ⟶ T') (x : T'.B) (hx : x ∈ T'.J) :
    ∃! ψ : pT T hT ⟶ T', jT T hT ≫ ψ = φ ∧ ψ.φ (xT (s := s) T) = x := by
  obtain ⟨F, ⟨hF1, hF2, hF3⟩, hFu⟩ := GlobalTheory.CompanionTheory.PDUniv.pdPoly_universal T.δ T'.δ φ.φ φ.dp x hx
  have hk : trI T s ≤ RingHom.ker F := by
    intro z hz
    have h1 : F z ∈ fil T'.δ (max s 1) := FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le _ _ F hF3 _ (Ideal.mem_map_of_mem F hz)
    have h2 : fil T'.δ (max s 1) ≤ fil T'.δ s := GlobalTheory.Cris.ExpBij.dpFil_anti T'.δ (le_max_left _ _)
    have h3 : F z ∈ T'.pdPow s := h2 h1
    rw [hT'] at h3
    exact h3
  let g : trB T s →+* T'.B := Ideal.Quotient.lift (trI T s) F fun a ha => hk ha
  have hgF : g.comp (Ideal.Quotient.mk (trI T s)) = F := by
    refine RingHom.ext fun z => ?_
    exact Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha
  have hg : g.comp (trF T s) = φ.φ := by
    rw [← RingHom.comp_assoc, hgF, hF1]
  have hdp : IsDPMorphism (trD T s) T'.δ g := (trD_spec T s).2 _ _ _ g (by rw [hgF]; exact hF3)
  have hle : trJ T s ≤ T'.J.comap g := Ideal.map_le_iff_le_comap.1 hdp.1
  refine ⟨descOf φ g hg hdp hle, ⟨hom_ext hg, (Ideal.Quotient.lift_mk (trI T s) F fun a ha => hk ha).trans hF2⟩, ?_⟩
  rintro ψ ⟨h1, h2⟩
  refine hom_ext ?_
  change ψ.φ = g
  have e := hFu (ψ.φ.comp (Ideal.Quotient.mk (trI T s))) ⟨?_, h2, ?_⟩
  · refine Ideal.Quotient.ringHom_ext ?_
    rw [e, hgF]
  · have := congrArg Thick.Hom.φ h1
    exact this
  · exact IsDPMorphism.comp _ ψ.dp (trD_spec T s).1

end Thickening

section Site

variable (l s : ℕ) (𝒱 : Set X.Opens)

abbrev Qc : ObjectProperty (Thick (nlFun γ 0 X q κ)) := St (TF l s) 𝒱

variable {l s 𝒱}

theorem pT_mem (T : (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱).FullSubcategory) : Qc l s 𝒱 (pT T.obj T.property.1) := by
  obtain ⟨V, hV, h⟩ := T.property.2
  exact ⟨pT_tf _ _, V, hV, inU_hom (jT T.obj T.property.1) h⟩

variable (l s 𝒱)

def polyQ : Poly (sP (Qc (γ := γ) (q := q) (κ := κ) l s 𝒱)) where
  P T := ⟨pT T.obj T.property.1, pT_mem T⟩
  j T := ObjectProperty.homMk (jT T.obj T.property.1)
  X T := xT (s := s) T.obj
  X_mem T := xT_mem T.obj
  univ {T T'} φ x hx := by
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := univ_tr T.obj T.property.1 T'.property.1.1 φ.hom x hx
    refine ⟨ObjectProperty.homMk ψ, ⟨ObjectProperty.hom_ext _ h1, h2⟩, ?_⟩
    rintro ψ' ⟨h3, h4⟩
    exact ObjectProperty.hom_ext _ (hu ψ'.hom ⟨congrArg (fun f => f.hom) h3, h4⟩)
  span T z := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (show trB T.obj s from z)
    obtain ⟨b, rfl⟩ := GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow T.obj.δ w
    exact ⟨b, (sum_eq T.obj b).symm⟩

theorem crit_fil (r : ℤ) (hr : r ≤ s) : (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (sFil _) r :=
  fun T b => fil_coeff T.obj b r hr

theorem crit_std (r : ℤ) (hr : r ≤ s) (c : R) :
    (polyQ (γ := γ) (q := q) (κ := κ) l s 𝒱).Crit (fun r => stdI _ (some r) c) r :=
  fun T b => std_coeff T.obj b r hr c

end Site

theorem polyTf : KH.PolyTf := by
  intro O R _ _ I γ X q κ l s 𝒱
  exact ⟨polyQ l s 𝒱, fun r hr => ⟨crit_fil l s 𝒱 r hr, crit_std l s 𝒱 r hr⟩⟩

end GlobalTheory.CompanionTheory.PolyTfCon
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTransferStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_transfer : KH.PolyTf := by
  first | exact @GlobalTheory.CompanionTheory.PolyTfCon.polyTf | exact GlobalTheory.CompanionTheory.PolyTfCon.polyTf | (intros; apply GlobalTheory.CompanionTheory.PolyTfCon.polyTf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InclRedM
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedPull

theorem incl_redM : ∀ {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : Option ℤ) (c : b.R) (j : ℕ) (z : HO Q j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r c)).pull j (redM Q r c j z) =
      redM Q' r c j ((incl h).o.pull j z) := by
  intro b L Q Q' h r c j z
  exact sq_toSq (incl h) _ _ (fun _ _ _ => trivial) (incl_std h r c) j z

end GlobalTheory.CompanionTheory.RedPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphism
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrisDP

theorem wn_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ),
    IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  intro l _ K r n
  let F₀ : WittVector l r.k →+* (base l).Acr0 :=
    (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))
  refine RL.pd_mor (Ideal.Quotient.mk _) ((base l).mkAcr n) (Ideal.span {(l : WittVector l r.k)}) (base l).PFil0
    (Wc.pd l r.k n) (B.DD true (base l) n) F₀ (Mid.wn r n) Ideal.Quotient.mk_surjective
    (pdI_l l (witt_unit l r.k)) (Wc.isPd l r.k n) ((base l).isPd_pdPFil n) ?_ ?_
  · intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  · intro a
    rw [Mid.wn_mk]
    exact (base l).cris_algebraMap n (WittVector.map r.s a)

end GlobalTheory.CompanionTheory.CrisDP
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittToAcrisIsDPMorphismStatement
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_to_acris_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), IsDPMorphism (Wc.pd l r.k n) (B.DD true (base l) n) (Mid.wn r n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | exact GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.CrisDP.wn_isDPMorphism <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCupListRepresentative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCupListRepresentative
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeRepCup

open GlobalTheory.CompanionTheory.CupRep

theorem cupList_cocycle {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) :
    ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → CH.d _ m (cupListC A ℓ) = 0
  | 0, _, _ => by
      funext s
      change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom 1 = (0 : A.obj _)
      rw [Fin.sum_univ_two, map_one, map_one]
      simp
  | m + 1, ℓ, h => by
      change CH.d _ (m + 1) ((CH.mulP A).cupC (by omega) (cupListC A fun i => ℓ (Fin.castSucc i)) (ℓ (Fin.last m))) = 0
      rw [CrystallineSemistableComparison.P.leibniz, cupList_cocycle A _ (fun k => h _), h]
      simp

theorem cupList_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m
  | 0, _, _ => mem_FC.2 fun s => by
      rw [Nat.cast_zero, hF.top 0 le_rfl]
      exact trivial
  | m + 1, ℓ, h => cup_mem hF (r := m) (r' := 1) _ (cupList_mem hF _ fun k => h _) (h _)

theorem exists_rep {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) :
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := by
  intro hF m ℓ hd hl
  have hm : cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m :=
    cupList_mem hF ℓ fun k => mem_FC.2 fun s => by simpa using hl k s
  refine GlobalTheory.CompanionTheory.ConeLocal.rep_exists (cupListC Φ.A ℓ) (mem_FC.1 hm) fun s => ?_
  rw [cupList_cocycle Φ.A ℓ hd]
  exact (Fil ((m : ℤ) + 1)).S _ |>.zero_mem

end GlobalTheory.CompanionTheory.ConeRepCup
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCupListRepresentativeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cup_list_representative : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := by
  first | exact @GlobalTheory.CompanionTheory.ConeRepCup.exists_rep | exact GlobalTheory.CompanionTheory.ConeRepCup.exists_rep | (intros; apply GlobalTheory.CompanionTheory.ConeRepCup.exists_rep <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWitt
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWitt
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisFlat

theorem flat_quotient_of_flat {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A)) (f : R ⧸ I →+* A ⧸ J)
    (hf : ∀ a, f (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap R A a)) :
    letI := f.toAlgebra; Module.Flat (R ⧸ I) (A ⧸ J) := by
  subst hJ
  letI := f.toAlgebra
  haveI : IsScalarTower R (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hf a).symm
  let e₀ : (R ⧸ I) ⊗[R] A ≃ₗ[R] A ⧸ I.map (algebraMap R A) :=
    (TensorProduct.comm R (R ⧸ I) A).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toLinearEquiv.restrictScalars R)
  let e : (R ⧸ I) ⊗[R] A ≃ₗ[R ⧸ I] A ⧸ I.map (algebraMap R A) :=
    e₀.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  exact Module.Flat.of_linearEquiv e.symm

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def wToAcr0 (r : Res l K) : WittVector l r.k →+* (base l).Acr0 :=
  (algebraMap (base l).W (base l).Acr0).comp ((base l).sW.comp (WittVector.map r.s))

theorem isTorsionFree_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.IsTorsionFree (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a x h
  by_cases ha : a = 0
  · exact Or.inl ha
  refine Or.inr ?_
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' a ha
  rw [Algebra.smul_def] at h
  have h1 : (wToAcr0 r a : Localization.Away (l : (base l).W)) * (x : Localization.Away (l : (base l).W)) = 0 :=
    congrArg Subtype.val h
  have hl : IsUnit (l : Localization.Away (l : (base l).W)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : (base l).W)) (l : (base l).W)
    rwa [map_natCast] at this
  have hu : IsUnit (wToAcr0 r a : Localization.Away (l : (base l).W)) := by
    have e2 : (wToAcr0 r a : Localization.Away (l : (base l).W)) =
        (l : Localization.Away (l : (base l).W)) ^ m * ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) b := by
      change ((base l).Acr0.val.toRingHom.comp (wToAcr0 r)) a = _
      rw [e, map_mul, map_pow, map_natCast]
    rw [e2]
    exact (hl.pow m).mul (b.isUnit.map _)
  exact Subtype.ext ((hu.mul_right_eq_zero).1 h1)

theorem flat_acris_zero (r : Res l K) :
    letI := (wToAcr0 r).toAlgebra; Module.Flat (WittVector l r.k) (base l).Acr0 := by
  letI := (wToAcr0 r).toAlgebra
  haveI := isTorsionFree_acris_zero r
  infer_instance

theorem flat_acr (r : Res l K) (n : ℕ) :
    letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  letI := (wToAcr0 r).toAlgebra
  haveI := flat_acris_zero r
  refine flat_quotient_of_flat (R := WittVector l r.k) (A := (base l).Acr0)
    (Ideal.span {(l : WittVector l r.k) ^ n}) (Ideal.span {(l : (base l).Acr0) ^ n}) ?_ (Mid.wn r n) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · intro a
    exact (Mid.wn_mk r n a).trans ((base l).cris_algebraMap n (WittVector.map r.s a))

end GlobalTheory.CompanionTheory.CrisFlat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWittStatement
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_acris_truncated_witt : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisFlat.flat_acr | exact GlobalTheory.CompanionTheory.CrisFlat.flat_acr | (intros; apply GlobalTheory.CompanionTheory.CrisFlat.flat_acr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotent
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.Dichotomy

section Core

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

end Core

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hc
  push Not at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hc x] at this
    exact this.symm)
  have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal

theorem exists_theta {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E), θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
  obtain ⟨y, hy⟩ := exists_moved h
  have hE2 : (2 : E) ≠ 0 := two_ne_zero
  have hσθ : σ (y - σ y) = -(y - σ y) := by
    rw [map_sub, sigma_sigma h]
    ring
  have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  generalize y - σ y = θ at hσθ hθ
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one] at hst
    have h1 := congrArg σ hst
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ, map_zero] at h1
    have hs : (2 : E) * algebraMap F E s = 0 := by
      linear_combination hst + h1
    have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
      linear_combination hst - h1
    have hs0 : s = 0 := by
      have := (mul_eq_zero.1 hs).resolve_left hE2
      exact (map_eq_zero _).1 this
    have ht0 : t = 0 := by
      have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
      exact (map_eq_zero _).1 this
    exact ⟨hs0, ht0⟩
  let B : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = θ := by simp [B]
  have hsum := B.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hB0, hB1] at hsum
  generalize B.repr (θ * θ) 0 = a at hsum
  generalize B.repr (θ * θ) 1 = b at hsum
  have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
    simpa only [Algebra.smul_def, mul_one] using hsum
  have hconj := congrArg σ hsum'
  simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ] at hconj
  have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
    linear_combination hsum' - hconj
  have hb0 : algebraMap F E b = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
  have hsq : θ * θ = algebraMap F E a := by
    rw [← hsum', hb0, zero_mul, add_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact hθ (mul_self_eq_zero.1 hsq)
  exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩

end CM

end GlobalTheory.CompanionTheory.SaGen.Dichotomy
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopRepresentativeAdd
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

open GlobalTheory.CompanionTheory.CupRep

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) :
    Ideal.Quotient.mk T.J (liftV T h g) = ev T h g :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T h g))

theorem liftV_sub_map_mem {V : X.Opens} {T T' : Thick (smFun X q)} (φ : T ⟶ T') (h : InU V T) (h' : InU V T')
    (g : Γ(X, V)) : liftV T' h' g - φ.φ (liftV T h g) ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [mk_liftV]
  have e : Ideal.Quotient.mk T'.J (φ.φ (liftV T h g)) =
      Ideal.quotientMap T'.J φ.φ φ.hle (Ideal.Quotient.mk T.J (liftV T h g)) := (Ideal.quotientMap_mk).symm
  rw [e, mk_liftV]
  exact GlobalTheory.CompanionTheory.GrForm.ev_nat φ h h' g

theorem liftV_add_mem {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (x y : Γ(X, V)) :
    liftV T h x + liftV T h y - liftV T h (x + y) ∈ T.J := by
  refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [map_sub, map_add (f := _), mk_liftV, mk_liftV, mk_liftV, map_add (f := _), sub_self]

variable (s : ℕ) (V : X.Opens)

theorem addC_mem (g : Γ(X, V)) :
    addC (KS q s {V}) (fun T => liftV T.obj (ks_in q s V T.obj T.property) g) ∈
      FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1 := by
  refine mem_FC.2 fun u => ?_
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  rw [Nat.cast_one, hF.one]
  exact liftV_sub_map_mem (u.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom _ _ g

theorem cupList_mem {d : ℕ} (l : Fin d → CH.Cn (CH.modF (sP (KS q s {V})).A) 1)
    (hl : ∀ k, l k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1) :
    cupListC (sP (KS q s {V})).A l ∈ FC (sFil (KS q s {V}) ((d : ℕ) : ℤ)) d := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  induction d with
  | zero =>
    refine mem_FC.2 fun u => ?_
    rw [hF.top _ (by simp)]
    trivial
  | succ n ih =>
    exact cup_mem hF (by omega) (ih _ fun i => hl _) (hl (Fin.last n))

theorem xdtC_val {d : ℕ} (t : Fin d → Γ(X, V)) (x : Γ(X, V)) (u : ComposableArrows (KS q s {V}).FullSubcategory d) :
    vl (xdtC (q := q) s V t x) u =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) *
      vl (cupListC (sP (KS q s {V})).A fun k =>
        addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k)) u :=
  congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last d)) =>
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) * b)
    (CrystallineSemistableComparison.Auxff.term_id _ u _ _ _ (fun t => by simp [CH.back]))

end GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

namespace GlobalTheory.CompanionTheory.ConeLocal

open GlobalTheory.CompanionTheory.CupRep XdtAdd

theorem rep_xdtC_add {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (s : ℕ) (V : X.Opens)
    {d : ℕ} (t : Fin d → Γ(X, V)) (x y : Γ(X, V)) (a b : HQ (KS q s {V}) d ((d : ℤ) + 1) d)
    (ha : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t x) a)
    (hb : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t y) b) :
    Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t (x + y)) (a + b) := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  refine rep_congr (rep_add ha hb) fun u => ?_
  have hc := mem_FC.1 (cupList_mem s V (fun k => addC (KS q s {V}) fun T =>
    liftV T.obj (ks_in q s V T.obj T.property) (t k)) fun k => addC_mem s V (t k)) u
  let T0 := u.obj (CH.front (Nat.zero_add d) (Fin.last 0))
  let ψ := u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0))))
  have h1 : ((sP (KS q s {V})).A.map ψ).hom
      (liftV T0.obj (ks_in q s V _ T0.property) x + liftV T0.obj (ks_in q s V _ T0.property) y -
        liftV T0.obj (ks_in q s V _ T0.property) (x + y)) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact (sP (KS q s {V})).J.map_mem ψ (liftV_add_mem T0.obj _ x y)
  have h2 := hF.mul 1 d _ h1 hc
  have e : ((1 + d : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
  rw [e] at h2
  change vl (xdtC (q := q) s V t x) u + vl (xdtC (q := q) s V t y) u - vl (xdtC (q := q) s V t (x + y)) u ∈ _
  rw [xdtC_val, xdtC_val, xdtC_val]
  convert h2 using 1
  rw [map_sub, map_add (f := _)]
  ring

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicative
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
namespace GlobalTheory.CompanionTheory.TruncLog

variable {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J)

theorem mul_dpow_eq_succ {x : A} (hx : x ∈ J) (a : ℕ) :
    x * δ.dpow a x = ((a : A) + 1) * δ.dpow (a + 1) x := by
  have h := δ.mul_dpow (m := 1) (n := a) hx
  rw [δ.dpow_one hx] at h
  rw [h, Nat.choose_one_right, add_comm 1 a]
  push_cast
  ring

theorem factorial_mul_dpow_eq_zero {N : ℕ} {x : A}
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) {a k : ℕ} (ha : N < a)
    (hk : a ≤ k + 1) : (k.factorial : A) * δ.dpow a x = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial (show c ≤ k by omega)
  rw [hd]
  push_cast
  rw [mul_comm (c.factorial : A), mul_assoc, hN c (by omega), mul_zero]

theorem one_add_mul_sum_succ {x : A} (hx : x ∈ J) (m n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + (m + 1)).factorial : A) * δ.dpow a x =
      ((m : A) + 1) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x
      + (-1) ^ n * ((n + (m + 1)).factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    have e : (((m + 1).factorial : ℕ) : A) = ((m : A) + 1) * (m.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, e, Nat.cast_zero]
    ring
  | succ n ih =>
    have e1 : ((n + 1 + (m + 1)).factorial : A)
        = ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    have e2 : ((n + 1 + m).factorial : A) = ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + m = n + (m + 1) by omega]
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ _ (n + 1), e1, e2]
    push_cast at hxp ⊢
    linear_combination
      (-1 : A) ^ (n + 1) * ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) * hxp

theorem one_add_mul_sum_zero {x : A} (hx : x ∈ J) (n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1), (-1 : A) ^ a * (a.factorial : A) * δ.dpow a x =
      1 + (-1) ^ n * (n.factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero]
  | succ n ih =>
    have e1 : ((n + 1).factorial : A) = ((n : A) + 1) * (n.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, e1]
    push_cast at hxp ⊢
    linear_combination (-1 : A) ^ (n + 1) * ((n : A) + 1) * (n.factorial : A) * hxp

theorem one_add_pow_mul_sum {N : ℕ} {x : A} (hx : x ∈ J)
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) (m : ℕ) :
    (1 + x) ^ (m + 1) * ∑ a ∈ Finset.range (N + 1),
      (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x = (m.factorial : A) := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, add_zero, Nat.factorial_zero, Nat.cast_one]
    rw [one_add_mul_sum_zero δ hx N]
    have := hN N le_rfl
    linear_combination ((-1 : A) ^ N * ((N : A) + 1)) * this
  | succ m ih =>
    have z := factorial_mul_dpow_eq_zero δ hN (a := N + 1) (k := N + (m + 1)) (by omega) (by omega)
    rw [pow_succ, mul_assoc, one_add_mul_sum_succ δ hx m N, Nat.factorial_succ]
    push_cast
    linear_combination ((m : A) + 1) * ih
      + (1 + x) ^ (m + 1) * (-1 : A) ^ N * ((N : A) + 1) * z

theorem sum_antidiagonal_eq_sum_box (g : ℕ → ℕ → A) {N M : ℕ} (hM : 2 * N ≤ M)
    (hg : ∀ a b, N < a ∨ N < b → g a b = 0) :
    ∑ k ∈ Finset.range (M + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, g p.1 p.2 =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b := by
  rw [← Finset.sum_product' (f := g),
    ← Finset.sum_fiberwise_of_maps_to
      (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1)) (t := Finset.range (M + 1))
      (g := fun p => p.1 + p.2)
      (by intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  · intro p hp hp'
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hp'
    apply hg
    by_contra hc
    exact hp' (by omega) hp

theorem dlog_mul {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ)
    (h : ∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) (v w : A)
    (hv : v - 1 ∈ J) (hw : w - 1 ∈ J) :
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  obtain ⟨x, rfl⟩ : ∃ x, v = 1 + x := ⟨v - 1, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, w = 1 + y := ⟨w - 1, by ring⟩
  have hx : x ∈ J := by simpa using hv
  have hy : y ∈ J := by simpa using hw
  have hvy : (1 + x) * y ∈ J := J.mul_mem_left _ hy
  have hz : x + (1 + x) * y ∈ J := J.add_mem hx hvy
  have dl : ∀ t : A, B.dlog δ N (1 + t) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) t := by
    intro t; simp [B.dlog]
  have dz : B.dlog δ N ((1 + x) * (1 + y)) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    have : (1 + x) * (1 + y) = 1 + (x + (1 + x) * y) := by ring
    rw [this, dl]
  let g : ℕ → ℕ → A := fun a b => (-1 : A) ^ (a + b + 1) * ((a + b - 1).factorial : A) *
    δ.dpow a x * ((1 + x) ^ b * δ.dpow b y)
  have hg : ∀ a b, N < a ∨ N < b → g a b = 0 := by
    intro a b hab
    rcases hab with hab | hab
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk x hx) (a := a) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      rw [mul_assoc ((-1 : A) ^ (a + b + 1)), this]
      ring
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk y hy) (a := b) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      linear_combination
        ((-1 : A) ^ (a + b + 1) * δ.dpow a x * (1 + x) ^ b) * this
  have s1 : B.dlog δ N ((1 + x) * (1 + y)) = ∑ k ∈ Finset.range (2 * N),
      (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    rw [dz]
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [mul_assoc, h k hk _ hz, mul_zero]
  have s2 : ∀ k, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), g p.1 p.2 := by
    intro k
    rw [δ.dpow_add hx hvy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = k + 1 := by simpa using hp
    simp only [g]
    rw [hp', δ.dpow_mul hy, show k + 1 - 1 = k by omega]
    ring
  have s3 := sum_antidiagonal_eq_sum_box g (N := N) (M := 2 * N) le_rfl hg
  rw [Finset.sum_range_succ'] at s3
  have s4 : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b =
      g 0 0 + (B.dlog δ N (1 + x) + B.dlog δ N (1 + y)) := by
    rw [Finset.sum_comm, Finset.sum_range_succ', Finset.sum_range_succ' (fun a => g a 0), dl, dl]
    have t1 : ∀ k, g (k + 1) 0 = (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) x := by
      intro k
      simp only [g, add_zero, pow_zero, δ.dpow_zero hy, show k + 1 - 1 = k by omega]
      ring
    have t2 : ∀ b, ∑ a ∈ Finset.range (N + 1), g a (b + 1) =
        (-1 : A) ^ b * (b.factorial : A) * δ.dpow (b + 1) y := by
      intro b
      rw [← one_add_pow_mul_sum δ hx (fun k hk => h k hk x hx) b]
      simp only [g]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show a + (b + 1) - 1 = a + b by omega]
      ring
    simp only [t1, t2]
    ring
  have s5 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, g p.1 p.2 = g 0 0 := by simp
  rw [s5, s4] at s3
  simp only [← s2] at s3
  rw [s1]
  linear_combination s3

end GlobalTheory.CompanionTheory.TruncLog
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicativeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_log_multiplicative : ∀ {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ),
    (∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) → ∀ v w : A, v - 1 ∈ J → w - 1 ∈ J →
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  first | exact @GlobalTheory.CompanionTheory.TruncLog.dlog_mul | exact GlobalTheory.CompanionTheory.TruncLog.dlog_mul | (intros; apply GlobalTheory.CompanionTheory.TruncLog.dlog_mul <;> assumption)
end
end
