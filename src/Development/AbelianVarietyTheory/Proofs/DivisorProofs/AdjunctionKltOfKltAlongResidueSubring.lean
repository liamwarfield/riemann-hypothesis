module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisResidueFieldUniformiserCons
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitMulZpowRegularLocalModelDimTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleOfOrdOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePlaceEvalNeZeroInvMemOfIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePlaceEvalNeZeroInvMemOfIsUnit
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem eval₂_residue_ne_zero_and_inv_mem_of_isUnit :
    ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q)
  (S : Place cL) (ψ : S.ring →+* K) (F : Place cK), S.Contains Q → (∀ a, ψ (S.const a) = cK a) →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  ∀ (m : ℕ) (z : Fin m → Q) (zs : Fin m → S.ring), (∀ i, (zs i : L) = z i) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P ≠ 0 ∧
    (MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P)⁻¹ ∈ F.ring := by
  intro L K _ _ cL cK Q hQ S ψ F hSQ hc hF m z zs hz hu P hP
  let j : Q →+* S.ring := Q.subtype.codRestrict S.ring fun q => hSQ q q.2
  have h1 : (ψ.comp j).comp (cL.codRestrict Q hQ.const_mem) = cK := RingHom.ext fun a => hc a
  have h2 : (fun i => (ψ.comp j) (z i)) = fun i => ψ (zs i) :=
    funext fun i => congrArg ψ (Subtype.ext (hz i).symm)
  have h3 : (ψ.comp j) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P) =
      MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P := by
    rw [MvPolynomial.hom_eval₂, h1, h2]
  obtain ⟨q, hq⟩ := (hu P hP).exists_right_inv
  have h4 : MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P * (ψ.comp j) q = 1 := by
    rw [← h3, ← map_mul, hq, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h4, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right h4]
  exact (hF _).2 ⟨j q, q.2, rfl⟩

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePlaceEvalNeZeroInvMemOfIsUnitStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residuePlace_eval_ne_zero_inv_mem_of_isUnit : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q)
  (S : Place cL) (ψ : S.ring →+* K) (F : Place cK), S.Contains Q → (∀ a, ψ (S.const a) = cK a) →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  ∀ (m : ℕ) (z : Fin m → Q) (zs : Fin m → S.ring), (∀ i, (zs i : L) = z i) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P ≠ 0 ∧
    (MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P)⁻¹ ∈ F.ring := by
  first | exact @GlobalTheory.FieldPair.eval₂_residue_ne_zero_and_inv_mem_of_isUnit | exact GlobalTheory.FieldPair.eval₂_residue_ne_zero_and_inv_mem_of_isUnit | (intros; apply GlobalTheory.FieldPair.eval₂_residue_ne_zero_and_inv_mem_of_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdQMapDomainResiduePlaceTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdQMapDomainResiduePlaceTransport
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTransport

variable {k M : Type} [Field k] [Field M] {c : k →+* M}

theorem ord_prod_zpow {ι : Type} (P : Place c) (s : Finset ι) (f : ι → M) (n : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : P.ord (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i * P.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      P.ord_mul (zpow_ne_zero _ (hf a (Finset.mem_insert_self a s)))
        (Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi))),
      P.ord_zpow, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ordQ_mapDomain {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) :
    P.ordQ (Finsupp.mapDomain f φ) = ∑ g ∈ φ.support, φ g * P.ord (f g) := by
  rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

theorem ord_prod_eq_mul_ordQ {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) (N : ℕ)
    (m : ι → ℤ) (hm : ∀ g ∈ φ.support, (m g : ℚ) = N * φ g) (hf : ∀ g ∈ φ.support, f g ≠ 0) :
    (P.ord (∏ g ∈ φ.support, f g ^ m g) : ℚ) = N * P.ordQ (Finsupp.mapDomain f φ) := by
  rw [ord_prod_zpow P _ f m hf, ordQ_mapDomain, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [hm g hg]
  ring

theorem exists_common_den {ι : Type} (s : Finset ι) (φ : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ s, ∃ m : ℤ, (m : ℚ) = N * φ g := by
  classical
  refine ⟨∏ g ∈ s, (φ g).den, Finset.prod_pos fun g _ => (φ g).den_pos, fun g hg =>
    ⟨(φ g).num * ∏ x ∈ s.erase g, ((φ x).den : ℤ), ?_⟩⟩
  rw [← Finset.mul_prod_erase s _ hg]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

end GlobalTheory.FieldPair.ResidueTransport

namespace GlobalTheory.FieldPair


open ResidueTransport in
theorem ordQ_mapDomain_residue_eq {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (Q : Subring L) (u : Q) (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK)
    (hSQ : S.Contains Q) (hSu : S.ord (u : L) = 0) (hu0 : (u : L) ≠ 0)
    (hψ : Function.Surjective ψ)
    (hF : ∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a)
    (hFu : ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1)
    (hG : ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
      ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G)
    (φ : S.ring →₀ ℚ) (hsupp : ∀ g ∈ φ.support, ψ g ≠ 0)
    (hPφ : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) :
    F.ordQ (Finsupp.mapDomain ψ φ) =
      E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by

  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal S.ring :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
  have hunit : ∀ g ∈ φ.support, IsUnit g := fun g hg =>
    IsLocalRing.notMem_maximalIdeal.1 (by rw [← hker, RingHom.mem_ker]; exact hsupp g hg)
  choose! w hw using hunit
  obtain ⟨N, hN, hm⟩ := exists_common_den φ.support φ
  choose! m hm using hm
  have hg0 : ∀ g ∈ φ.support, ((g : S.ring) : L) ≠ 0 := fun g hg h =>
    hsupp g hg (by rw [show g = 0 from Subtype.ext h, map_zero])
  set G : L := ∏ g ∈ φ.support, ((g : S.ring) : L) ^ m g with hGdef
  set H : K := ∏ g ∈ φ.support, ψ g ^ m g with hHdef
  have hGord := fun P : Place cL => ord_prod_eq_mul_ordQ P φ (fun g : S.ring => (g : L)) N m hm hg0
  have hHord := ord_prod_eq_mul_ordQ F φ ψ N m hm hsupp
  have hG0 : G ≠ 0 := Finset.prod_ne_zero_iff.2 fun g hg => zpow_ne_zero _ (hg0 g hg)

  have hPG : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0 := by
    intro P hP hPE
    by_cases hPS : P.ring = S.ring
    · obtain rfl : P = S := Place.ext hPS
      rw [hGdef, ord_prod_zpow P _ _ m hg0]
      refine Finset.sum_eq_zero fun g hg => ?_
      rw [← hw g hg, P.ord_eq_zero (w g).isUnit, mul_zero]
    · have h := hGord P
      rw [hPφ P hP hPS hPE, mul_zero] at h
      exact_mod_cast h
  obtain ⟨q, hqU, hGq⟩ := hG G hG0 hPG
  set b := E.ord G with hb

  let uS : S.ring := ⟨u, hSQ _ u.2⟩
  have huS : IsUnit uS := by
    have h1 : (u : L) ∈ S.ring := hSQ _ u.2
    have h2 : (u : L)⁻¹ ∈ S.ring := by
      rw [← S.ord_nonneg_iff (inv_ne_zero hu0), S.ord_inv, hSu]; simp
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hu0))
  obtain ⟨r, hr⟩ := hqU.exists_right_inv
  let qS : S.ring := ⟨q, hSQ _ q.2⟩
  let rS : S.ring := ⟨r, hSQ _ r.2⟩
  have hqr : qS * rS = 1 := Subtype.ext (by change ((q * r : Q) : L) = 1; rw [hr]; rfl)
  let qU : S.ringˣ := (IsUnit.of_mul_eq_one rS hqr).unit
  let uU : S.ringˣ := huS.unit
  let W : S.ringˣ := ∏ g ∈ φ.support, w g ^ m g
  let e : S.ringˣ →* Lˣ := Units.map (S.ring.subtype : S.ring →* L)
  let f : S.ringˣ →* Kˣ := Units.map (ψ : S.ring →* K)
  have he : ∀ x, ((e x : Lˣ) : L) = ((x : S.ring) : L) := fun _ => rfl
  have hf : ∀ x, ((f x : Kˣ) : K) = ψ x := fun _ => rfl
  have heW : ((e W : Lˣ) : L) = G := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, he]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hfW : ((f W : Kˣ) : K) = H := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hf]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hWeq : W = qU * uU ^ b := by
    have hinj : Function.Injective e := fun x y h =>
      Units.ext (Subtype.ext (by rw [← he, ← he, h]))
    apply hinj
    apply Units.ext
    rw [heW, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, he, he,
      IsUnit.unit_spec, IsUnit.unit_spec]
    exact hGq
  have hH : H = ψ qS * ψ uS ^ b := by
    rw [← hfW, hWeq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hf, hf,
      IsUnit.unit_spec, IsUnit.unit_spec]

  have hq0 : ψ qS * ψ rS = 1 := by rw [← map_mul, hqr, map_one]
  have hψq0 : ψ qS ≠ 0 := left_ne_zero_of_mul_eq_one hq0
  have hψu0 : ψ uS ≠ 0 := (huS.map ψ).ne_zero
  have hFq : F.ord (ψ qS) = 0 := by
    have h1 : 0 ≤ F.ord (ψ qS) := (F.ord_nonneg_iff hψq0).2 ((hF _).2 ⟨qS, q.2, rfl⟩)
    have hinv : (ψ qS)⁻¹ = ψ rS := inv_eq_of_mul_eq_one_right hq0
    have h2 : 0 ≤ F.ord (ψ qS)⁻¹ := (F.ord_nonneg_iff (inv_ne_zero hψq0)).2
      (by rw [hinv]; exact (hF _).2 ⟨rS, r.2, rfl⟩)
    rw [F.ord_inv] at h2
    omega
  have hFH : F.ord H = b := by
    rw [hH, F.ord_mul hψq0 (zpow_ne_zero _ hψu0), F.ord_zpow, hFq, hFu uS rfl]
    ring
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hEG := hGord E
  rw [← hb, ← hFH, hHord] at hEG
  exact mul_left_cancel₀ hNq hEG

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdQMapDomainResiduePlaceTransportStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordQ_mapDomain_residuePlace_transport : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK),
  S.Contains Q → S.ord (u : L) = 0 → (u : L) ≠ 0 → Function.Surjective ψ →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  (∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1) →
  (∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
    ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G) →
  ∀ φ : S.ring →₀ ℚ, (∀ g ∈ φ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) →
  F.ordQ (Finsupp.mapDomain ψ φ) = E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by
  first | exact @GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq | exact GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq | (intros; apply GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueTopFormAlongPrimeDivisorAdjunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueTopFormAlongPrimeDivisorAdjunction
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Residue

open KaehlerDifferential IsLocalRing Module

theorem exists_basis_D_cons (k V : Type) [Field k] [CharZero k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra k V] [Algebra.EssFiniteType k V] (n : ℕ) {t : V}
    (w : Fin n → V) (ht : Irreducible t) (hb₀ : Nonempty (Module.Basis (Fin (n + 1)) V Ω[V⁄k]))
    (hw : ∀ P : MvPolynomial (Fin n) k, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (algebraMap k V) w P)) :
    ∃ b : Module.Basis (Fin (n + 1)) V Ω[V⁄k], ∀ i, b i = D k V ((Fin.cons t w : Fin (n + 1) → V) i) := by
  obtain ⟨b₀⟩ := hb₀
  haveI : Algebra.FormallySmooth k V := formallySmooth_of_isRegularLocalRing_of_perfectField k V
  let κ := ResidueField V
  let wb : Fin n → κ := fun i => algebraMap V κ (w i)
  have hai : AlgebraicIndependent k wb := by
    rw [algebraicIndependent_iff]
    intro P hP
    by_contra hne
    have hu := hw P hne
    have e : MvPolynomial.aeval wb P = algebraMap V κ (MvPolynomial.eval₂ (algebraMap k V) w P) := by
      rw [show wb = algebraMap V κ ∘ w from rfl, MvPolynomial.aeval_algebraMap_apply]
      rfl
    rw [e] at hP
    exact (residue_ne_zero_iff_isUnit _).mpr hu hP
  have hdli : LinearIndependent κ fun i => D k κ (wb i) := by
    have hs : AlgebraicIndepOn k id (Set.range wb) := by
      exact (algebraicIndependent_subtype_range hai.injective).mpr hai
    obtain ⟨s, hsub, hs⟩ := exists_isTranscendenceBasis_superset hs
    haveI := hs.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → κ))) κ :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
    let ι : Fin n → s := fun i => ⟨wb i, hsub (Set.mem_range_self i)⟩
    have hι : Function.Injective ι := fun i j h => hai.injective (congrArg Subtype.val h)
    have := b.linearIndependent.comp ι hι
    convert this using 1
    funext i
    simp [ι, hb]
  have ht₀ : algebraMap V κ t = 0 := (residue_eq_zero_iff t).mpr (by
    rw [ht.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self t)
  let z : Fin (n + 1) → V := Fin.cons t w
  have hli : LinearIndependent κ (TensorProduct.mk V κ Ω[V⁄k] 1 ∘ fun i => D k V (z i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Function.comp_apply, TensorProduct.mk_apply, z, Fin.cons_zero, Fin.cons_succ] at hg
    have hφ := congrArg (mapBaseChange k V κ) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, map_zero, mapBaseChange_tmul, one_smul, map_D, ht₀,
      Derivation.map_zero, smul_zero, zero_add] at hφ
    have hs : ∀ i : Fin n, g i.succ = 0 :=
      Fintype.linearIndependent_iff.mp hdli (fun i => g i.succ) hφ
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at hg
    have h0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h (one_tmul_D_ne_zero k ht)
    intro i
    exact Fin.cases h0 hs i
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis (b₀.baseChange κ), Fintype.card_fin])
  haveI : Module.Free V Ω[V⁄k] := Module.Free.of_basis b₀
  haveI : Module.Finite V Ω[V⁄k] := Module.Finite.of_basis b₀
  haveI : Module.FinitePresentation V Ω[V⁄k] := Module.finitePresentation_of_finite V _
  exact Module.exists_basis_of_basis_baseChange (R := V) (fun i => D k V (z i)) hli hsp
    (Module.Flat.rTensor_preserves_injective_linearMap (maximalIdeal V).subtype
      Subtype.val_injective)

theorem residue_dForm : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → ∀ (t f : S.ring) (v w : Fin n → S.ring) (H : L),
  Irreducible t → Irreducible f → TrBasis cK (fun i => ψ (v i)) →
  TrBasis cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
    H • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  ∃ h : S.ring, (h : L) * f = H * t ∧ dForm cK (fun i => ψ (w i)) = ψ h • dForm cK (fun i => ψ (v i)) := by
  intro L K _ _ cL cK n S ψ hψ hc t f v w H ht hf hvK hvL hH
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  letI : Algebra S.ring K := ψ.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : IsScalarTower ℂ S.ring K := IsScalarTower.of_algebraMap_eq' hcomp.symm
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hψt : ψ t = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact ht.not_isUnit
  have hb₀ : Nonempty (Module.Basis (Fin (n + 1)) S.ring Ω[S.ring⁄ℂ]) := by
    obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ ht
    have h1 := trdeg_eq_of_basis_kaehler ℂ L b
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hvL
    rw [h1, Cardinal.mk_fin] at h2
    have h3 : n + 1 = m + 1 := by exact_mod_cast h2
    obtain rfl : n = m := by omega
    exact ⟨b⟩
  have hvu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P) := by
    intro P hP
    by_contra hu
    have hm : MvPolynomial.eval₂ (algebraMap ℂ S.ring) v P ∈ RingHom.ker ψ := by
      rw [hker]
      exact hu
    rw [RingHom.mem_ker, MvPolynomial.hom_eval₂, hcomp] at hm
    have hind : AlgebraicIndependent ℂ (fun i => ψ (v i)) := hvK.1
    exact hP ((algebraicIndependent_iff.1 hind) P hm)
  obtain ⟨b, hb⟩ := exists_basis_D_cons ℂ S.ring n v ht hb₀ hvu

  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ ht hf
  set z : Fin (n + 1) → S.ring := Fin.cons t v with hz
  have hω : IsFreeGen S.ring (dForm S.const z) := isFreeGen_dForm z b hb
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) S.ring :=
    Matrix.of fun i j => b.repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i)) j
  have hM : dForm S.const (Fin.cons f w : Fin (n + 1) → S.ring) = M.det • dForm S.const z := by
    refine dForm_eq_det_smul _ _ M fun i => ?_
    change D ℂ S.ring _ = ∑ j, M i j • D ℂ S.ring (z j)
    conv_lhs => rw [← b.sum_repr (D ℂ S.ring ((Fin.cons f w : Fin (n + 1) → S.ring) i))]
    simp only [hb, M, Matrix.of_apply, hz]
  have hcons : ∀ (a : S.ring) (g : Fin n → S.ring),
      (fun i => S.ring.subtype ((Fin.cons a g : Fin (n + 1) → S.ring) i)) =
        (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have htoRat : ∀ (a : S.ring) (g : Fin n → S.ring),
      S.toRat (n + 1) (dForm S.const (Fin.cons a g : Fin (n + 1) → S.ring)) =
        dForm cL (Fin.cons (a : L) (fun i => (g i : L)) : Fin (n + 1) → L) := by
    intro a g
    exact (formMap_dForm (D := n + 1) S.ring.subtype rfl _).trans (congrArg _ (hcons a g))
  have hML : dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
      (M.det : L) • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) := by
    have := congrArg (S.toRat (n + 1)) hM
    rw [map_smulₛₗ, hz, htoRat, htoRat] at this
    exact this
  have hHM : H = (M.det : L) := by
    have hne := S.toRat_ne_zero hω
    rw [hz, htoRat] at hne
    exact smul_left_injective L hne (hH.symm.trans hML)

  have hmain : M.det * ↑u⁻¹ * f = M.det * t := by
    rw [← hu, mul_comm t, ← mul_assoc, mul_assoc M.det, Units.inv_mul, mul_one]
  refine ⟨M.det * ↑u⁻¹, ?_, ?_⟩
  · rw [hHM]
    exact_mod_cast congrArg Subtype.val hmain
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => ψ (M i.succ j.succ)
  have hN : dForm cK (fun i => ψ (w i)) = N.det • dForm cK (fun i => ψ (v i)) := by
    refine dForm_eq_det_smul _ _ N fun i => ?_
    change D ℂ K (ψ (w i)) = ∑ j, N i j • D ℂ K (ψ (v j))
    have := congrArg (KaehlerDifferential.map ℂ ℂ S.ring K) (b.sum_repr (D ℂ S.ring (w i)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, KaehlerDifferential.map_D, Fin.sum_univ_succ, RingHom.algebraMap_toAlgebra] at this
    rw [← this]
    simp only [map_smul, hb, KaehlerDifferential.map_D, hz, Fin.cons_zero, Fin.cons_succ,
      RingHom.algebraMap_toAlgebra, hψt, map_zero, smul_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K]
    simp [N, M, RingHom.algebraMap_toAlgebra]
  have hDt : D ℂ S.ring t = b 0 := by rw [hb]; rfl
  have hrow : ∀ j, ψ (M 0 j) = ψ (u * Finsupp.single (0 : Fin (n + 1)) (1 : S.ring) j) := by
    intro j
    simp only [M, Matrix.of_apply, Fin.cons_zero]
    rw [← hu, Derivation.leibniz, hDt, map_add (f := _), map_smul, map_smul, b.repr_self]
    rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, map_add (f := _),
      map_mul, hψt, zero_mul, zero_add]
  have hsub : (ψ.mapMatrix M).submatrix Fin.succ Fin.succ = N := Matrix.ext fun _ _ => rfl
  have h0 : ∀ j : Fin n, ψ.mapMatrix M 0 j.succ = 0 := fun j => by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp [Finsupp.single_apply, (Fin.succ_ne_zero j).symm]
  have h00 : ψ.mapMatrix M 0 0 = ψ u := by
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow]
    simp
  have hdet : ψ M.det = ψ u * N.det := by
    rw [RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove_zero, hsub]
    simp only [h0, h00, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
      one_mul]
  rw [hN, map_mul, hdet, mul_comm (ψ u), mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

end GlobalTheory.Residue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueTopFormAlongPrimeDivisorAdjunctionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_topForm_along_primeDivisor_adjunction : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → ∀ (t f : S.ring) (v w : Fin n → S.ring) (H : L),
  Irreducible t → Irreducible f → TrBasis cK (fun i => ψ (v i)) →
  TrBasis cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) =
    H • dForm cL (Fin.cons (t : L) (fun i => (v i : L)) : Fin (n + 1) → L) →
  ∃ h : S.ring, (h : L) * f = H * t ∧ dForm cK (fun i => ψ (w i)) = ψ h • dForm cK (fun i => ψ (v i)) := by
  first | exact @GlobalTheory.Residue.residue_dForm | exact GlobalTheory.Residue.residue_dForm | (intros; apply GlobalTheory.Residue.residue_dForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdFreeTopFormEqZeroOfIsPrimeOf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdFreeTopFormEqZeroOfIsPrimeOf
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (fun i => (x i : L))) = 0 := by
  intro L _ cL Q hQ D x hx P hP
  let α : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  let ρ : Q →+* P.ring := RingHom.codRestrict Q.subtype P.ring (fun q => hP.1 q q.2)
  have hρ : ρ.comp α = P.const := RingHom.ext fun _ => Subtype.ext rfl
  have e : dForm cL (fun i => (x i : L)) = P.toRat D (dForm P.const fun i => ρ (x i)) := by
    have h := TopForm.formMap_dForm (D := D) (α := P.const) (β := cL) P.ring.subtype rfl (fun i => ρ (x i))
    refine Eq.trans ?_ h.symm
    congr 1
  let S : Submonoid Q :=
    { carrier := {b | (b : L) ≠ 0 ∧ P.ord b = 0}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_⟩
        · change (a : L) * b ≠ 0
          exact mul_ne_zero ha.1 hb.1
        · change P.ord ((a : L) * b) = 0
          rw [P.ord_mul ha.1 hb.1, ha.2, hb.2, add_zero]
      one_mem' := ⟨one_ne_zero, P.ord_one⟩ }
  letI := α.toAlgebra
  letI := P.const.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower ℂ Q P.ring := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization S P.ring :=
    { map_units := fun ⟨b, hb⟩ => by
        have hinv : (b : L)⁻¹ ∈ P.ring := by
          rw [← P.ord_nonneg_iff (inv_ne_zero hb.1), P.ord_inv, hb.2, neg_zero]
        exact IsUnit.of_mul_eq_one (⟨(b : L)⁻¹, hinv⟩ : P.ring)
          (Subtype.ext (mul_inv_cancel₀ hb.1))
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb0, hbo⟩), Subtype.ext e⟩
      exists_of_eq := fun {a b} e => by
        have h : (a : L) = b := congrArg (fun z : P.ring => (z : L)) e
        exact ⟨1, by rw [Subtype.ext h]⟩ }
  haveI : Algebra.FormallyEtale Q P.ring := .of_isLocalization S
  have hG : IsFreeGen P.ring (TopForm.formMap D ρ hρ (dForm α x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q P.ring) D)
  rw [TopForm.formMap_dForm] at hG
  rw [e]
  exact P.formOrd_toRat hG

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdFreeTopFormEqZeroOfIsPrimeOfStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_freeTopForm_eq_zero_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (fun i => (x i : L))) = 0 := by
  first | exact @GlobalTheory.formOrd_dForm_of_isPrimeOf | exact GlobalTheory.formOrd_dForm_of_isPrimeOf | (intros; apply GlobalTheory.formOrd_dForm_of_isPrimeOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResiduePlaceOfTwoDimLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResiduePlaceOfTwoDimLocalModel
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem residuePlace_of_locModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  intro L K _ _ cL cK Q hQ t u hm hdim S ψ hS ht hψ hc
  letI := hQ.isLocalRing
  have hSQ : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let φ₀ : Q →+* S.ring := Q.subtype.codRestrict S.ring hSQ
  let φ : Q →+* K := ψ.comp φ₀
  have hker : ∀ s : S.ring, ψ s = 0 ↔ ¬ IsUnit s := by
    intro s
    have hmax := RingHom.ker_isMaximal_of_surjective ψ hψ
    have h := IsLocalRing.eq_maximalIdeal hmax
    rw [← RingHom.mem_ker, h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hunit : ∀ s : S.ring, (s : L) ≠ 0 → S.ord s = 0 → IsUnit s := by
    intro s hs h0
    have hinv : (s : L)⁻¹ ∈ S.ring :=
      (S.ord_nonneg_iff (inv_ne_zero hs)).1 (by rw [S.ord_inv, h0, neg_zero])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hs))
  have hφt : φ t = 0 := by
    show ψ (φ₀ t) = 0
    rw [hker]
    intro hu
    have h := S.ord_eq_zero hu
    change S.ord (t : L) = 0 at h
    rw [ht] at h
    exact one_ne_zero h
  have hφu : φ u ≠ 0 := by
    intro hu0
    have hsp : Ideal.span {t, u} ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact hφt
      · exact hu0
    have hle : ∀ f ∈ S.ring, f ∈ Q := by
      intro f hf
      obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f hf
      have hbu : IsUnit (⟨b, hb⟩ : Q) := by
        by_contra hnu
        have h1 : φ ⟨b, hb⟩ = 0 := hsp (hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu)
        exact (hker _).1 h1 (hunit (φ₀ ⟨b, hb⟩) hb0 hbo)
      obtain ⟨v, hv⟩ := hbu.exists_right_inv
      have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
      have hf' : f = a * (v : L) := by
        calc f = f * (b * v) := by rw [hv', mul_one]
          _ = a * v := by rw [← mul_assoc, e]
      rw [hf']
      exact Q.mul_mem ha v.2
    let e : Q ≃+* S.ring := RingEquiv.ofBijective φ₀
      ⟨fun x y h => Subtype.ext (congrArg (fun s : S.ring => (s : L)) h), fun s => ⟨⟨s, hle s s.2⟩, rfl⟩⟩
    have h := ringKrullDim_eq_of_ringEquiv e
    rw [hdim, IsDiscreteValuationRing.ringKrullDim_eq_one] at h
    norm_num at h
  have hmemR : ∀ a : K, a ∈ φ.range ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a := by
    intro a
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨φ₀ q, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  have hfrac : ∀ a : K, ∃ x y : Q, φ y ≠ 0 ∧ a * φ y = φ x := by
    intro a
    obtain ⟨s, rfl⟩ := hψ a
    obtain ⟨x, hx, y, hy, hy0, hyo, e⟩ := hS.2 s s.2
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => (hker _).1 h (hunit (φ₀ ⟨y, hy⟩) hy0 hyo), ?_⟩
    show ψ s * ψ (φ₀ ⟨y, hy⟩) = ψ (φ₀ ⟨x, hx⟩)
    rw [← map_mul]
    exact congrArg ψ (Subtype.ext e)
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  let R := φ.range
  let φR : Q →+* R := φ.rangeRestrict
  haveI : IsNoetherianRing R := isNoetherianRing_range φ
  haveI : IsLocalRing R := IsLocalRing.of_surjective' φR φ.rangeRestrict_surjective
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {φR u} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective φR φ.rangeRestrict_surjective, ← hm,
      Ideal.map_span, Set.image_pair]
    have h0 : φR t = 0 := Subtype.ext hφt
    rw [h0, Ideal.span_insert_zero]
  have hu0R : φR u ≠ 0 := fun h => hφu (congrArg Subtype.val h)
  have hnf : ¬ IsField R := by
    intro hf
    obtain ⟨w, hw⟩ := hf.mul_inv_cancel hu0R
    have hmem : φR u ∈ IsLocalRing.maximalIdeal R := hmR ▸ Ideal.subset_span rfl
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_mul_eq_one w hw)
  haveI hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 1 5).2
      (show (IsLocalRing.maximalIdeal R).IsPrincipal from ⟨_, hmR⟩)
  let V : ValuationSubring K :=
    { R with
      mem_or_inv_mem' := by
        intro a
        obtain ⟨x, y, hy, e⟩ := hfrac a
        obtain ⟨c, hc | hc⟩ := ValuationRing.cond (φR x) (φR y)
        · right
          have hc' : φ x * (c : K) = φ y := congrArg Subtype.val hc
          have h1 : a * c = 1 := by
            refine mul_right_cancel₀ hy ?_
            linear_combination (c : K) * e + hc'
          rw [inv_eq_of_mul_eq_one_right h1]
          exact c.2
        · left
          have hc' : φ y * (c : K) = φ x := congrArg Subtype.val hc
          have h1 : a = c := by
            refine mul_right_cancel₀ hy ?_
            linear_combination e - hc'
          rw [h1]
          exact c.2 }
  have hconst : ∀ a, cK a ∈ V := fun a => (hmemR (cK a)).2 ⟨S.const a, hQ.const_mem a, hc a⟩
  have hφV : ∀ q : Q, φ q ∈ V := fun q => ⟨q, rfl⟩
  let φV : Q →+* V := φ.codRestrict V hφV
  have hφVs : Function.Surjective φV := by
    rintro ⟨v, q, rfl⟩
    exact ⟨q, rfl⟩
  haveI hdvrV : IsDiscreteValuationRing V := hdvr
  have hcomp : cK.codRestrict V hconst = φV.comp (cL.codRestrict Q hQ.const_mem) :=
    RingHom.ext fun a => Subtype.ext (hc a).symm
  let F : Place cK :=
    ⟨V, hconst, hdvrV, hcomp ▸ hQ.essFiniteType.comp (RingHom.FiniteType.of_surjective φV hφVs).essFiniteType⟩
  refine ⟨F, hmemR, fun us hus => ?_⟩
  have h1 : ψ us = ((φV u : V) : K) := by
    show ψ us = ψ (φ₀ u)
    exact congrArg ψ (Subtype.ext hus)
  have hmV : IsLocalRing.maximalIdeal V = Ideal.span {φV u} := hmR
  have hirr : Irreducible (φV u) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmV
  rw [h1]
  exact F.ord_irreducible hirr

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResiduePlaceOfTwoDimLocalModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  first | exact @GlobalTheory.FieldPair.residuePlace_of_locModel | exact GlobalTheory.FieldPair.residuePlace_of_locModel | (intros; apply GlobalTheory.FieldPair.residuePlace_of_locModel <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.AdjCodimTwo

theorem irreducible_of_ord_one {k K : Type} [Field k] [Field K] {c : k →+* K} (P : Place c)
    (x : P.ring) (hx : P.ord (x : K) = 1) : Irreducible x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hv0 : ((v : P.ring) : K) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
  have e : P.ord (((v : P.ring) * π ^ n : P.ring) : K) = n := by
    push_cast
    rw [P.ord_mul hv0 (pow_ne_zero _ hπ0), P.ord_eq_zero v.isUnit, P.ord_pow, P.ord_irreducible hπ]
    simp
  rw [e] at hx
  obtain rfl : n = 1 := by exact_mod_cast hx
  rw [pow_one]
  exact (irreducible_isUnit_mul v.isUnit).2 hπ

theorem disc_residue_eq : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
  ringKrullDim Q = 2 → S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : L) = 1 → E.ord (u : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) = 0) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    F.disc (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) =
      E.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
        (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n Q hQ t u S E ψ f w θ hm hd hS hE hSt hEu hψ hc hf hw hθ hP
  classical
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters cL Q hQ t u hm hd
  obtain ⟨m, z, hzU, hzG⟩ := GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons cL Q hQ t u hm hd
  have hxe : (fun i => ((Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q) i : L)) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => rfl) j
  have hzT := GlobalTheory.T.isTranscendenceBasis_of_kaehlerWedge_freeGenerator cL Q hQ _ _ (by omega) hzG
  have hzO := GlobalTheory.T.formOrd_freeTopForm_eq_zero_of_isPrimeOf cL Q hQ _ _ hzG
  rw [hxe] at hzT hzO
  obtain ⟨F, hFr, hFu⟩ := GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel cL cK Q hQ t u hm hd S ψ hS hSt hψ hc
  have hQS : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let us : S.ring := ⟨u, hQS u⟩
  let ts : S.ring := ⟨t, hQS t⟩
  let zs : Fin m → S.ring := fun i => ⟨z i, hQS (z i)⟩
  have hF1 : F.ord (ψ us) = 1 := hFu us rfl
  have hB4 := GlobalTheory.T.residuePlace_eval_ne_zero_inv_mem_of_isUnit cL cK Q hQ S ψ F hS.1 hc hFr m z zs (fun _ => rfl) hzU
  have hzF : ∀ i, ψ (zs i) ∈ F.ring := fun i => (hFr _).2 ⟨zs i, (z i).2, rfl⟩
  have hTK := GlobalTheory.T.isTranscendenceBasis_residueField_uniformiser_cons cL cK S ψ hψ hc F m (ψ us) (fun i => ψ (zs i)) ⟨_, hzT⟩ hF1 hzF hB4
  have hFO := GlobalTheory.T.formOrd_kaehlerWedge_uniformiser_residueIndependent_eq_zero cK F m (ψ us) (fun i => ψ (zs i)) hF1 hzF hB4 hTK
  obtain rfl : n = m + 1 := by
    letI := cK.toAlgebra
    have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hw
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hTK
    rw [Cardinal.mk_fin] at h1 h2
    exact_mod_cast h1.trans h2.symm
  let v : Fin (m + 1) → S.ring := Fin.cons us zs
  have hv : (fun i => ψ (v i)) = (Fin.cons (ψ us) (fun i => ψ (zs i)) : Fin (m + 1) → K) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have htv : (Fin.cons (ts : L) (fun i => (v i : L)) : Fin (m + 2) → L) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  set Ω0 := (dForm cL (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L)) with hΩ0
  set η := dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (m + 1 + 1) → L) with hη
  have hfreeL := (GlobalTheory.T.dvrPlace_topForm_orders_api cL (m + 2) _ hzT).1
  obtain ⟨H, hH⟩ := hfreeL.2 η
  have ht_irr : Irreducible ts := irreducible_of_ord_one S ts hSt
  obtain ⟨h, hhf, hhw⟩ := GlobalTheory.T.residue_topForm_along_primeDivisor_adjunction cL cK (m + 1) S ψ hψ hc ts f v w H ht_irr hf (hv ▸ hTK)
    (htv ▸ hzT) (by rw [htv]; exact hH.symm)
  rw [hv] at hhw
  have hne : ∀ {A M : Type} [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] {ω : M},
      IsFreeGen A ω → ω ≠ 0 := fun hω h0 => one_ne_zero (hω.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  have hIK := GlobalTheory.T.dvrPlace_topForm_orders_api cK (m + 1) _ hTK
  have hIL := GlobalTheory.T.dvrPlace_topForm_orders_api cL (m + 2) _ hzT
  have hwne := hne (GlobalTheory.T.dvrPlace_topForm_orders_api cK (m + 1) _ hw).1
  have hvne := hne hIK.1
  have hΩne : Ω0 ≠ 0 := hne hfreeL
  have hψh : ψ h ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hhw
    exact hwne hhw
  have hh0 : (h : L) ≠ 0 := fun h0 => hψh (by rw [show h = 0 from Subtype.ext h0, map_zero])
  have hf0 : (f : L) ≠ 0 := fun h0 => hf.ne_zero (Subtype.ext h0)
  have ht0 : (t : L) ≠ 0 := fun h0 => ht_irr.ne_zero (Subtype.ext h0)
  have hH0 : H ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hhf
    exact mul_ne_zero hh0 hf0 hhf
  have hFw : F.formOrd (dForm cK (fun i => ψ (w i))) = F.ord (ψ h) := by
    have hs : F.formOrd (ψ h • dForm cK (Fin.cons (ψ us) (fun i => ψ (zs i)))) =
        F.ord (ψ h) + F.formOrd (dForm cK (Fin.cons (ψ us) (fun i => ψ (zs i)))) := by
      simpa only [Place.formOrd] using (hIK.2 F).2.2.1 _ _ hvne hψh
    rw [hhw, hs]
    simpa only [Place.formOrd, hFO, add_zero]
  have hPη : ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd η = P.ord H := by
    intro P hPQ
    have hs : P.formOrd (H • Ω0) = P.ord H + P.formOrd Ω0 := by
      simpa only [Place.formOrd] using (hIL.2 P).2.2.1 Ω0 H hΩne hH0
    rw [← hH, hs]
    simpa only [Place.formOrd, hzO P hPQ, add_zero]
  have hPo : ∀ P : Place cL, P.ord (h : L) + P.ord (f : L) = P.ord H + P.ord (t : L) := by
    intro P
    rw [← P.ord_mul hh0 hf0, ← P.ord_mul hH0 ht0, hhf]
  have hEt : E.ord (t : L) = 0 := (hA2 E hE).resolve_right (by rw [hEu]; norm_num)
  have hSu : S.ord (u : L) = 0 := (hA2 S hS).resolve_left (by rw [hSt]; norm_num)
  have hu0 : (u : L) ≠ 0 := by
    intro h0
    rw [h0] at hEu
    simp [Place.ord] at hEu
  have hE1 := GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo cL Q hQ t u hm hd E hE hEu
  set θ' := Finsupp.mapDomain (fun g : S.ring => (g : L)) θ with hθ'
  have hφs : ∀ g ∈ (Finsupp.single h 1 - θ).support, ψ g ≠ 0 := by
    intro g hg
    rcases Finset.mem_union.1 (Finsupp.support_sub hg) with hg | hg
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
      exact hψh
    · exact hθ g hg
  have hmc : Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ) =
      Finsupp.single (h : L) 1 - θ' := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hmψ : Finsupp.mapDomain ψ (Finsupp.single h 1 - θ) =
      Finsupp.single (ψ h) 1 - Finsupp.mapDomain ψ θ := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hφP : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ)) = 0 := by
    intro P hPQ hPS hPE
    have h1 := hP P hPQ hPS hPE
    rw [Place.disc, map_add (f := _), Place.ordQ_single, hPη P hPQ] at h1
    have hPt : P.ord (t : L) = 0 := by
      by_contra hne'
      have h0 : 0 ≤ P.ord (t : L) := (P.ord_nonneg_iff ht0).2 (hPQ.1 t t.2)
      exact hPS (hA1 P S hPQ hS (lt_of_le_of_ne h0 (Ne.symm hne')) (by rw [hSt]; norm_num))
    have h2 := hPo P
    rw [hPt, add_zero] at h2
    rw [hmc, map_sub, Place.ordQ_single]
    have h3 : ((P.ord (h : L) : ℤ) : ℚ) = (P.ord H : ℚ) - (P.ord (f : L) : ℚ) := by
      rw [← h2]; push_cast; ring
    rw [h3]
    linarith
  have hE2 := GlobalTheory.T.ordQ_mapDomain_residuePlace_transport cL cK Q u S E ψ F hS.1 hSu hu0 hψ hFr hFu hE1 _ hφs hφP
  rw [hmc, hmψ, map_sub, map_sub, Place.ordQ_single, Place.ordQ_single] at hE2
  refine ⟨F, hFr, ?_⟩
  rw [Place.disc, Place.disc, hFw, map_add (f := _), Place.ordQ_single, hPη E hE]
  have h2 := hPo E
  rw [hEt, add_zero] at h2
  have h3 : ((E.ord H : ℤ) : ℚ) = (E.ord (h : L) : ℚ) + (E.ord (f : L) : ℚ) := by
    rw [← h2]; push_cast; ring
  rw [h3]
  linarith

end GlobalTheory.AdjCodimTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjunctionKltOfKltAlongResidueSubring
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_of_klt_restrict : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n T S hS ψ f w θ R hψ hc hf hw hθ hR hK
  refine ⟨?_, ?_, ?_⟩
  · have htr := (trBasis_uniformiser_cons cL cK n S ψ f w hψ hc hf hw).1
    have hfree := (formOrd_api cL (n + 1) _ htr).1
    exact fun h0 => one_ne_zero (hfree.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  · have hf0 : (0 : L) ≠ (f : L) := fun h => hf.ne_zero (Subtype.ext h.symm)
    have hθ0 : θ 0 = 0 := by
      by_contra h
      exact hθ 0 (Finsupp.mem_support_iff.2 h) (map_zero ψ)
    have h1 : Finsupp.mapDomain (fun g : S.ring => (g : L)) θ ((0 : S.ring) : L) = θ 0 :=
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective θ 0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hf0, add_zero]
    exact h1.trans hθ0
  intro Q hQ t u E hTQ hspan hdim hSQ hEQ hSt hEu hP
  obtain ⟨F, hF, hdisc⟩ := GlobalTheory.AdjCodimTwo.disc_residue_eq cL cK n Q hQ t u S E ψ f w θ hspan hdim
    hSQ hEQ hSt hEu hψ hc hf hw hθ hP
  rw [← hdisc]
  apply hK.lt_disc
  intro a ha
  obtain ⟨x, hx⟩ := hR a ha
  exact (hF a).2 ⟨⟨x, hS x x.2⟩, hTQ x.2, hx⟩

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjunctionKltOfKltAlongResidueSubringStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjunctionKlt_of_klt_along_residue_subring : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (S : Place cL) (hS : S.Contains T) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ) (R : Subring K), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → (∀ g ∈ θ.support, ψ g ≠ 0) → (∀ a ∈ R, ∃ t : T, ψ ⟨t, hS t t.2⟩ = a) → Klt cK n R (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) → AdjKlt cL (n + 1) T S (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  first | exact @GlobalTheory.FieldPair.adjKlt_of_klt_restrict | exact GlobalTheory.FieldPair.adjKlt_of_klt_restrict | (intros; apply GlobalTheory.FieldPair.adjKlt_of_klt_restrict <;> assumption)
end
