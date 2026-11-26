module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralValuesEqualCharacteristic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPole
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValue
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValue
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.Enlarge

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_den {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {g : Ω} (hg : g ∈ Algebra.adjoin K gs) :
    ∃ d : O, d ≠ 0 ∧ algebraMap K Ω (algebraMap O K d) * g ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by
  set S := Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) with hS
  have hOS : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ S := fun a =>
    Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨(1 : O), one_ne_zero, ?_⟩
    rw [map_one, map_one, one_mul]
    exact Subring.subset_closure (Set.mem_union_right _ hx)
  | algebraMap x =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    have hb' : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    rw [← map_mul, mul_div_cancel₀ _ hb']
    exact hOS a
  | add x y _ _ hx hy =>
    obtain ⟨d1, h1, hx⟩ := hx
    obtain ⟨d2, h2, hy⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero h1 h2, ?_⟩
    have : algebraMap K Ω (algebraMap O K (d1 * d2)) * (x + y) =
        algebraMap K Ω (algebraMap O K d2) * (algebraMap K Ω (algebraMap O K d1) * x) +
          algebraMap K Ω (algebraMap O K d1) * (algebraMap K Ω (algebraMap O K d2) * y) := by
      simp only [map_mul]; ring
    rw [this]
    exact S.add_mem (S.mul_mem (hOS _) hx) (S.mul_mem (hOS _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨d1, h1, hx⟩ := hx
    obtain ⟨d2, h2, hy⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero h1 h2, ?_⟩
    have : algebraMap K Ω (algebraMap O K (d1 * d2)) * (x * y) =
        (algebraMap K Ω (algebraMap O K d1) * x) * (algebraMap K Ω (algebraMap O K d2) * y) := by
      simp only [map_mul]; ring
    rw [this]
    exact S.mul_mem hx hy

theorem clear_den {K Ω O : Type} [Field K] [Field Ω] [Algebra K Ω] [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (gs : Set Ω) {r : Ω} (hr : IsIntegral (Algebra.adjoin K gs) r) :
    ∃ κ : O, κ ≠ 0 ∧ ∃ q : Polynomial Ω, q.Monic ∧ q.eval (algebraMap K Ω (algebraMap O K κ) * r) = 0 ∧
      ∀ i, q.coeff i ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) := by
  set S := Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gs) with hS
  have hOS : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ S := fun a =>
    Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hr
  have hex := fun i => exists_den (O := O) gs (p.coeff i).2
  choose d hd0 hd using hex
  set κ : O := ∏ i ∈ Finset.range (p.natDegree + 1), d i with hκdef
  have hκ : κ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hd0 i)
  have hκc : ∀ i, algebraMap K Ω (algebraMap O K κ) * ((p.coeff i : Algebra.adjoin K gs) : Ω) ∈ S := by
    intro i
    by_cases hi : i ∈ Finset.range (p.natDegree + 1)
    · rw [hκdef, ← Finset.mul_prod_erase _ _ hi, map_mul, map_mul, mul_comm (algebraMap K Ω (algebraMap O K (d i))),
        mul_assoc]
      exact S.mul_mem (hOS _) (hd i)
    · have : p.coeff i = 0 := p.coeff_eq_zero_of_natDegree_lt (by simp at hi; omega)
      rw [this]
      simp
  set k := algebraMap K Ω (algebraMap O K κ) with hk
  set pm := p.map (algebraMap (Algebra.adjoin K gs) Ω) with hpmdef
  have hpmm : pm.Monic := hpm.map _
  have hdeg : pm.natDegree = p.natDegree := hpm.natDegree_map _
  refine ⟨κ, hκ, pm.scaleRoots k, (monic_scaleRoots_iff k).mpr hpmm, ?_, ?_⟩
  · have h0 : eval₂ (RingHom.id Ω) r pm = 0 := by
      rw [eval₂_id, hpmdef, Polynomial.eval_map]; exact hp
    have := scaleRoots_eval₂_eq_zero (RingHom.id Ω) h0 (s := k)
    rwa [eval₂_id] at this
  · intro i
    rw [coeff_scaleRoots]
    have hci : pm.coeff i = ((p.coeff i : Algebra.adjoin K gs) : Ω) := by
      rw [hpmdef, coeff_map]; rfl
    rcases h : pm.natDegree - i with _ | m
    · rcases (show pm.natDegree ≤ i by omega).lt_or_eq with hlt | heq
      · rw [coeff_eq_zero_of_natDegree_lt hlt]; simp
      · rw [← heq, hpmm.coeff_natDegree]; simp
    · have : pm.coeff i * k ^ (m + 1) = k ^ m * (k * ((p.coeff i : Algebra.adjoin K gs) : Ω)) := by
        rw [hci]; ring
      rw [this]
      exact S.mul_mem (S.pow_mem (hOS κ) m) (hκc i)

theorem mem_of_root {K Ω L : Type} [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (A : Subalgebra K Ω)
    (Sb : Subring Ω) (hSA : ∀ x ∈ Sb, x ∈ A) (ψ : A →ₐ[K] L) (W : ValuationSubring L)
    (hW : ∀ x (hx : x ∈ Sb), ψ ⟨x, hSA x hx⟩ ∈ W) (q : Polynomial Ω) (hqm : q.Monic) (hqc : ∀ i, q.coeff i ∈ Sb)
    (t : Ω) (ht : t ∈ A) (h0 : q.eval t = 0) : ψ ⟨t, ht⟩ ∈ W := by
  let incl : Sb →+* A :=
    { toFun := fun x => ⟨x, hSA x x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let θ : Sb →+* W := ((ψ : A →+* L).comp incl).codRestrict W (fun x => hW x x.2)
  have hcs : (q.coeffs : Set Ω) ⊆ Sb := by
    intro x hx
    obtain ⟨n, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact hqc n
  set q' := q.toSubring Sb hcs with hq'
  have hq'm : q'.Monic := (Polynomial.monic_toSubring q Sb hcs).mpr hqm
  have hroot : Polynomial.eval₂ incl ⟨t, ht⟩ q' = 0 := by
    apply Subtype.ext
    have key := Polynomial.hom_eval₂ q' incl ((A.val : A →ₐ[K] Ω) : A →+* Ω) ⟨t, ht⟩
    rw [show ((A.val : A →ₐ[K] Ω) : A →+* Ω).comp incl = Sb.subtype from RingHom.ext fun _ => rfl,
      Polynomial.eval₂_eq_eval_map Sb.subtype, hq', Polynomial.map_toSubring] at key
    change ((A.val : A →ₐ[K] Ω) : A →+* Ω) _ = 0
    rw [key]
    exact h0
  have hint : IsIntegral W (ψ ⟨t, ht⟩) := by
    refine ⟨q'.map θ, hq'm.map θ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap W L).comp θ = (ψ : A →+* L).comp incl := RingHom.ext fun _ => rfl
    rw [hc]
    have h1 := Polynomial.hom_eval₂ q' incl (ψ : A →+* L) ⟨t, ht⟩
    rw [hroot, map_zero] at h1
    exact h1.symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hw]
  exact w.2

def trPt {Ω : Type} [Field Ω] [Algebra c.F Ω] {A B : Subalgebra c.F Ω} (h : A = B) (y : FrPt Xo c A) :
    FrPt Xo c B :=
  h ▸ y

theorem frMap_trPt {Ω : Type} [Field Ω] [Algebra c.F Ω] {A B : Subalgebra c.F Ω} (h : A = B) {T : Type} [CommRing T]
    [Algebra c.F T] (ψ : B →ₐ[c.F] T) (y : FrPt Xo c A) (z : FrPt Xo c T) :
    FrMap ψ (trPt h y) z ↔ FrMap (ψ.comp (Subalgebra.equivOfEq A B h).toAlgHom) y z := by
  subst h
  have : ψ.comp (Subalgebra.equivOfEq A A rfl).toAlgHom = ψ := AlgHom.ext fun _ => rfl
  rw [this]
  rfl

variable {O : Type} [CommRing O] {β : O →+* c.F}

attribute [local instance] Classical.propDecidable

theorem eqR (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) (e : P.Ω) (he : e ∈ P.es) :
    P.R e = Algebra.adjoin c.F (insert e⁻¹ ((insert s P.gens : Finset P.Ω) : Set P.Ω)) := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.insert_subset_insert (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
  · rw [Algebra.adjoin_le_iff, Finset.coe_insert]
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact Algebra.subset_adjoin (Set.mem_insert _ _)
    · exact hs e he
    · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

def enlarge (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) : PChart Xo c β where
  Ω := P.Ω
  fld := P.fld
  alg := P.alg
  gens := insert s P.gens
  frac := by
    rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _))
  es := P.es
  es_ne := P.es_ne
  es_mem e he := ⟨(P.es_mem e he).1, Subring.closure_mono
    (Set.union_subset_union_right _ (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)) (P.es_mem e he).2⟩
  sm e he := by rw [← eqR P s hs e he]; exact P.sm e he
  yg := P.yg
  y e he := trPt (eqR P s hs e he) (P.y e he)
  gen e he := by
    rw [frMap_trPt]
    have : (Algebra.adjoin c.F (insert e⁻¹ ((insert s P.gens : Finset P.Ω) : Set P.Ω))).val.comp
        (Subalgebra.equivOfEq _ _ (eqR P s hs e he)).toAlgHom = (P.R e).val := AlgHom.ext fun _ => rfl
    rw [this]
    exact P.gen e he
  int e he T io := by
    intro ψ hO hg z hz
    letI : Algebra c.F T.Fr := io.toAlgebra
    exact P.int e he T io (ψ.comp (Subalgebra.equivOfEq (P.R e) _ (eqR P s hs e he)).toAlgHom) hO
      (fun g hgm => hg _ (Finset.mem_insert_of_mem hgm)) z ((frMap_trPt (eqR P s hs e he) ψ (P.y e he) z).mp hz)

theorem catches_enlarge (P : PChart Xo c β) (s : P.Ω) (hs : ∀ e ∈ P.es, s ∈ P.R e) {L : Type} [Field L]
    [Algebra c.F L] (W : ValuationSubring L) (hW : ∀ a : O, algebraMap c.F L (β a) ∈ W) (q : Polynomial P.Ω)
    (hqm : q.Monic) (hq0 : q.eval s = 0) (hqc : ∀ i, q.coeff i ∈ P.B) (y : FrPt Xo c L) (hy : P.Catches W y) :
    (enlarge P s hs).Catches W y := by
  obtain ⟨e, he, ψ, z, t, hg, hm, hb⟩ := hy
  have hR := eqR P s hs e he
  refine ⟨e, he, ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom, z, t, ?_, ?_, hb⟩
  · intro g hgm
    rcases Finset.mem_insert.mp hgm with h | h
    · have hBA : ∀ x ∈ P.B, x ∈ P.R e := by
        intro x hx
        refine (Subring.closure_le (t := (P.R e).toSubring)).mpr ?_ hx
        rintro x (⟨a, rfl⟩ | hx)
        · exact Subalgebra.algebraMap_mem _ _
        · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
      have hWB : ∀ x (hx : x ∈ P.B), ψ ⟨x, hBA x hx⟩ ∈ W := by
        intro x hx
        have hle : P.B ≤ ((W.toSubring.comap (ψ : P.R e →+* L)).map ((P.R e).val : P.R e →+* P.Ω)) := by
          rw [Subring.closure_le]
          rintro x (⟨a, rfl⟩ | hx)
          · refine ⟨algebraMap c.F (P.R e) (β a), ?_, rfl⟩
            show ψ (algebraMap c.F (P.R e) (β a)) ∈ W
            rw [AlgHom.commutes]; exact hW a
          · exact ⟨⟨x, Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)⟩, hg _ hx, rfl⟩
        obtain ⟨a, ha, hax⟩ := hle hx
        have : a = ⟨x, hBA x hx⟩ := Subtype.ext hax
        subst this
        exact ha
      have hgR : (show P.Ω from g.1) ∈ P.R e := by rw [hR]; exact g.2
      exact mem_of_root (P.R e) P.B hBA ψ W hWB q hqm hqc (show P.Ω from g.1) hgR (by rw [h]; exact hq0)
    · exact hg (Subalgebra.equivOfEq _ _ hR.symm g) h
  · have : (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom).comp (Subalgebra.equivOfEq _ _ hR).toAlgHom = ψ :=
      AlgHom.ext fun _ => rfl
    exact (frMap_trPt hR (ψ.comp (Subalgebra.equivOfEq _ _ hR.symm).toAlgHom) (P.y e he) z).mpr
      (by rw [this]; exact hm)

theorem enlarge_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ f P hR hI
  obtain ⟨κ, hκ, q, hqm, hq0, hqc⟩ := clear_den (O := O) (P.gens : Set P.Ω) hI
  have hk : algebraMap O c.F κ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hκ)
  set r := evR Xo c f P.yg with hr
  set s := algebraMap c.F P.Ω (algebraMap O c.F κ) * r with hsdef
  have hs : ∀ e ∈ P.es, s ∈ P.R e := fun e he =>
    Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hR e he)
  refine ⟨enlarge P s hs, ?_, fun L _ _ W hW y hy => catches_enlarge P s hs W hW q hqm hq0 hqc y hy⟩
  show r ∈ Algebra.adjoin c.F ((insert s P.gens : Finset P.Ω) : Set P.Ω)
  have : r = algebraMap c.F P.Ω (algebraMap O c.F κ)⁻¹ * s := by
    rw [hsdef, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
  rw [this]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin (by simp))

end GlobalTheory.Reg.Enlarge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValueStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  first | exact @GlobalTheory.Reg.Enlarge.enlarge_exists | exact GlobalTheory.Reg.Enlarge.enlarge_exists | (intros; apply GlobalTheory.Reg.Enlarge.enlarge_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralAdjoinOfForallCdvr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralAdjoinOfForallCdvr
open Formalism.L2.Pj

open IsLocalRing

namespace GlobalTheory

theorem isIntegral_adjoin_of_forall_cdvr (K Ω : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (gens : Finset Ω)
    (hcl : Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤) (x : Ω)
    (hx : ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr,
      (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) →
      (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) :
    IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  classical
  set A := Algebra.adjoin K (gens : Set Ω) with hAdef

  have hfrac : ∀ z : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ z * b = a := by
    intro z
    have hz : z ∈ Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) := hcl ▸ trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
    have hc : Subring.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = A.toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm
    rw [hc] at ha hb
    rcases eq_or_ne b 0 with rfl | hb0
    · exact ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, by simp⟩
    · exact ⟨a, ha, b, hb, hb0, div_mul_cancel₀ a hb0⟩

  have hKc : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have hΩc : Countable Ω := by
    have hs : (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)).Countable :=
      (Set.countable_range _).union gens.finite_toSet.countable
    have h1 : Cardinal.mk (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))) ≤
        Cardinal.aleph0 :=
      (Subfield.cardinalMk_closure_le_max _).trans
        (max_le (Cardinal.mk_le_aleph0_iff.2 hs.to_subtype) le_rfl)
    have h2 := Cardinal.mk_le_aleph0_iff.1 h1
    rw [hcl] at h2
    exact Function.Injective.countable (f := fun (z : Ω) => (⟨z, trivial⟩ : (⊤ : Subfield Ω)))
      fun a b h => congrArg Subtype.val h

  have hAft : Algebra.FiniteType K A := .adjoin_of_finite gens.finite_toSet
  have hAn : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hess : Algebra.EssFiniteType A Ω := by
    refine (Algebra.essFiniteType_iff A Ω).mpr ⟨∅, fun z => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hfrac z
    simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot]
    exact ⟨b, ⟨⟨b, hb⟩, rfl⟩, isUnit_iff_ne_zero.mpr hb0, ⟨⟨a, ha⟩, hab.symm⟩⟩
  by_contra hni
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hni isIntegral_zero

  letI := invertibleOfNonzero (inv_ne_zero hx0)
  let B := Algebra.adjoin A {x⁻¹}
  let xinv : B := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have hne : (⊥ : Ideal A).map (algebraMap A B) ⊔ Ideal.span {xinv} ≠ ⊤ := by
    intro heq
    obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
      x⁻¹ (⊥ : Ideal A) bot_ne_top heq
    have hm : p.Monic := by
      rw [Ideal.mem_bot, sub_eq_zero] at hp
      exact hp
    rw [invOf_eq_inv, inv_inv] at hpx
    exact hni ⟨p, hm, by rw [← Polynomial.aeval_def, hpx]⟩
  obtain ⟨W, hW, hW'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ hne
  have hxW : x⁻¹ ∈ W.nonunits := hW' ⟨xinv, Ideal.mem_sup_right (Ideal.subset_span rfl), rfl⟩

  obtain ⟨V, hV, hAV, -, hxV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := A)
    W (fun r => hW (B.algebraMap_mem r)) (s := ∅) (t := {x⁻¹}) Set.finite_empty
    (Set.finite_singleton _) (by simp) (by simpa using hxW) ⟨x⁻¹, rfl, inv_ne_zero hx0⟩
  have hxV' : x⁻¹ ∈ V.nonunits := hxV _ rfl
  have hKV : ∀ k : K, algebraMap K Ω k ∈ V := fun k => hAV (algebraMap K A k)
  have hgV : ∀ g ∈ gens, g ∈ V := fun g hg => hAV ⟨g, Algebra.subset_adjoin hg⟩

  let ι := algebraMap V (AdicCompletion (maximalIdeal V) V)
  have hch : CharZero (AdicCompletion (maximalIdeal V) V) :=
    (RingHom.charZero_iff (ι.comp ((algebraMap K Ω).codRestrict V hKV)).injective).1 inferInstance
  let T : CDVR := { V := AdicCompletion (maximalIdeal V) V, ch0 := hch }
  have hVc : Countable V := Subtype.countable
  have hres : Countable (ResidueField T.V) := by
    have hsurj : Function.Surjective ((residue T.V).comp ι) := by
      intro t0
      obtain ⟨t, rfl⟩ := residue_surjective t0
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (maximalIdeal V) 1 t)
      refine ⟨r, ?_⟩
      change residue T.V (ι r) = residue T.V t
      change Ideal.Quotient.mk _ (ι r) = Ideal.Quotient.mk _ t
      rw [Ideal.Quotient.eq]
      intro hu
      have hnt : Nontrivial (V ⧸ maximalIdeal V ^ 1) := by
        rw [pow_one]; infer_instance
      have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal V) 1)
      rw [map_sub] at h1
      change IsUnit ((AdicCompletion.evalₐ (maximalIdeal V) 1) (AdicCompletion.of _ _ r) - _) at h1
      rw [AdicCompletion.evalₐ_of, hr, sub_self] at h1
      exact not_isUnit_zero h1
    exact hsurj.countable
  have hg : Function.Injective ((algebraMap T.V T.Fr).comp ι) :=
    (IsFractionRing.injective T.V T.Fr).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let φ : Ω →+* T.Fr := IsFractionRing.lift (A := V) hg
  have hφ : ∀ v : V, φ v = algebraMap T.V T.Fr (ι v) := fun v => IsFractionRing.lift_algebraMap hg v
  obtain ⟨t, ht⟩ := hx T hres φ (fun k => ⟨ι ⟨_, hKV k⟩, (hφ ⟨_, hKV k⟩).symm⟩)
    (fun g hg' => ⟨ι ⟨g, hgV g hg'⟩, (hφ ⟨g, hgV g hg'⟩).symm⟩)
  let y : V := ⟨x⁻¹, V.nonunits_subset hxV'⟩
  have h1 : algebraMap T.V T.Fr (t * ι y) = 1 := by
    rw [map_mul, ht, ← hφ y]
    change φ x * φ x⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  have h2 : t * ι y = 1 := IsFractionRing.injective T.V T.Fr (h1.trans (map_one _).symm)
  have h3 : IsUnit (ι y) := isUnit_iff_exists_inv.mpr ⟨t, by rw [mul_comm]; exact h2⟩
  exact (ValuationSubring.coe_mem_nonunits_iff (a := y)).mp hxV' (isUnit_of_map_unit ι y h3)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralAdjoinOfForallCdvrStatement
open Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (gens : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → ∀ x : Ω, (∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr, (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) → (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) → IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  first | exact @GlobalTheory.isIntegral_adjoin_of_forall_cdvr | exact GlobalTheory.isIntegral_adjoin_of_forall_cdvr | (intros; apply GlobalTheory.isIntegral_adjoin_of_forall_cdvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPole
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspReg

theorem exists_cover_noPole : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ (J : Type) (_ : Finite J) (P : J → GlobalTheory.Reg.PChart Xo c (algebraMap (la.valuation c.F).valuationSubring c.F)), GlobalTheory.Reg.Covers P ∧ ∀ j, evR Xo c f (P j).yg ∈ Algebra.adjoin c.F ((P j).gens : Set (P j).Ω) := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
  obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hF := cusp_le_sec Xo c U a n hf
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
  have hY : ∃ Y : Model Xo c (algebraMap (la.valuation c.F).valuationSubring c.F),
      PushInvertible Y.t.G Y.t.PP.L := by
    by_cases hr : 1 ≤ Dw.p + Dw.q
    · obtain ⟨Y, hP, -⟩ := GlobalTheory.GoodTransfer.exists_model hr Xo c la p hp hpl hg
      exact ⟨Y, hP⟩
    · exact GlobalTheory.SupFinite.exists_model_rank_zero (Xo := Xo) (c := c) (by omega) _
  obtain ⟨Y, hP⟩ := hY
  obtain ⟨J, hJ, P, hC⟩ := GlobalTheory.Reg.exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c
    hE.bc (la.valuation c.F).valuationSubring Y hP
  set_option synthInstance.maxHeartbeats 200000 in
  have hmem : ∀ j, ∀ e ∈ (P j).es, evR Xo c f (P j).yg ∈ (P j).R e := fun j e he => by
    rw [(hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)]
    exact (evR Xo c f ((P j).y e he)).2
  have hint : ∀ j, IsIntegral (Algebra.adjoin c.F ((P j).gens : Set (P j).Ω)) (evR Xo c f (P j).yg) := by
    intro j
    refine GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem c.F (P j).Ω (P j).gens (P j).frac _ fun T hT φ hK hgn => ?_
    obtain ⟨e, he⟩ := (P j).es_ne
    let io : c.F →+* T.Fr := φ.comp (algebraMap c.F (P j).Ω)
    letI := io.toAlgebra
    let ψ : (P j).R e →ₐ[c.F] T.Fr :=
      { toRingHom := φ.comp ((P j).R e).val.toRingHom, commutes' := fun k => rfl }
    obtain ⟨z, hz⟩ := hE.bc _ _ ψ ((P j).y e he)
    have hzI := (P j).int e he T io ψ (fun a => hK _) (fun g hg' => hgn _ hg') z hz
    have h1 := GlobalTheory.T.cuspForm_integral_values_equal_characteristic E H Dw l Xo c r U hU a n f hd hf T hT io hK ⟨z, hE.test _ z, hzI⟩
    have e1 : evR Xo c f z = ψ (evR Xo c f ((P j).y e he)) := (hev _).1 _ ψ _ _ hz
    have e2 : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
      (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
    rw [e2]
    change evR Xo c f z ∈ _ at h1
    rw [e1] at h1
    exact h1
  choose P' hP'1 hP'2 using fun j => GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value E H Dw l Xo c (la.valuation c.F).valuationSubring f (P j) (hmem j) (hint j)
  refine ⟨J, hJ, P', fun L _ _ W hW y => ?_, hP'1⟩
  obtain ⟨j, hj⟩ := hC L W hW y
  exact ⟨j, hP'2 j L W hW y hj⟩

end GlobalTheory.CuspReg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralChartCoverCuspFormNoPoleStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_chart_cover_cuspForm_no_pole : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ (J : Type) (_ : Finite J) (P : J → GlobalTheory.Reg.PChart Xo c (algebraMap (la.valuation c.F).valuationSubring c.F)), GlobalTheory.Reg.Covers P ∧ ∀ j, evR Xo c f (P j).yg ∈ Algebra.adjoin c.F ((P j).gens : Set (P j).Ω) := by
  first | exact @GlobalTheory.CuspReg.exists_cover_noPole | exact GlobalTheory.CuspReg.exists_cover_noPole | (intros; apply GlobalTheory.CuspReg.exists_cover_noPole <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultiple
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CuspBound

theorem exists_mul_mem_closure {O K Ω : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field Ω] [Algebra K Ω] (S : Set Ω) {x : Ω} (hx : x ∈ Algebra.adjoin K S) :
    ∃ κ : O, κ ≠ 0 ∧ algebraMap K Ω (algebraMap O K κ) * x ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) := by
  have hmem : ∀ u : O, algebraMap K Ω (algebraMap O K u) ∈
      Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ S) :=
    fun u => Subring.subset_closure (Or.inl ⟨u, rfl⟩)
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    exact ⟨1, one_ne_zero, by rw [map_one, map_one, one_mul]; exact Subring.subset_closure (Or.inr hx)⟩
  | algebraMap r =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) r
    have hb0 : algebraMap O K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← map_mul, mul_div_cancel₀ _ hb0]
    exact hmem a
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x + y) =
        algebraMap K Ω (algebraMap O K t) * (algebraMap K Ω (algebraMap O K s) * x) +
        algebraMap K Ω (algebraMap O K s) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (hmem t) h1) (mul_mem (hmem s) h2)
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, h1⟩ := hx
    obtain ⟨t, ht, h2⟩ := hy
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : algebraMap K Ω (algebraMap O K (s * t)) * (x * y) =
        (algebraMap K Ω (algebraMap O K s) * x) * (algebraMap K Ω (algebraMap O K t) * y) := by
      simp only [map_mul]; ring
    rw [e]
    exact mul_mem h1 h2

theorem inV_iff' (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0; simp [InV, vV]
  have hne := valV_ne_zero (V := T.V) h0
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log hne one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV; omega
  · intro h
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log hne one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_of_overLa' {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR}
    {io : K →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e) (a : (la.valuation K).valuationSubring) : InV T (io a) := by
  rw [inV_iff', ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : (a : K) = 0
  · simp [h0, vLa]
  have hne : la.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h2 := (WithZero.log_le_log hne one_ne_zero).2 a.2
  rw [WithZero.log_one] at h2
  unfold vLa; omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff_of_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : CDVR}
    {io : c.F →+* T.Fr} (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ)
    (h : letI := io.toAlgebra; FrBor t y.1 y'.1) : InV T (evI y f) ↔ InV T (evI y' f) := by
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h1 := unitIndep_of hE.wt hU a n f hf T io y y' t h 1
  have key : ∀ x : T.Fr, InV T x ↔ 0 ≤ nval T.V 1 x := fun x => by
    by_cases h0 : x = 0
    · subst h0; simp [nval_zero, InV]
    · rw [nval_of_ne h0, inV_iff', EReal.coe_nonneg]; simp
  rw [key, key, h1]

theorem inV_of_mem_B {O : Type} [CommRing O] {β : O →+* c.F} (P : GlobalTheory.Reg.PChart Xo c β) {e : P.Ω} {T : CDVR}
    {io : c.F →+* T.Fr} (ψ : P.R e →+* T.Fr) (hψ : ∀ k, ψ (algebraMap c.F _ k) = io k) (hO : ∀ a, InV T (io (β a)))
    (hg : ∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) (s : P.R e) (hs : (s : P.Ω) ∈ P.B) : InV T (ψ s) := by
  have hle : P.B ≤ (((algebraMap T.V T.Fr).range.comap ψ).map (P.R e).val.toRingHom) := by
    refine Subring.closure_le.2 ?_
    rintro w (⟨o, rfl⟩ | hw)
    · refine ⟨algebraMap c.F _ (β o), ?_, rfl⟩
      show ψ (algebraMap c.F _ (β o)) ∈ (algebraMap T.V T.Fr).range
      rw [hψ]; exact hO o
    · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
  obtain ⟨w, hw, hw'⟩ := hle hs
  obtain rfl : w = s := Subtype.ext hw'
  exact hw

end GlobalTheory.CuspBound

namespace GlobalTheory.CuspBound


set_option maxHeartbeats 1000000 in
theorem exists_bddAll_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
    obtain ⟨J, hJ, P, hC, hreg⟩ := GlobalTheory.T.exists_integral_chart_cover_cuspForm_no_pole E H Dw l Xo c r U hU la p hp hpl hg a n f hd hf
    haveI := Fintype.ofFinite J
    choose κ hκ0 hκ using fun j =>
      exists_mul_mem_closure (O := (la.valuation c.F).valuationSubring) (K := c.F) ((P j).gens : Set (P j).Ω) (hreg j)
    have hF := cusp_le_sec Xo c U a n hf
    refine ⟨algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j), ?_, ?_⟩
    · exact (map_ne_zero_iff _ (IsFractionRing.injective _ c.F)).2 (Finset.prod_ne_zero_iff.2 fun j _ => hκ0 j)
    intro T io m ho y _
    letI := io.toAlgebra
    obtain ⟨hE, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
    have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hF
    let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
    have hW : ∀ x, x ∈ W ↔ InV T x := fun x =>
      ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h,
        by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
    have hO : ∀ a : (la.valuation c.F).valuationSubring, InV T (io (algebraMap _ c.F a)) := fun a => inV_of_overLa' ho a
    obtain ⟨j, e, he, ψ, z, t, hgW, hz, ht⟩ := hC T.Fr W (fun a => (hW _).2 (hO a)) y.1
    have hzI : Integral T io z := (P j).int e he T io ψ (fun a => hO a) (fun g hg => (hW _).1 (hgW g hg)) z hz
    let z' : IntFr Xo c T io := ⟨z, hE.test _ z, hzI⟩
    set κ' := algebraMap (la.valuation c.F).valuationSubring c.F (∏ j, κ j) with hκ'
    rw [← evI_smul, inV_iff_of_frBor (Submodule.smul_mem _ κ' hF) y z' t ht, evI_smul]
    show InV T (io κ' * evR Xo c f z)
    rw [(hev _).1 _ ψ _ _ hz]
    let s : (P j).R e := algebraMap c.F _ κ' * evR Xo c f ((P j).y e he)
    have hs : ψ s = io κ' * ψ (evR Xo c f ((P j).y e he)) := by
      simp only [s, map_mul, AlgHom.commutes]; rfl
    rw [← hs]
    refine inV_of_mem_B (P j) ψ.toRingHom (fun k => ψ.commutes k) hO
      (fun g hg => (hW _).1 (hgW g hg)) s ?_
    have hyg : evR Xo c f (P j).yg = ((P j).R e).val (evR Xo c f ((P j).y e he)) :=
      (hev _).1 _ ((P j).R e).val _ _ ((P j).gen e he)
    obtain ⟨d, hd'⟩ : κ j ∣ ∏ i, κ i := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have e1 : ((s : (P j).R e) : (P j).Ω) = algebraMap c.F (P j).Ω (algebraMap _ c.F d) *
        (algebraMap c.F (P j).Ω (algebraMap _ c.F (κ j)) * evR Xo c f (P j).yg) := by
      rw [hyg]
      simp only [s, hκ', hd', map_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_val]
      ring
    rw [e1]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨d, rfl⟩)) (hκ j)

end GlobalTheory.CuspBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultipleStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  first | exact @GlobalTheory.CuspBound.exists_bddAll_cusp | exact GlobalTheory.CuspBound.exists_bddAll_cusp | (intros; apply GlobalTheory.CuspBound.exists_bddAll_cusp <;> assumption)
end
