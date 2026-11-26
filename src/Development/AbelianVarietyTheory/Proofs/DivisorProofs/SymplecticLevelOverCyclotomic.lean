module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSymplecticLevelScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CycLift

open Polynomial

theorem exists_injective_hom {n : ℕ} (hn : n ≠ 0) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    {u : V} (hu : IsPrimitiveRoot u n) (hnV : IsUnit (n : V)) :
    ∃ f : cycAway n →+* V, Function.Injective f ∧ f (zetaAway n) = u := by
  have hp := Nat.pos_of_ne_zero hn
  let L := FractionRing V
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  haveI : CharZero L := charZero_of_injective_algebraMap hinj
  have hz : IsPrimitiveRoot (zetaAway n : ℂ) n := Complex.isPrimitiveRoot_exp n hn
  have hi : IsIntegral ℚ (zetaAway n : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway n : ℂ)}
  have hle : cycAway n ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K n)
  have huL : IsPrimitiveRoot (algebraMap V L u) n := hu.map_of_injective hinj
  have hr : algebraMap V L u ∈ (minpoly ℚ (zetaAway n : ℂ)).aroots L := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero n ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact huL.isRoot_cyclotomic hp
  let g : K →ₐ[ℚ] L := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨_, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway n : ℂ)) = algebraMap V L u :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨_, hr⟩
  let f₀ : cycAway n →+* L := g.toRingHom.comp (Subring.inclusion hle)
  have hf₀ : Function.Injective f₀ := g.toRingHom.injective.comp (Subring.inclusion_injective hle)
  have hζ : f₀ (zetaAway n) = algebraMap V L u := hg
  have hmem : ∀ x, f₀ x ∈ (algebraMap V L).range := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨u, hζ.symm⟩
      · refine ⟨↑hnV.unit⁻¹, ?_⟩
        have e : (n : cycAway n) * ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
        have e₁ := congrArg f₀ e
        rw [map_mul, map_natCast, map_one] at e₁
        have e₂ : (n : L) * algebraMap V L ↑hnV.unit⁻¹ = 1 := by
          rw [← map_natCast (algebraMap V L) n, ← map_mul, hnV.mul_val_inv, map_one]
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e₂) (e₂.trans e₁.symm)
    | zero => exact Set.mem_of_eq_of_mem (map_zero f₀) (zero_mem _)
    | one => exact Set.mem_of_eq_of_mem (map_one f₀) (one_mem _)
    | add x y hx hy ihx ihy => exact (map_add f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f₀ ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  let e := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  have he : ∀ y, algebraMap V L (e.symm y) = y := fun y => congrArg Subtype.val (e.apply_symm_apply y)
  refine ⟨e.symm.toRingHom.comp (f₀.codRestrict _ hmem),
    e.symm.injective.comp (fun a b h => hf₀ (congrArg Subtype.val h)), hinj ?_⟩
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he]
  exact hζ

end GlobalTheory.CycLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRoot
open GlobalTheory.SiegelTor

namespace GlobalTheory.CycLift

theorem exists_hom_to_field : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
    ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  intro M hM K _ y hy hMK
  obtain ⟨p, hcp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharZero (WittVector p K) := by
      obtain ⟨q, hq⟩ := CharP.exists (WittVector p K)
      have h1 : ((q : ℕ) : K) = 0 := by
        have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) (CharP.cast_eq_zero (WittVector p K) q)
        rwa [map_natCast, map_zero] at this
      have h2 : p ∣ q := (CharP.cast_eq_zero_iff K p q).1 h1
      rcases CharP.char_is_prime_or_zero (WittVector p K) q with h | h
      · have h3 : p = q := (Nat.prime_dvd_prime_iff_eq hp h).1 h2
        subst h3
        exact absurd (CharP.cast_eq_zero (WittVector p K) p) (WittVector.p_nonzero p K)
      · subst h
        exact CharP.charP_to_charZero _
    let π : WittVector p K →+* K := WittVector.constantCoeff
    have hcc : ∀ x : K, π (WittVector.teichmuller p x) = x := fun x => by simp [π]
    have hu : IsPrimitiveRoot (WittVector.teichmuller p y) M :=
      ⟨by rw [← map_pow, hy.pow_eq_one, map_one], fun l hl => hy.dvd_of_pow_eq_one l (by
        have := congrArg π hl
        rwa [map_pow, hcc, map_one] at this)⟩
    have hnV : IsUnit (M : WittVector p K) := by
      refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
      have : π (M : WittVector p K) ≠ 0 := by rw [map_natCast]; exact hMK.ne_zero
      exact this
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hu hnV
    exact ⟨π.comp f, by rw [RingHom.comp_apply, hfζ, hcc]⟩
  · haveI : CharZero K := CharP.charP_to_charZero K
    obtain ⟨f, -, hfζ⟩ := exists_injective_hom hM hy hMK
    exact ⟨f, hfζ⟩

end GlobalTheory.CycLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRootStatement
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
  ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  first | (exact @GlobalTheory.CycLift.exists_hom_to_field) | (exact GlobalTheory.CycLift.exists_hom_to_field) | (intros; apply GlobalTheory.CycLift.exists_hom_to_field  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeMapModOfPerfectAlternating
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeMapModOfPerfectAlternating
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Module

theorem exists_lattice_map_of_symplecticBasis {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (hB : EF.IsAlt) (b : Basis (Fin g ⊕ Fin g) ℤ La)
    (d : Fin g → ℤ) (hb : IsSymplecticBasisOfType EF b d) (M : ℕ) (u t : Fin g → ℤ)
    (ht : ∀ i, u i * d i = 1 + (M : ℤ) * t i) :
    ∃ L : (Fin g ⊕ Fin g → ℤ) →+ La,
      (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
      ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  classical
  let w : Fin g ⊕ Fin g → ℤ := Sum.elim u 1
  have hw : ∀ j, IsCoprime (w j) (M : ℤ) := by
    rintro (i | i)
    · exact ⟨d i, -t i, by simp only [w, Sum.elim_inl]; linear_combination ht i⟩
    · exact isCoprime_one_left
  let S : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
    { toFun := fun a j => w j * a j
      map_add' := fun a c => by funext j; simp [mul_add]
      map_smul' := fun r a => by funext j; simp; ring }
  let L : (Fin g ⊕ Fin g → ℤ) →+ La := (b.equivFun.symm.toLinearMap ∘ₗ S).toAddMonoidHom
  have hrepr : ∀ v j, b.repr (b.equivFun.symm v) j = v j := fun v j => by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hL : ∀ a j, b.repr (L a) j = w j * a j := fun a j => hrepr (S a) j
  refine ⟨L, fun a => ⟨?_, ?_⟩, fun x => ?_, fun a c => ?_⟩
  · rintro ⟨y, hy⟩
    have hdiv : ∀ j, (M : ℤ) ∣ a j := by
      intro j
      have := hL a j
      rw [hy, map_nsmul] at this
      have h2 : (M : ℤ) ∣ w j * a j := ⟨b.repr y j, by rw [← this]; simp⟩
      exact (hw j).symm.dvd_of_dvd_mul_left h2
    choose c hc using hdiv
    exact ⟨c, funext fun j => by simp [hc j]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨L c, map_nsmul L M c⟩
  · refine ⟨Sum.elim (fun i => d i * b.repr x (Sum.inl i)) (fun i => b.repr x (Sum.inr i)),
      b.equivFun.symm (Sum.elim (fun i => -(t i * b.repr x (Sum.inl i))) 0), ?_⟩
    apply b.repr.injective
    ext j
    rw [map_add (f := _), Finsupp.add_apply, hL, map_nsmul, Finsupp.smul_apply]
    rcases j with i | i
    · simp only [w, Sum.elim_inl, hrepr, nsmul_eq_mul]
      linear_combination (-(b.repr x (Sum.inl i))) * ht i
    · simp [w, hrepr]
  · refine ⟨∑ i, t i * (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)), ?_⟩
    rw [hb.apply_eq_sum hB, omegaStd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hL, w, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_mul]
    linear_combination (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)) * ht i

theorem exists_lattice_map_mod_of_perfect : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  intro La _ _ _ EF halt hinj e M hperf hcop
  have hB : EF.IsAlt := halt
  obtain ⟨g, b, d, hb, -, -⟩ := exists_isSymplecticBasisOfType_pos hB hinj
  have hg : Module.finrank ℤ La / 2 = g := by
    rw [IsSymplecticBasisOfType.finrank_eq b, Fintype.card_fin]; omega
  rw [hg]
  have hde : ∀ i, d i ∣ (e : ℤ) := by
    intro i
    obtain ⟨x, hx⟩ := hperf (b.coord (Sum.inr i))
    have h1 := hb.apply_right x i
    rw [hx] at h1
    simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      nsmul_eq_mul, mul_one] at h1
    exact ⟨b.repr x (Sum.inl i), by rw [h1, mul_comm]⟩
  have hc : ∀ i, IsCoprime (M : ℤ) (d i) := fun i =>
    (Nat.isCoprime_iff_coprime.2 hcop).of_isCoprime_of_dvd_right (hde i)
  choose p u hpu using hc
  exact exists_lattice_map_of_symplecticBasis EF hB b d hb M u (fun i => -p i)
    (fun i => by linear_combination hpu i)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeMapModOfPerfectAlternatingStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_map_mod_of_perfect_alternating : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  first | (exact @GlobalTheory.exists_lattice_map_mod_of_perfect) | (exact GlobalTheory.exists_lattice_map_mod_of_perfect) | (intros; apply GlobalTheory.exists_lattice_map_mod_of_perfect  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylor
noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

theorem exists_sympCond_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ M → Odd M → M.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
    ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (Over.mk x ⟶ o.A)),
      SympCond o (Module.finrank ℤ D.La / 2) M (Over.mk x) t₁ lv := by
  intro p _ D R _ b N M e hM3 hModd hMp hMe hperf S t o K _ _ x
  have hM0 : 0 < M := by omega
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, x ≫ t = spMap β :=
    ⟨(Spec.preimage (x ≫ t)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨I, -⟩ := o.geom K x β hβ
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨L, hLker, hLonto, hLω⟩ := GlobalTheory.T.exists_lattice_map_mod_of_perfect_alternating D.La D.EF D.alt D.nondeg e M hperf hMe
  have hMK : IsUnit (M : K) := by simpa using (b.unit M hMp).map β
  have hprim : IsPrimitiveRoot ((I.ζ M : Kˣ) : K) M :=
    IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim M hM0 hMp)
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot M (by omega) K _ hprim hMK
  refine ⟨spMap β₀, fun a => I.ev M (L a), fun a c => by show I.ev M (L (a + c)) = I.ev M (L a) * I.ev M (L c); rw [map_add (f := _), I.add],
    fun a => (I.onto M hM0 hMp _).2 ⟨L a, rfl⟩, ?_⟩
  intro k _ _ x' β' z hx' hz
  obtain ⟨φ, rfl⟩ : ∃ φ : K →+* k, x' = spMap φ := ⟨(Spec.preimage x').hom, (Spec.map_preimage _).symm⟩
  have hβ' : β' = φ.comp β₀ := by
    have e2 : CommRingCat.ofHom β' = CommRingCat.ofHom (φ.comp β₀) :=
      Spec.map_injective (hx'.symm.trans (by simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]))
    exact congrArg CommRingCat.Hom.hom e2
  subst hβ'
  have hz' : z = Units.map φ.toMonoidHom (I.ζ M) := Units.ext (by simpa [hβ₀] using hz)
  subst hz'
  obtain ⟨β'', hβ''⟩ : ∃ β'' : R →+* k, (spMap φ ≫ x) ≫ t = spMap β'' :=
    ⟨(Spec.preimage ((spMap φ ≫ x) ≫ t)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨I', -⟩ := o.geom k (spMap φ ≫ x) β'' hβ''
  let h : Over.mk (spMap φ ≫ (Over.mk x).hom) ⟶ Over.mk x := Over.homMk (spMap φ) rfl
  have : Epi h.left := GlobalTheory.UPel.GeometricLevelExistence.epi_spMap_field φ
  have : Epi h := Over.epi_of_epi_left h
  change (∀ a, h ≫ I.ev M (L a) = 1 ↔ _) ∧ (∀ g : Over.mk (spMap φ ≫ (Over.mk x).hom) ⟶ o.A, g ^ M = 1 →
      ∃ a, h ≫ I.ev M (L a) = g) ∧ ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M
        (h ≫ I.ev M (L a)) (h ≫ I.ev M (L c)) (unitOn (Units.map φ.toMonoidHom (I.ζ M) ^ (2 * omegaStd a c)))
  have hPa : ∀ a b, h ≫ I.ev M (a + b) = (h ≫ I.ev M a) * (h ≫ I.ev M b) := fun a b => by
    rw [I.add, MonObj.comp_mul]
  have hP : ∀ a, h ≫ I.ev M a = 1 ↔ ∃ b, a = M • b := fun a => by
    rw [← I.ker M hM0 hMp a]
    constructor
    · intro e
      rw [← cancel_epi h, e, MonObj.comp_one]
    · intro e
      rw [e, MonObj.comp_one]
  have hQ : ∀ a, I'.ev M a = 1 ↔ ∃ b, a = M • b := I'.ker M hM0 hMp
  have hPQ : ∀ a, ∃ c, h ≫ I.ev M a = I'.ev M c := fun a => by
    have e : (h ≫ I.ev M a) ^ M = 1 := by
      rw [← MonObj.comp_pow, (I.onto M hM0 hMp (I.ev M a)).2 ⟨a, rfl⟩, MonObj.comp_one]
    obtain ⟨c, hc⟩ := (I'.onto M hM0 hMp _).1 e
    exact ⟨c, hc.symm⟩
  refine ⟨fun a => (hP (L a)).trans (hLker a), fun g hg => ?_, fun a c => ?_⟩
  · obtain ⟨c, rfl⟩ := (I'.onto M hM0 hMp g).1 hg
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.UPel.GeometricLevelExistence.exists_eq_of_count M hM0 _ _ hPa (I'.add M) hP hQ hPQ c
    obtain ⟨a, y, rfl⟩ := hLonto x₀
    refine ⟨a, ?_⟩
    rw [← hx₀, hPa, (hP _).2 ⟨y, rfl⟩, _root_.mul_one]
  · have H := CommPairing.weilIs_pull globalFns_holds o.ab (LB.isLB_pull o.isLB _) h (I.isom M hM0 hMp (L a) (L c))
    have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn (I.ζ M ^ (2 * D.EF (L a) (L c)))) =
        unitOn (Units.map φ.toMonoidHom (I.ζ M) ^ (2 * omegaStd a c)) := by
      obtain ⟨k₀, hk₀⟩ := hLω a c
      have hζM : I.ζ M ^ (M : ℤ) = 1 := by
        rw [zpow_natCast]
        exact (I.ζ_prim M hM0 hMp).pow_eq_one
      have hK : I.ζ M ^ (2 * D.EF (L a) (L c)) = I.ζ M ^ (2 * omegaStd a c) := by
        rw [hk₀, show (2 : ℤ) * (omegaStd a c + M * k₀) = 2 * omegaStd a c + M * (2 * k₀) by ring, zpow_add,
          zpow_mul (I.ζ M) (M : ℤ), hζM, one_zpow, _root_.mul_one]
      rw [hK, ← map_zpow]
      exact GlobalTheory.UPel.GeometricLevelExistence.unitOn_pull_spMap φ _
    rw [e] at H
    exact H

end GlobalTheory.HTSympCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ M → Odd M → M.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
    ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (Over.mk x ⟶ o.A)),
      SympCond o (Module.finrank ℤ D.La / 2) M (Over.mk x) t₁ lv := by
  first | (exact @GlobalTheory.HTSympCover.exists_sympCond_geom) | (exact GlobalTheory.HTSympCover.exists_sympCond_geom) | (intros; apply GlobalTheory.HTSympCover.exists_sympCond_geom  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOnFibreUniqueTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.TensorTorsionNsmul

open scoped TensorProduct

variable {L : Type} [AddCommGroup L]

theorem tmul_surjective (n : ℕ) (x : ZMod n ⊗[ℤ] L) : ∃ a : L, (1 : ZMod n) ⊗ₜ[ℤ] a = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul r a =>
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨m • a, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

theorem eq_nsmul_of_tmul_eq_zero {n : ℕ} {a : L} (h : (1 : ZMod n) ⊗ₜ[ℤ] a = 0) : ∃ d, a = n • d := by
  let e : ZMod n ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    (Int.quotientSpanNatEquivZMod n).symm.toAddEquiv.toIntLinearEquiv
  have he : e 1 = 1 := map_one (Int.quotientSpanNatEquivZMod n).symm
  have h1 := congrArg (fun y => TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(n : ℤ)})
    (LinearMap.rTensor L e.toLinearMap y)) h
  simp only [LinearMap.rTensor_tmul, map_zero, LinearEquiv.coe_coe, he,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨d, -, hd⟩ := h1
  exact ⟨d, by rw [← hd, natCast_zsmul]⟩

theorem tmul_nsmul_eq_zero (n : ℕ) (d : L) : (1 : ZMod n) ⊗ₜ[ℤ] (n • d) = 0 := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, _root_.mul_one, ZMod.natCast_self,
    TensorProduct.zero_tmul]

variable {G : Type} [Group G]

theorem map_nsmul_of_add {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c) (m : ℕ) (a : L) :
    φ (m • a) = φ a ^ m := by
  have h0 : φ 0 = 1 := by
    have := hφ 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction m with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ m ih => rw [succ_nsmul, hφ, ih, pow_succ]

theorem tmul_eq_tmul_iff {n : ℕ} {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b) (a c : L) :
    (1 : ZMod n) ⊗ₜ[ℤ] a = 1 ⊗ₜ c ↔ φ a = φ c := by
  have e : φ a = φ (a - c) * φ c := by rw [← hφ, sub_add_cancel]
  rw [e, mul_eq_right, hk, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  constructor
  · exact eq_nsmul_of_tmul_eq_zero
  · rintro ⟨d, hd⟩
    rw [hd]
    exact tmul_nsmul_eq_zero n d

def matchMap (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) : (ZMod n ⊗[ℤ] L) →ₗ[ZMod n] (ZMod n ⊗[ℤ] L) :=
  LinearMap.liftBaseChange (ZMod n)
    (AddMonoidHom.mk' (fun b => (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b)) (fun b b' => by
      rw [← TensorProduct.tmul_add, tmul_eq_tmul_iff hφ hk, hφ, Classical.choose_spec (hr _),
        Classical.choose_spec (hr _), Classical.choose_spec (hr _), hφ']) : L →+ ZMod n ⊗[ℤ] L).toIntLinearMap

theorem matchMap_tmul (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) (b c : L) :
    matchMap n φ φ' hφ hφ' hk hr ((1 : ZMod n) ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  rw [matchMap, LinearMap.liftBaseChange_tmul, one_smul]
  change (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b) = _ ↔ _
  rw [tmul_eq_tmul_iff hφ hk, Classical.choose_spec (hr b), eq_comm]

theorem exists_equiv (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hk' : ∀ a, φ' a = 1 ↔ ∃ b, a = n • b) (hr : ∀ b, ∃ c, φ c = φ' b) (hr' : ∀ c, ∃ b, φ' b = φ c) :
    ∃ e : (ZMod n ⊗[ℤ] L) ≃ₗ[ZMod n] (ZMod n ⊗[ℤ] L), ∀ b c, e (1 ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  let f := matchMap n φ φ' hφ hφ' hk hr
  let g := matchMap n φ' φ hφ' hφ hk' hr'
  have hfg : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr b
    obtain ⟨d, hd⟩ := hr' c
    rw [(matchMap_tmul n φ φ' hφ hφ' hk hr b c).2 hc, (matchMap_tmul n φ' φ hφ' hφ hk' hr' c d).2 hd,
      tmul_eq_tmul_iff hφ' hk', hd, hc]
  have hgf : ∀ x, f (g x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr' b
    obtain ⟨d, hd⟩ := hr c
    rw [(matchMap_tmul n φ' φ hφ' hφ hk' hr' b c).2 hc, (matchMap_tmul n φ φ' hφ hφ' hk hr c d).2 hd,
      tmul_eq_tmul_iff hφ hk, hd, hc]
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hgf) (LinearMap.ext hfg), fun b c => ?_⟩
  exact matchMap_tmul n φ φ' hφ hφ' hk hr b c

end GlobalTheory.UPel.TensorTorsionNsmul

namespace GlobalTheory.UPel

open scoped TensorProduct

end GlobalTheory.UPel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

open scoped TensorProduct

theorem piScalarRight_tmul_one {h M : ℕ} (a : Fin h ⊕ Fin h → ℤ) :
    TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h) ((1 : ZMod M) ⊗ₜ[ℤ] a) = reduceMod M a := by
  funext i
  simp [TensorProduct.piScalarRight_apply, reduceMod]

theorem omegaMod_reduceMod {h M : ℕ} (a c : Fin h ⊕ Fin h → ℤ) :
    omegaMod M (reduceMod M a) (reduceMod M c) = ((omegaStd a c : ℤ) : ZMod M) := by
  simp [omegaMod, omegaStd, reduceMod]

theorem sp_exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp B ⟶ Sp A) : ∃ f : A →+* B, g = spMap f :=
  ⟨(Spec.preimage g).hom, by simp [spMap]⟩

theorem sympCond_fibre_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  intro p _ D R _ b N h M hM hodd hh σ hσ S t o K _ _ x t₁ t₁' lv lv' H H'
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, -, hgeo⟩ := H
  obtain ⟨hadd', -, hgeo'⟩ := H'
  obtain ⟨β, hβ⟩ := sp_exists_spMap t₁
  obtain ⟨β', hβ'⟩ := sp_exists_spMap t₁'
  have hζ : ∀ g₀ : cycAway M →+* K, g₀ (zetaAway M) ^ M = 1 := fun g₀ => by
    rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
  let z : Kˣ := Units.ofPowEqOne _ M (hζ β) hM.ne'
  let z' : Kˣ := Units.ofPowEqOne _ M (hζ β') hM.ne'
  obtain ⟨hk, hon, hW⟩ := hgeo K (𝟙 _) β z (by rw [Category.id_comp, hβ]) rfl
  obtain ⟨hk', hon', hW'⟩ := hgeo' K (𝟙 _) β' z' (by rw [Category.id_comp, hβ']) rfl
  let jx : Over.mk (𝟙 (Sp K) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 _) rfl
  have canc : ∀ f g : Over.mk x ⟶ o.A, jx ≫ f = jx ≫ g → f = g := by
    intro f g e
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left e
    simpa [jx] using this
  let φ : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv a
  let φ' : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv' a
  have hφ : ∀ a c, φ (a + c) = φ a * φ c := fun a c => by simp only [φ, hadd, MonObj.comp_mul]
  have hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c := fun a c => by simp only [φ', hadd', MonObj.comp_mul]
  have hkφ : ∀ a, φ a = 1 ↔ ∃ c, a = M • c := fun a => hk a
  have hkφ' : ∀ a, φ' a = 1 ↔ ∃ c, a = M • c := fun a => hk' a
  have hr : ∀ b, ∃ c, φ c = φ' b := fun b => hon (φ' b) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ', (hkφ' _).2 ⟨b, rfl⟩])
  have hr' : ∀ c, ∃ b, φ' b = φ c := fun c => hon' (φ c) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ, (hkφ _).2 ⟨c, rfl⟩])
  obtain ⟨e, he⟩ := GlobalTheory.UPel.TensorTorsionNsmul.exists_equiv M φ φ' hφ hφ' hkφ hkφ' hr hr'
  let E := TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h)
  let e' := E.symm.trans (e.trans E)
  have he' : ∀ b c, e' (reduceMod M b) = reduceMod M c ↔ φ c = φ' b := by
    intro b c
    rw [← he, ← piScalarRight_tmul_one, ← piScalarRight_tmul_one]
    show E (e (E.symm (E _))) = E _ ↔ _
    rw [LinearEquiv.symm_apply_apply, E.injective.eq_iff]
  have hz : IsPrimitiveRoot z M := IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hM.ne' β)
  obtain ⟨i, hcop, he_i⟩ := exists_pow_of_isLocalRing hM.ne' β β'
  have hzi : z ^ i = z' := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact he_i.symm)
  have h2u : IsUnit (2 : ZMod M) := by
    have := (ZMod.isUnit_iff_coprime 2 M).2 (Nat.coprime_two_left.2 hodd)
    exact_mod_cast this
  have hval : ∀ a b c d, φ c = φ' a → φ d = φ' b →
      ((omegaStd c d : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) := by
    intro a b c d hc hd
    have w₁ := hW c d
    have w₂ := hW' a b
    change Out.WeilIs _ _ _ (φ' a) (φ' b) _ at w₂
    change Out.WeilIs _ _ _ (φ c) (φ d) _ at w₁
    rw [← hc, ← hd] at w₂
    have e₁ := H1.unitOn_injective
      (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) w₂ w₁)
    rw [← hzi, ← zpow_natCast, ← zpow_mul] at e₁
    have h2 : z ^ ((i : ℤ) * (2 * omegaStd a b) - 2 * omegaStd c d) = 1 := by
      rw [zpow_sub, e₁, mul_inv_cancel]
    rw [hz.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : (2 : ZMod M) * ((i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) - ((omegaStd c d : ℤ) : ZMod M)) = 0 := by
      linear_combination h2
    have h4 := h2u.mul_right_eq_zero.1 h3
    linear_combination -h4
  have hmul : ∀ X Y, omegaMod M (e' X) (e' Y) = (i : ZMod M) * omegaMod M X Y := by
    intro X Y
    obtain ⟨a, rfl⟩ : ∃ a, reduceMod M a = X := ⟨liftMod X, reduceMod_liftMod X⟩
    obtain ⟨b, rfl⟩ : ∃ b, reduceMod M b = Y := ⟨liftMod Y, reduceMod_liftMod Y⟩
    obtain ⟨c, hc⟩ := hr a
    obtain ⟨d, hd⟩ := hr b
    rw [(he' a c).2 hc, (he' b d).2 hd, omegaMod_reduceMod, omegaMod_reduceMod]
    exact hval a b c d hc hd
  have hsim : e' ∈ sympSimGrp h M :=
    ⟨ZMod.unitOfCoprime i hcop, fun X Y => by rw [ZMod.coe_unitOfCoprime]; exact hmul X Y⟩
  let a₀ : sympSimGrp h M := ⟨e', hsim⟩
  have hmul₀ : IsMultOf a₀ i := hmul
  refine ⟨a₀, ⟨?_, fun c => canc _ _ ?_⟩, ?_⟩
  · obtain ⟨n, hn, hσn⟩ := hσ a₀
    have hni : (n : ZMod M) = i := isMultOf_unique hh hn hmul₀
    have hc : β.comp (σ a₀) = β' := cycAway_hom_ext hM.ne' (by
      rw [RingHom.comp_apply, hσn, zetaAway_pow_eq M hM.ne' hni, map_pow, he_i])
    rw [hβ, hβ', spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  · change φ (liftMod (e' (reduceMod M c))) = φ' c
    exact (he' c _).1 (reduceMod_liftMod _).symm
  · rintro a ⟨-, ha⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    obtain ⟨b', rfl⟩ : ∃ b', reduceMod M b' = X := ⟨liftMod X, reduceMod_liftMod X⟩
    have h1 : φ (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))) = φ' b' :=
      congrArg (jx ≫ ·) (ha b')
    rw [← reduceMod_liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))]
    exact ((he' b' _).2 h1).symm

end GlobalTheory.HTSympCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_similitude_between_symplecticLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  first | exact @GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | exact GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | (intros; apply GlobalTheory.HTSympCover.sympCond_fibre_existsUnique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitude
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitude
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem reduceMod_eq_zero_iff {h : ℕ} (M : ℕ) (u : Fin h ⊕ Fin h → ℤ) :
    reduceMod M u = 0 ↔ ∃ c, u = M • c := by
  constructor
  · intro hu
    refine ⟨fun i => u i / M, ?_⟩
    funext i
    have hi : ((u i : ℤ) : ZMod M) = 0 := congrFun hu i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hi
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact (Int.mul_ediv_cancel' hi).symm
  · rintro ⟨c, rfl⟩
    funext i
    simp [reduceMod]

theorem omegaStd_cast {h : ℕ} (M : ℕ) (u v : Fin h ⊕ Fin h → ℤ) :
    ((omegaStd u v : ℤ) : ZMod M) = omegaMod M (reduceMod M u) (reduceMod M v) := by
  simp [omegaStd, omegaMod, reduceMod]

theorem sympCond_twist : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  intro p _ D R _ b N h M hM S t o T t₁ lv hlv a n σ hn hσ
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, htor, hgeo⟩ := hlv

  let φ : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (T ⟶ o.A) :=
    MonoidHom.mk' (fun u => lv (Multiplicative.toAdd u)) (fun u v => hadd _ _)
  have hsm : ∀ (k : ℕ) (w : Fin h ⊕ Fin h → ℤ), lv (k • w) = lv w ^ k := by
    intro k w
    have := map_pow φ (Multiplicative.ofAdd w) k
    simpa [φ, ← ofAdd_nsmul] using this
  have per : ∀ {u v : Fin h ⊕ Fin h → ℤ}, reduceMod M u = reduceMod M v → lv u = lv v := by
    intro u v huv
    have h0 : reduceMod M (u - v) = 0 := by
      funext i
      have := congrFun huv i
      simp only [reduceMod, Pi.sub_apply, Pi.zero_apply, Int.cast_sub] at this ⊢
      rw [this, sub_self]
    obtain ⟨w, hw⟩ := (reduceMod_eq_zero_iff M _).1 h0
    have : u = v + M • w := by rw [← hw]; abel
    rw [this, hadd, hsm, htor, _root_.mul_one]
  let g := (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
  have tw : ∀ u, sympTwist a lv u = lv (liftMod (g (reduceMod M u))) := fun u => rfl
  have redAdd : ∀ u v : Fin h ⊕ Fin h → ℤ, reduceMod M (u + v) = reduceMod M u + reduceMod M v := by
    intro u v; funext i; simp [reduceMod]
  refine ⟨fun u c => ?_, fun u => ?_, fun k _ _ x β' z' hx' hz' => ?_⟩
  · rw [tw, tw, tw, ← hadd]
    apply per
    rw [reduceMod_liftMod, redAdd, redAdd, reduceMod_liftMod, reduceMod_liftMod, map_add (f := _)]
  · rw [tw]; exact htor _
  ·
    set β : cycAway M →+* k := (Spec.preimage (x ≫ t₁)).hom with hβdef
    have hβ : x ≫ t₁ = spMap β := by
      simp only [spMap, hβdef, CommRingCat.ofHom_hom, Spec.map_preimage]
    have hβ' : β' = β.comp σ := by
      have e : spMap β' = spMap (β.comp σ) := by
        rw [spMap_comp, ← hx', ← hβ, Category.assoc]
      have := Spec.map_injective e
      exact congrArg CommRingCat.Hom.hom this
    have hζM : β (zetaAway M) ^ M = 1 := by
      rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
    have hne : β (zetaAway M) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM.ne'] at hζM
      exact zero_ne_one hζM
    set z : kˣ := Units.mk0 (β (zetaAway M)) hne with hzdef
    have hz : (z : k) = β (zetaAway M) := rfl
    have hzz : z' = z ^ n := by
      ext
      rw [hz', hβ', RingHom.comp_apply, hσ, map_pow, Units.val_pow_eq_pow_val, hz]
    have hzM : z ^ (M : ℤ) = 1 := by
      rw [zpow_natCast]; ext; rw [Units.val_pow_eq_pow_val, hz, hζM]; rfl
    obtain ⟨hK, hS, hW⟩ := hgeo k x β z hβ hz
    refine ⟨fun u => ?_, fun g' hg' => ?_, fun u c => ?_⟩
    · rw [tw, hK]
      constructor
      · rintro ⟨c, hc⟩
        apply (reduceMod_eq_zero_iff M u).1
        have : g (reduceMod M u) = 0 := by
          rw [← reduceMod_liftMod (g (reduceMod M u)), hc]
          exact (reduceMod_eq_zero_iff M _).2 ⟨c, rfl⟩
        exact (LinearEquiv.map_eq_zero_iff _).1 this
      · intro hu
        apply (reduceMod_eq_zero_iff M _).1
        rw [reduceMod_liftMod, (reduceMod_eq_zero_iff M u).2 hu, map_zero]
    · obtain ⟨u₀, hu₀⟩ := hS g' hg'
      refine ⟨liftMod (g.symm (reduceMod M u₀)), ?_⟩
      rw [tw, reduceMod_liftMod, LinearEquiv.apply_symm_apply, per (reduceMod_liftMod _)]
      exact hu₀
    · rw [tw, tw]
      set u' := liftMod (g (reduceMod M u))
      set c' := liftMod (g (reduceMod M c))
      have hcast : ((2 * omegaStd u' c' : ℤ) : ZMod M) = (((n : ℤ) * (2 * omegaStd u c) : ℤ) : ZMod M) := by
        push_cast
        rw [omegaStd_cast, omegaStd_cast, reduceMod_liftMod, reduceMod_liftMod]
        rw [show omegaMod M (g (reduceMod M u)) (g (reduceMod M c)) = n * omegaMod M (reduceMod M u) (reduceMod M c)
          from hn _ _]
        ring
      have e : z' ^ (2 * omegaStd u c) = z ^ (2 * omegaStd u' c') := by
        rw [hzz, ← zpow_natCast z, ← zpow_mul, zpow_eq_zpow_emod _ hzM, zpow_eq_zpow_emod (2 * omegaStd u' c') hzM]
        congr 1
        exact ((ZMod.intCast_eq_intCast_iff' _ _ _).1 hcast).symm
      rw [e]
      exact hW u' c'

end GlobalTheory.HTSympCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitudeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticLevel_twist_by_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  first | exact @GlobalTheory.HTSympCover.sympCond_twist | exact GlobalTheory.HTSympCover.sympCond_twist | (intros; apply GlobalTheory.HTSympCover.sympCond_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomic
noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem exists_galoisCover_of_geom {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] (b : Base D R)
    (N h M : ℕ) (h1 : 1 ≤ h) (hM0 : 0 < M) (hodd : Odd M) (hMp : M.Coprime p)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)) (huniv : HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev)
    (ρ : sympSimGrp h M → (X ⟶ X)) (hρ : SympActs s s₁ u lev ρ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t)
    (geo : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)), SympCond o h M (Over.mk x) t₁ lv) :
    ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp h M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X) (o' : Obj b N (π₁ ≫ t)),
      GlobalTheory.ZM.IsGaloisCover (sympSimGrp h M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
      y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨Y, t₁, lu, hYf, hYe, hY⟩ := GlobalTheory.T.exists_finiteEtale_symplecticLevel_scheme p D R b N h M hM0 hMp S t o
  have hAu : SympCond o h M Y t₁ lu := (hY Y t₁ lu).2 ⟨𝟙 Y, by simp, fun a => Category.id_comp _⟩
  have uniqY : ∀ {T : Over S} (f g : T ⟶ Y), f.left ≫ t₁ = g.left ≫ t₁ → (∀ c, f ≫ lu c = g ≫ lu c) → f = g :=
    fun {T} f g e1 e2 => ((hY T (g.left ≫ t₁) (fun c => g ≫ lu c)).1 ((hY T _ _).2 ⟨g, rfl, fun _ => rfl⟩)).unique
      ⟨e1, e2⟩ ⟨rfl, fun _ => rfl⟩
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y.left t Y.hom o
  have hlift : ∀ c, ∃ g : 𝟙_ (Over Y.left) ⟶ o'.A, g.left ≫ m.φ = (lu c).left := fun c => by
    have w : (lu c).left ≫ o.A.hom = 𝟙 Y.left ≫ Y.hom := by rw [Over.w (lu c), Category.id_comp]
    exact ⟨Over.homMk (m.cart.1.lift (lu c).left (𝟙 Y.left) w) (m.cart.1.lift_snd _ _ _),
      m.cart.1.lift_fst _ _ _⟩
  choose lv' hlv' using hlift
  choose n σ hn hσζ hσs using fun a => (hρ a).2.1
  have hTw : ∀ a, SympCond o h M Y (t₁ ≫ spMap (σ a)) (sympTwist a lu) := fun a =>
    GlobalTheory.T.symplecticLevel_twist_by_similitude p D R b N h M hM0 S t o Y t₁ lu hAu a (n a) (σ a) (hn a) (hσζ a)
  choose r hr using fun a => ((hY Y _ _).1 (hTw a)).exists
  have hlev' : IsSympLev o'.P h M (zetaAway M) t₁ lv' := GlobalTheory.T.isSymplecticLevel_of_pulledBack_object p D R b N h M S t o Y t₁ o' m lv' lu hlv' hAu
  have hlevT : ∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv') := fun a =>
    GlobalTheory.T.isSymplecticLevel_of_pulledBack_object p D R b N h M S t o Y (t₁ ≫ spMap (σ a)) o' m (sympTwist a lv') (sympTwist a lu) (fun c => hlv' _) (hTw a)
  obtain ⟨y, ⟨hys, hys₁, my, hmy⟩, -⟩ := huniv Y.left (Y.hom ≫ t) t₁ o' lv' hlev'
  have hdet := (GlobalTheory.SiegelTor.cycAway_galois M (by omega)).2.1
  have hσ1 : σ 1 = RingHom.id _ := hdet _ (σ 1) (RingHom.id _) (by
    rw [hσζ, RingHom.id_apply]
    conv_rhs => rw [← pow_one (zetaAway M)]
    apply zetaAway_pow_eq M (by omega)
    have hm1 : IsMultOf (1 : sympSimGrp h M) 1 := fun x y => by simp
    exact_mod_cast isMultOf_unique h1 (hn 1) hm1)
  have hσmul : ∀ a c, (σ a).comp (σ c) = σ (a * c) := fun a c => hdet _ _ _ (by
    rw [RingHom.comp_apply, hσζ, map_pow, hσζ, hσζ, ← pow_mul]
    apply zetaAway_pow_eq M (by omega)
    have hm : IsMultOf (a * c) (n a * n c) := fun x y => by
      show omegaMod M ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) x))
        ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) y)) = _
      rw [hn a, hn c]
      push_cast
      ring
    exact isMultOf_unique h1 hm (hn (a * c)))
  have hsm : ∀ (k : ℕ) w, lu (k • w) = lu w ^ k := by
    have h0 : lu 0 = 1 := by
      have e0 := hAu.1 0 0
      rw [add_zero] at e0
      exact (by simpa using congrArg (· * (lu 0)⁻¹) e0 : (1 : Y ⟶ o.A) = lu 0).symm
    intro k w
    induction k with
    | zero => rw [zero_smul, h0, pow_zero]
    | succ k ih => rw [succ_nsmul, hAu.1, ih, pow_succ]
  have hper : ∀ c, lu (liftMod (reduceMod M c)) = lu c := by
    intro c
    have hw : liftMod (reduceMod M c) = c + M • (fun i => -(c i / M)) := by
      funext i
      simp only [liftMod, reduceMod, ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply]
      rw [Int.emod_def]
      ring
    rw [hw, hAu.1, hsm, hAu.2.1, _root_.mul_one]
  have hsp1 : spMap (RingHom.id (cycAway M)) = 𝟙 _ := Spec.map_id _
  have hr1 : r 1 = 𝟙 Y := uniqY _ _ (by rw [(hr 1).1, hσ1, hsp1]; simp) (fun c => by
    rw [(hr 1).2, Category.id_comp]
    exact hper c)
  have hrmul : ∀ a c, r (a * c) = r a ≫ r c := fun a c => uniqY _ _ (by
      rw [(hr _).1, Over.comp_left, Category.assoc, (hr c).1, ← Category.assoc, (hr a).1, Category.assoc,
        ← spMap_comp, hσmul])
    (fun d => by
      rw [(hr _).2, Category.assoc, (hr c).2]
      change sympTwist (a * c) lu d = r a ≫ lu (liftMod
        ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M d)))
      rw [(hr a).2]
      change lu (liftMod (((a * c : sympSimGrp h M) : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M d))) = lu (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
          (reduceMod M (liftMod ((c : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M))
            (reduceMod M d))))))
      rw [reduceMod_liftMod]
      rfl)
  refine ⟨Y.left, Y.hom, fun a => (r a).left, y, o', ⟨sympSimGrp_finite h M, ?_, ?_, ?_, hYf, hYe, ?_, ?_⟩,
    ?_, hys, ⟨m⟩, ⟨my⟩⟩
  · show (r 1).left = _
    rw [hr1]
    rfl
  · intro a c
    show (r (a * c)).left = _
    rw [hrmul]
    rfl
  · intro a
    exact Over.w (r a)
  · refine ⟨fun pt => ?_⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨t₀, lv, hlv⟩ := geo k x
    obtain ⟨f, -, -⟩ := (hY (Over.mk x) t₀ lv).1 hlv
    obtain ⟨q, hq⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨f.left q, by rw [← Scheme.Hom.comp_apply, Over.w f]; exact hq⟩
  · intro K _ _ y₁ y₂ h12
    let P1 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₁ rfl
    let P2 : Over.mk (y₁ ≫ Y.hom) ⟶ Y := Over.homMk y₂ h12.symm
    have c1 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₁ ≫ t₁) (fun c => P1 ≫ lu c) :=
      (hY _ _ _).2 ⟨P1, rfl, fun _ => rfl⟩
    have c2 : SympCond o h M (Over.mk (y₁ ≫ Y.hom)) (y₂ ≫ t₁) (fun c => P2 ≫ lu c) :=
      (hY _ _ _).2 ⟨P2, rfl, fun _ => rfl⟩
    obtain ⟨a, ⟨ha1, ha2⟩, hu⟩ := GlobalTheory.T.existsUnique_similitude_between_symplecticLevels p D R b N h M hM0 hodd h1 σ (fun a => ⟨n a, hn a, hσζ a⟩) S t o K
      (y₁ ≫ Y.hom) _ _ _ _ c1 c2
    refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
    · have : P1 ≫ r a = P2 := uniqY _ _ (by
          show y₁ ≫ (r a).left ≫ t₁ = y₂ ≫ t₁
          rw [(hr a).1, ← Category.assoc]
          exact ha1)
        (fun c => by rw [Category.assoc, (hr a).2]; exact ha2 c)
      exact congrArg (fun q => q.left) this
    · have e' : P1 ≫ r a' = P2 := Over.OverMorphism.ext ha'
      refine ⟨?_, fun c => ?_⟩
      · rw [Category.assoc, ← (hr a').1, ← Category.assoc]
        exact congrArg (· ≫ t₁) ha'
      · show P1 ≫ lu _ = P2 ≫ lu c
        rw [← e', Category.assoc, (hr a').2]
        rfl
  · exact fun a => GlobalTheory.T.classifyingMap_symplecticLevel_equivariant p D R b N h M X s s₁ u lev huniv ρ hρ σ hσs S t o Y t₁ lu o' m lv' hlv' hlevT y my hmy
      hys hys₁ r (fun a => (hr a).1) (fun a => (hr a).2) a

theorem exists_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
  (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  intro p _ D R _ b N M e _ _ hM hodd hMp _ hMe hperf X s s₁ u lev _ huniv ρ hρ S t o
  have h1 : 1 ≤ Module.finrank ℤ D.La / 2 := by have := D.two_le_finrank_La; omega
  exact exists_galoisCover_of_geom b N _ M h1 (by omega) hodd hMp X s s₁ u lev huniv ρ hρ S t o
    (fun K _ _ x => GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor p D R b N M e hM hodd hMp hMe hperf S t o K x)

end GlobalTheory.HTSympCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelOverCyclotomicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_level_over_cyclotomic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e →
  (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P (Module.finrank ℤ D.La / 2) M (zetaAway M) s₁ lev →
    HarrisTaylorSymplecticLevelFamilyUniversalProperty b N (Module.finrank ℤ D.La / 2) M s s₁ u lev →
    ∀ ρ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
      ∃ (S₁ : Scheme.{0}) (π₁ : S₁ ⟶ S) (ρ₁ : sympSimGrp (Module.finrank ℤ D.La / 2) M → (S₁ ⟶ S₁)) (y : S₁ ⟶ X)
        (o' : Obj b N (π₁ ≫ t)),
        GlobalTheory.ZM.IsGaloisCover (sympSimGrp (Module.finrank ℤ D.La / 2) M) ρ₁ π₁ ∧ (∀ a, ρ₁ a ≫ y = y ≫ ρ a) ∧
        y ≫ s = π₁ ≫ t ∧ Nonempty (ObjMap o' o π₁) ∧ Nonempty (ObjMap o' u y) := by
  first | (exact @GlobalTheory.HTSympCover.exists_galoisCover) | (exact GlobalTheory.HTSympCover.exists_galoisCover) | (intros; apply GlobalTheory.HTSympCover.exists_galoisCover <;> assumption)
end
