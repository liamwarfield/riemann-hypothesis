module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingConditionLocusIsClopen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.CycAwayCover

theorem isUnit_natCast_cycAway {M : ℕ} (hM : M ≠ 0) : IsUnit (M : cycAway M) := by
  refine isUnit_iff_exists_inv.2 ⟨⟨(M : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩, ?_⟩
  exact Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))

def awayToCyc (M : ℕ) (hM : M ≠ 0) : Localization.Away (M : ℤ) →+* cycAway M :=
  IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) (g := Int.castRingHom (cycAway M))
    (by simpa using isUnit_natCast_cycAway hM)

theorem awayToCyc_injective {M : ℕ} (hM : M ≠ 0) : Function.Injective (awayToCyc M hM) := by
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  rw [awayToCyc, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.Away (M : ℤ)) hle).eq_iff,
    (Int.castRingHom (cycAway M)).injective_int.eq_iff]

theorem finite_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Finite := by
  letI := (awayToCyc M hM).toAlgebra
  have hv : ∀ hx, (⟨(M : ℂ)⁻¹, hx⟩ : cycAway M) =
      algebraMap (Localization.Away (M : ℤ)) (cycAway M) (IsLocalization.Away.invSelf (M : ℤ)) := by
    intro hx
    have h1 : (M : cycAway M) * ⟨(M : ℂ)⁻¹, hx⟩ = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))
    have h2 : (M : cycAway M) * algebraMap (Localization.Away (M : ℤ)) (cycAway M)
        (IsLocalization.Away.invSelf (M : ℤ)) = 1 := by
      have := congrArg (algebraMap (Localization.Away (M : ℤ)) (cycAway M))
        (IsLocalization.Away.mul_invSelf (S := Localization.Away (M : ℤ)) (M : ℤ))
      simpa using this
    exact (isUnit_natCast_cycAway hM).mul_left_cancel (h1.trans h2.symm)
  have hint : Algebra.IsIntegral (Localization.Away (M : ℤ)) (cycAway M) := by
    constructor
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hM, by
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
          exact sub_eq_zero.2 (GlobalTheory.SiegelTor.zetaAway_pow_self hM)⟩
      · convert (isIntegral_algebraMap (R := Localization.Away (M : ℤ)) (x := IsLocalization.Away.invSelf (M : ℤ)) : IsIntegral _ (algebraMap (Localization.Away (M : ℤ)) (cycAway M) _)) using 1
        exact hv _
    | zero => exact isIntegral_zero
    | one => exact isIntegral_one
    | add x y _ _ hx hy => exact hx.add hy
    | neg x _ hx => exact hx.neg
    | mul x y _ _ hx hy => exact hx.mul hy
  haveI : Algebra.FiniteType (Localization.Away (M : ℤ)) (cycAway M) := by
    refine ⟨⟨{zetaAway M}, eq_top_iff.2 ?_⟩⟩
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self _))
      · convert Subalgebra.algebraMap_mem (Algebra.adjoin (Localization.Away (M : ℤ)) ((({zetaAway M} : Finset (cycAway M)) : Set (cycAway M)))) (IsLocalization.Away.invSelf (M : ℤ)) using 1
        exact hv _
    | zero => exact Subalgebra.zero_mem _
    | one => exact Subalgebra.one_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | neg x _ hx => exact Subalgebra.neg_mem _ hx
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  exact (Algebra.IsIntegral.finite : Module.Finite (Localization.Away (M : ℤ)) (cycAway M))

theorem etale_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Etale := by
  letI := (awayToCyc M hM).toAlgebra
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  haveI : IsDomain (Localization.Away (M : ℤ)) := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain (Localization.Away (M : ℤ)) :=
    IsLocalization.isDedekindDomain ℤ hle (Localization.Away (M : ℤ))
  haveI : Module.Finite (Localization.Away (M : ℤ)) (cycAway M) := finite_awayToCyc hM
  haveI : FaithfulSMul (Localization.Away (M : ℤ)) (cycAway M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (awayToCyc_injective hM)
  haveI : Module.Flat (Localization.Away (M : ℤ)) (cycAway M) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (M : ℤ)) (cycAway M) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI := formallyUnramified_cycAway hM (Localization.Away (M : ℤ))
  exact (Algebra.Etale.of_formallyUnramified_of_flat : Algebra.Etale (Localization.Away (M : ℤ)) (cycAway M))

theorem exists_cycAway_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  intro M S hM hS
  have hM0 : M ≠ 0 := hM.ne'
  have hSu : IsUnit ((Int.castRingHom Γ(S, ⊤)) (M : ℤ)) := by simpa using hS
  let φ : S ⟶ Sp (Localization.Away (M : ℤ)) :=
    S.toSpecΓ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) hSu)
  let S' : Over S := Over.mk (pullback.fst φ (spMap (awayToCyc M hM0)))
  haveI : IsFinite (spMap (awayToCyc M hM0)) := (IsFinite.SpecMap_iff _).2 (finite_awayToCyc hM0)
  haveI : Etale (spMap (awayToCyc M hM0)) := HasRingHomProperty.Spec_iff.2 (etale_awayToCyc hM0)
  refine ⟨S', pullback.snd φ (spMap (awayToCyc M hM0)), ?_, ?_, ?_⟩
  · exact (inferInstance : IsFinite (pullback.fst φ (spMap (awayToCyc M hM0))))
  · exact (inferInstance : Etale (pullback.fst φ (spMap (awayToCyc M hM0))))
  · intro T f t₁
    haveI : IsOpenImmersion (spMap (algebraMap ℤ (Localization.Away (M : ℤ)))) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (M : ℤ))))))
    have e : f ≫ φ = t₁ ≫ spMap (awayToCyc M hM0) :=
      (cancel_mono (spMap (algebraMap ℤ (Localization.Away (M : ℤ))))).1 (specZIsTerminal.hom_ext _ _)
    refine ⟨pullback.lift f t₁ e, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
    rintro g ⟨h1, h2⟩
    exact pullback.hom_ext (h1.trans (pullback.lift_fst _ _ e).symm) (h2.trans (pullback.lift_snd _ _ e).symm)

end GlobalTheory.CycAwayCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  first | (exact @GlobalTheory.CycAwayCover.exists_cycAway_cover) | (exact GlobalTheory.CycAwayCover.exists_cycAway_cover) | (intros; apply GlobalTheory.CycAwayCover.exists_cycAway_cover  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.TorsCount

variable {κ Q : Type} [Fintype κ] [Group Q]

theorem map_zero_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c) :
    e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem map_sub_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (a c : L) : e (a - c) = e a * (e c)⁻¹ := by
  have h := hadd (a - c) c
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

def red (M : ℕ) (e : (κ → ℤ) → Q) (hpow : ∀ a, e a ^ M = 1) : (κ → ZMod M) → {g : Q // g ^ M = 1} :=
  fun c => ⟨e fun i => ((c i).val : ℤ), hpow _⟩

theorem exists_red (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) (a : κ → ℤ) :
    ∃ c : κ → ZMod M, e (fun i => ((c i).val : ℤ)) = e a := by
  refine ⟨fun i => (a i : ZMod M), ?_⟩
  have h : e (a - fun i => (((a i : ZMod M)).val : ℤ)) = 1 := by
    refine (hker _).2 ⟨fun i => a i / (M : ℤ), funext fun i => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.val_intCast]
    have := Int.emod_add_mul_ediv (a i) (M : ℤ)
    linarith
  rw [map_sub_of_add e hadd, mul_inv_eq_one] at h
  exact h.symm

theorem red_injective (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) : Function.Injective (red M e hpow) := by
  intro c c' hcc
  have h1 : e (fun i => ((c i).val : ℤ)) = e (fun i => ((c' i).val : ℤ)) := congrArg Subtype.val hcc
  have h2 : e ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) = 1 := by
    rw [map_sub_of_add e hadd, h1, mul_inv_cancel]
  obtain ⟨d, hd⟩ := (hker _).1 h2
  funext i
  have h3 := congrArg (fun x : κ → ℤ => ((x i : ℤ) : ZMod M)) hd
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    Int.cast_mul, ZMod.natCast_self, zero_mul] at h3
  exact sub_eq_zero.1 h3

theorem card_tors (M : ℕ) (hM : 0 < M) (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c)
    (hon : ∀ g : Q, g ^ M = 1 → ∃ a, e a = g) : Nat.card {g : Q // g ^ M = 1} = M ^ Fintype.card κ := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  have hb : Function.Bijective (red M e hpow) := by
    refine ⟨red_injective M e hadd hpow hker, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := hon g hg
    obtain ⟨c, hc⟩ := exists_red M e hadd hker a
    exact ⟨c, Subtype.ext hc⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

end GlobalTheory.TorsCount

namespace GlobalTheory.HTSympCover

theorem onto_tors_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  intro p _ D R _ b N h M hM hcop S t o k _ _ y e hadd hpow hker
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (y ≫ t)
  obtain ⟨I, -⟩ := o.geom k y β hβ
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  let ev' : (Module.Free.ChooseBasisIndex ℤ D.La → ℤ) → (Over.mk y ⟶ o.A) := fun a => I.ev M (B.equivFun.symm a)
  have hadd' : ∀ a c, ev' (a + c) = ev' a * ev' c := fun a c => by
    simp only [ev', map_add (f := _)]
    exact I.add M _ _
  have hpow' : ∀ a, ev' a ^ M = 1 := fun a => (I.onto M hM hcop _).2 ⟨_, rfl⟩
  have hker' : ∀ a, ev' a = 1 ↔ ∃ c, a = M • c := fun a => by
    simp only [ev']
    rw [I.ker M hM hcop]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨B.equivFun c, by rw [← map_nsmul, ← hc, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨B.equivFun.symm c, map_nsmul _ _ _⟩
  have hon' : ∀ g, g ^ M = 1 → ∃ a, ev' a = g := fun g hg => by
    obtain ⟨x, hx⟩ := (I.onto M hM hcop g).1 hg
    exact ⟨B.equivFun x, by simp only [ev', LinearEquiv.symm_apply_apply, hx]⟩
  have hcard := GlobalTheory.TorsCount.card_tors M hM ev' hadd' hpow' hker' hon'
  rw [← Module.finrank_eq_card_chooseBasisIndex] at hcard
  have hinj := GlobalTheory.TorsCount.red_injective M e hadd hpow hker
  have hdom : Nat.card (Fin h ⊕ Fin h → ZMod M) = M ^ (2 * h) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin, two_mul]
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have h1 : M = 1 := by omega
    subst h1
    simp only [true_or, iff_true]
    intro g hg
    rw [pow_one] at hg
    exact ⟨0, by rw [hg]; exact GlobalTheory.TorsCount.map_zero_of_add e hadd⟩
  · have hMne : M ≠ 1 := by omega
    simp only [hMne, false_or]
    haveI : Finite {g : Over.mk y ⟶ o.A // g ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    constructor
    · intro hon
      have hb : Function.Bijective (GlobalTheory.TorsCount.red M e hpow) := by
        refine ⟨hinj, fun ⟨g, hg⟩ => ?_⟩
        obtain ⟨a, rfl⟩ := hon g hg
        obtain ⟨c, hc⟩ := GlobalTheory.TorsCount.exists_red M e hadd hker a
        exact ⟨c, Subtype.ext hc⟩
      have h2 := Nat.card_eq_of_bijective _ hb
      rw [hcard, hdom] at h2
      exact Nat.pow_right_injective hM2 h2
    · intro hr g hg
      have hs : Function.Surjective (GlobalTheory.TorsCount.red M e hpow) :=
        (hinj.bijective_of_nat_card_le (by rw [hcard, hdom, hr])).2
      obtain ⟨c, hc⟩ := hs ⟨g, hg⟩
      exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.HTSympCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  first | (exact @GlobalTheory.HTSympCover.onto_tors_iff) | (exact GlobalTheory.HTSympCover.onto_tors_iff) | (intros; apply GlobalTheory.HTSympCover.onto_tors_iff  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilyKernelExactIsClopenGeometric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilyKernelExactIsClopenGeometric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.KerClopen

variable {S : Scheme.{0}}

theorem comp_zsmul {L : Type} [AddCommGroup L] {G T T' : Over S} [GrpObj G] (e : L → (T ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (h : T' ⟶ T) (n : ℤ) (a : L) : h ≫ e (n • a) = (h ≫ e a) ^ n := by
  let φ : Multiplicative L →* (T' ⟶ G) :=
    MonoidHom.mk' (fun x => h ≫ e x.toAdd) fun x y => by
      change h ≫ e (x.toAdd + y.toAdd) = _
      rw [he, MonObj.comp_mul]
  exact map_zpow φ (Multiplicative.ofAdd a) n

theorem loc_one (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G) (M : ℕ)
    (hM : IsUnit (M : Γ(S, ⊤))) {L : Type} [AddCommGroup L] (Z : Over S) (e : L → (Z ⟶ G))
    (he : ∀ a c, e (a + c) = e a * e c) (hM' : ∀ a, e a ^ M = 1) (a : L) :
    GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x =>
      (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1) := by
  obtain ⟨Z₁, et, R⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S G M ℤ hG hM
  have hx : ∀ n m : ℤ, e ((n + m) • a) = e (n • a) * e (m • a) := fun n m => by rw [add_smul, he]
  have hx' : ∀ n : ℤ, e (n • a) ^ M = 1 := fun n => hM' _
  have R' : GlobalTheory.LevCover.RepTors G M ℤ Z₁ et := R
  have C := GlobalTheory.LevCover.RepTors.clopenCond (T := Z) R' (fun n : ℤ => e (n • a)) (fun _ => 1) hx hx'
    (fun _ _ => (_root_.mul_one _).symm) (fun _ => one_pow _)
  obtain ⟨U, hU, H⟩ := C
  refine ⟨(U : Set Z.left), ⟨hU, U.isOpen⟩, fun k _ _ x => ?_⟩
  rw [← GlobalTheory.HkClopen.range_subset_iff x]
  have := (H (Over.mk (x ≫ Z.hom)) (Over.homMk x rfl)).symm
  refine this.trans ⟨fun h1 => ?_, fun h1 n => ?_⟩
  · have := h1 1
    rwa [one_smul, MonObj.comp_one] at this
  · rw [MonObj.comp_one, comp_zsmul e he, h1, one_zpow]

end GlobalTheory.KerClopen

open GlobalTheory.KerClopen in
theorem GlobalTheory.kerClopen_geom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := by
  intro S G _ _ hG M h hM0 hM Z e he hM'
  let L := Fin h ⊕ Fin h → ℤ
  obtain ⟨κ, _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod L hM0
  let I₀ := Set.range q
  let r : I₀ → L := fun i => i.2.choose
  have hr : ∀ i : I₀, q (r i) = i.1 := fun i => i.2.choose_spec
  have hP : ∀ a c : L, e (a + M • c) = e a := fun a c => by
    rw [he, GlobalTheory.LevCover.add_map_nsmul he, hM', _root_.mul_one]
  have hQ : ∀ a c : L, (∃ d, a + M • c = M • d) ↔ ∃ d, a = M • d := fun a c =>
    ⟨fun ⟨d, hd⟩ => ⟨d - c, by rw [smul_sub, ← hd, add_sub_cancel_right]⟩,
     fun ⟨d, hd⟩ => ⟨d + c, by rw [hd, smul_add]⟩⟩
  have Lc := GlobalTheory.HkClopen.Loc.comb (I₀ := I₀)
    (fun i => loc_one G hG M hM Z e he hM' (r i)) fun f => ∀ i, (f i ↔ ∃ c, r i = M • c)
  refine Lc.congr fun k _ _ x => ⟨fun H a => ?_, fun H i => H (r i)⟩
  obtain ⟨c, hc⟩ := hq (r ⟨q a, a, rfl⟩) a (hr _)
  have := H ⟨q a, a, rfl⟩
  beta_reduce at this
  revert this hc
  generalize r ⟨q a, a, rfl⟩ = a₀
  intro hc this
  subst hc
  rw [hP, hQ]
  exact this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilyKernelExactIsClopenGeometricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFamily_kernel_exact_isClopen_geometric : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := by
  first | (exact @GlobalTheory.kerClopen_geom) | (exact GlobalTheory.kerClopen_geom) | (intros; apply GlobalTheory.kerClopen_geom  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSymplecticLevelScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympRep

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def PtC {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type) [Field k]
    (y : Sp k ⟶ S) (z : kˣ) (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)) : Prop :=
  (∀ a, f a = 1 ↔ ∃ c, a = M • c) ∧ (∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, f a = g) ∧
    ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M (f a) (f c) (unitOn (z ^ (2 * omegaStd a c)))

theorem ptC_congr {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (k : Type)
    [Field k] (z : kˣ) {y y' : Sp k ⟶ S} (hy : y = y') (f : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A))
    (f' : (Fin h ⊕ Fin h → ℤ) → (Over.mk y' ⟶ o.A)) (hf : ∀ a, (f a).left = (f' a).left) :
    PtC o h M k y z f ↔ PtC o h M k y' z f' := by
  subst hy
  obtain rfl : f = f' := funext fun a => Over.OverMorphism.ext (hf a)
  rfl

theorem lemCyc : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := GlobalTheory.T.exists_cyclotomicAway_finiteEtale_cover

theorem lemKer : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := GlobalTheory.T.torsionFamily_kernel_exact_isClopen_geometric

theorem lemOnto : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := GlobalTheory.T.torsionFamily_surjective_iff_geometricPoint

theorem lemWeil : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Z : Over S) (t₁ : Z.left ⟶ Sp (cycAway M)) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ (β : cycAway M →+* k) (z : kˣ), x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) → ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e c) (unitOn (z ^ (2 * omegaStd a c)))) := GlobalTheory.T.weilPairing_condition_locus_isClopen

theorem exists_sympLevScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
    ∃ (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M)) (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)),
      IsFinite Y.hom ∧ Etale Y.hom ∧
      ∀ (T : Over S) (t₁' : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
        (SympCond o h M T t₁' lv → ∃! f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) ∧
        ((∃ f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) → SympCond o h M T t₁' lv) := by
  intro p _ D R _ b N h M hM hcop S t o
  have hM0 : M ≠ 0 := hM.ne'
  have hMS : IsUnit (M : Γ(S, ⊤)) := by
    have := (b.unit M hcop).map (GlobalTheory.LevCover.fnOn t)
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, eadd, epow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A M (Fin h ⊕ Fin h → ℤ) o.ab hMS
  haveI := hfin
  haveI := het
  obtain ⟨S', t₀, hS1, hS2, hSu⟩ := lemCyc M S hM hMS
  haveI := hS1
  haveI := hS2
  obtain ⟨hW1, hW2⟩ := GlobalTheory.LevCover.finiteEtale_tensor Z S'
  haveI := hW1
  haveI := hW2
  let W : Over S := Z ⊗ S'
  let e : (Fin h ⊕ Fin h → ℤ) → (W ⟶ o.A) := fun a => fst Z S' ≫ et a
  let τ : W.left ⟶ Sp (cycAway M) := (snd Z S').left ≫ t₀
  have eadd' : ∀ a c, e (a + c) = e a * e c := fun a c => by simp only [e, eadd, MonObj.comp_mul]
  have epow' : ∀ a, e a ^ M = 1 := fun a => by simp only [e]; rw [← MonObj.comp_pow, epow, MonObj.comp_one]
  let C : Prop := M = 1 ∨ 2 * h = Module.finrank ℤ D.La
  obtain ⟨Vs, hVs, HV⟩ := (lemKer S o.A o.ab M h hM hMS W e eadd' epow').and
    ((GlobalTheory.HkClopen.Loc.const (S := W.left) C).and (lemWeil p D R b N h M hM hcop S t o W τ e eadd' epow'))
  let U : W.left.Opens := ⟨Vs, hVs.isOpen⟩
  obtain ⟨Y, i, hY1, hY2, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub U hVs.isClosed
  have memIff : ∀ (T : Over S) (w : T ⟶ W) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left)
      (β : cycAway M →+* k) (z : kˣ), (x ≫ w.left) ≫ τ = spMap β → (z : k) = β (zetaAway M) →
      ((x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs ↔
        PtC o h M k (x ≫ T.hom) z (fun a => (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ w ≫ e a)) := by
    intro T w k _ _ x β z hβ hz
    rw [HV k (x ≫ w.left), ← ptC_congr o h M k z (show (x ≫ w.left) ≫ W.hom = x ≫ T.hom by
      rw [Category.assoc, Over.w w]) (fun a => (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a)
      _ (fun a => by simp)]
    have ha : ∀ a c, (Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e (a + c) =
        ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) *
          ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e c) := fun a c => by
      rw [eadd', MonObj.comp_mul]
    have hp : ∀ a, ((Over.homMk (x ≫ w.left) rfl : Over.mk ((x ≫ w.left) ≫ W.hom) ⟶ W) ≫ e a) ^ M = 1 :=
      fun a => by rw [← MonObj.comp_pow, epow', MonObj.comp_one]
    constructor
    · rintro ⟨hk, hC, hw⟩
      exact ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).2 hC, hw β z hβ hz⟩
    · rintro ⟨hk, ho, hw⟩
      refine ⟨hk, (lemOnto p D R b N h M hM hcop S t o k _ _ ha hp hk).1 ho, fun β' z' hβ' hz' => ?_⟩
      obtain rfl : β' = β := GlobalTheory.LevCover.spMap_inj' (hβ'.symm.trans hβ)
      obtain rfl : z' = z := Units.ext (hz'.trans hz.symm)
      exact hw
  have unitζ : ∀ (k : Type) [Field k] (β : cycAway M →+* k), IsUnit (β (zetaAway M)) := fun k _ β =>
    IsUnit.of_pow_eq_one (by rw [← map_pow, GlobalTheory.HTSympCover.zetaAway_pow_self M hM0, map_one]) hM0
  refine ⟨Y, i.left ≫ τ, fun a => i ≫ e a, hY1, hY2, fun T t₁' lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hpow, hgeo⟩ := hL
    obtain ⟨u, hu, huu⟩ := huniv T lv hadd hpow
    obtain ⟨g, ⟨hg1, hg2⟩, hgu⟩ := hSu T.left T.hom t₁'
    let v : T ⟶ S' := Over.homMk g hg1
    let w : T ⟶ W := lift u v
    have hwe : ∀ a, w ≫ e a = lv a := fun a => by
      simp only [w, e]
      rw [← Category.assoc, lift_fst, hu]
    have hwτ : w.left ≫ τ = t₁' := by
      simp only [τ]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      exact hg2
    have hr : Set.range w.left ⊆ U := by
      rintro _ ⟨q, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left q
      obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (x ≫ t₁')
      have hm : (x ≫ w.left) (default : PrimeSpectrum k) ∈ Vs := by
        refine (memIff T w k x β (unitζ k β).unit (by rw [Category.assoc, hwτ, hβ]) rfl).2 ?_
        have := hgeo k x β (unitζ k β).unit hβ rfl
        simp only [hwe]
        exact this
      have hp' : x (default : PrimeSpectrum k) = q := by
        have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
        rwa [hx] at this
      exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left q by rw [← hp']; rfl) ▸ hm
    obtain ⟨f, hf⟩ := (Hi T w).1 hr
    refine ⟨f, ⟨by rw [← Category.assoc, ← Over.comp_left, hf, hwτ], fun a => by
      rw [← Category.assoc, hf, hwe]⟩, fun f' ⟨hf'1, hf'2⟩ => ?_⟩
    have e1 : f' ≫ i ≫ fst Z S' = u := huu _ fun a => by
      have := hf'2 a
      simp only [e, Category.assoc] at this ⊢
      exact this
    have e2 : f' ≫ i ≫ snd Z S' = v := by
      apply Over.OverMorphism.ext
      refine hgu _ ⟨Over.w (f' ≫ i ≫ snd Z S'), ?_⟩
      rw [← hf'1]
      simp [τ]
    have e3 : f' ≫ i = w := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, e1]; exact (lift_fst u v).symm
      · rw [Category.assoc, e2]; exact (lift_snd u v).symm
    exact (cancel_mono i).1 (e3.trans hf.symm)
  · obtain ⟨f, hf1, hf2⟩ := hex
    have hlv : ∀ a, lv a = (f ≫ i) ≫ e a := fun a => by rw [Category.assoc]; exact (hf2 a).symm
    refine ⟨fun a c => by rw [hlv, hlv, hlv, eadd', MonObj.comp_mul],
      fun a => by rw [hlv, ← MonObj.comp_pow, epow', MonObj.comp_one], fun k _ _ x β z hx hz => ?_⟩
    have hr : Set.range (f ≫ i).left ⊆ U := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hm : (x ≫ (f ≫ i).left) (default : PrimeSpectrum k) ∈ Vs := hr ⟨x (default : PrimeSpectrum k), rfl⟩
    have hG := (memIff T (f ≫ i) k x β z (by rw [← hx, ← hf1]; simp) hz).1 hm
    simp only [← hlv] at hG
    exact hG

end GlobalTheory.HTSympRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSymplecticLevelSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_symplecticLevel_scheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t),
    ∃ (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M)) (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)),
      IsFinite Y.hom ∧ Etale Y.hom ∧
      ∀ (T : Over S) (t₁' : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
        (SympCond o h M T t₁' lv → ∃! f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) ∧
        ((∃ f : T ⟶ Y, f.left ≫ t₁ = t₁' ∧ ∀ a, f ≫ lu a = lv a) → SympCond o h M T t₁' lv) := by
  first | (exact @GlobalTheory.HTSympRep.exists_sympLevScheme) | (exact GlobalTheory.HTSympRep.exists_sympLevScheme) | (intros; apply GlobalTheory.HTSympRep.exists_sympLevScheme <;> assumption)
end
