module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegrees
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamRelationNaturalSmoothLiftMorphiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftDegreeOneComparisonRelation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm

universe u

section Gen

variable {C : Type u} [Category.{0} C]

theorem cx_H1_mk_eq_zero_iff (K : Cx C) (x : K.Z1) :
    (QuotientAddGroup.mk x : K.H1) = 0 ↔ ∃ g, K.D0 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem cx_H2_mk_eq_zero_iff (K : Cx C) (x : K.Z2) :
    (QuotientAddGroup.mk x : K.H2) = 0 ↔ ∃ g, K.D1 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

variable {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single1_mem (f : GlobalTheory.CatCoh.Z1 F) :
    ((f.1 : (Coef.ofAlg F).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0)) ∈ (Cx.single (Coef.ofAlg F)).Z1 := by
  show Cx.D1 _ _ = 0
  refine Prod.ext ?_ (Prod.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl) (funext fun _ ↦ rfl))
  funext T T' T'' φ ψ
  have := f.2 φ ψ
  change (mp F ψ) (f.1 T T' φ) - f.1 T T'' (φ ≫ ψ) + f.1 T' T'' ψ = 0
  rw [this]; abel

theorem single_H1_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z1) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H1) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d0 F g = x.1.1 := by
  rw [cx_H1_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen

section Gen2

variable {C : Type u} [Category.{0} C] {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single_fst_mem_Z1 (x : (Cx.single (Coef.ofAlg F)).Z1) : x.1.1 ∈ GlobalTheory.CatCoh.Z1 F := by
  intro T T' T'' φ ψ
  have h : Cx.D1 _ x.1 = 0 := x.2
  have := congrArg (fun c ↦ c.1 T T' T'' φ ψ) h
  change (mp F ψ) (x.1.1 T T' φ) - x.1.1 T T'' (φ ≫ ψ) + x.1.1 T' T'' ψ = 0 at this
  linear_combination -this

theorem single2_mem (z : GlobalTheory.CatCoh.Z2 F) :
    ((z.1 : (Coef.ofAlg F).c2), (fun _ _ _ ↦ PUnit.unit : (Coef.zero C).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0))
      ∈ (Cx.single (Coef.ofAlg F)).Z2 :=
  ⟨fun T T' T'' T''' φ ψ χ ↦ z.2 φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩

theorem single_fst_mem_Z2 (x : (Cx.single (Coef.ofAlg F)).Z2) : x.1.1 ∈ GlobalTheory.CatCoh.Z2 F :=
  fun _ _ _ _ φ ψ χ ↦ x.2.1 _ _ _ _ φ ψ χ

theorem single_H2_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z2) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H2) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d1 F g = x.1.1 := by
  rw [cx_H2_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨(g, fun _ ↦ PUnit.unit), Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen2

section Lift

variable {D : Data} (Λ : Lift D)

theorem smoothLiftThickenings_restrictionOne_sub {k k' : ((KK D.κ D.t).res Λ.L).T1} {w w' : Tot1 (OAff D.s)} (h : Λ.Res1 k w)
    (h' : Λ.Res1 k' w') : Λ.Res1 (k - k') (w - w') := by
  refine ⟨fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V a, h'.1 U V a, map_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2 U, h'.2 U, map_sub, Submodule.Quotient.mk_sub]

theorem smoothLiftThickenings_restrictionTwo_sub {k k' : ((KK D.κ D.t).res Λ.L).T2} {w w' : Tot2 (OAff D.s)} (h : Λ.Res2 k w)
    (h' : Λ.Res2 k' w') : Λ.Res2 (k - k') (w - w') := by
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V W a b, h'.1 U V W a b, map_sub]
  · simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, h.2.1 U V a, h'.2.1 U V a, map_sub,
      Submodule.Quotient.mk_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2.2 U, h'.2.2 U, map_sub, Submodule.Quotient.mk_sub]

end Lift

section Main

variable (D : Data) (Λ : Lift D)

theorem crystallineCechDeRham_degreeOne_relation_total : (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.1
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).1
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.1 D Λ
  have key : ∀ k : (KK D.κ D.t).Z1, (∃ g, GlobalTheory.CatCoh.d0 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D0 g = ((KK D.κ D.t).resMap Λ.L).p1 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H1))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k)).symm.trans e).trans
      (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single1_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k - ⟨_, single1_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    refine ⟨Hyp1.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H1.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp1.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z1 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    obtain ⟨g', hg'⟩ := (hZ _ _ (smoothLiftThickenings_restrictionOne_sub Λ hw1 hk0)).2.1 ⟨g, hg⟩
    refine ⟨GlobalTheory.CatCoh.H1.mk _ ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp1.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H1.mk_eq_zero, Hyp1.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2


set_option maxHeartbeats 1000000 in
theorem crystallineCechDeRham_degreeTwo_relation_total : (∀ c, ∃ h, Λ.Rel2 c h) ∧ (∀ h, ∃ c, Λ.Rel2 c h) ∧
    ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.2
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).2
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.2 D Λ
  have key : ∀ k : (KK D.κ D.t).Z2, (∃ g, GlobalTheory.CatCoh.d1 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D1 g = ((KK D.κ D.t).resMap Λ.L).p2 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H2))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k)).symm.trans e).trans
      (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single2_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k - ⟨_, single2_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    refine ⟨Hyp2.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H2.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp2.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z2 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    have hR : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1 - k0) (w1 - w.1) := smoothLiftThickenings_restrictionTwo_sub Λ hw1 hk0
    have hE := ((hZ _ _ hR).2).1
    obtain ⟨g', hg'⟩ := hE ⟨g, by rw [hg, AddSubgroup.coe_sub]; rfl⟩
    refine ⟨GlobalTheory.CatCoh.H2.mk _ ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp2.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H2.mk_eq_zero, Hyp2.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2

end Main

theorem rel_total_zero : (∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel2 c h) ∧
    (∀ h, ∃ c, Λ.Rel2 c h) ∧ ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) :=
  ⟨crystallineCechDeRham_degreeOne_relation_total, crystallineCechDeRham_degreeTwo_relation_total⟩

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero : (∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧ ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel2 c h) ∧ (∀ h, ∃ c, Λ.Rel2 c h) ∧ ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) := by
  first | exact @GlobalTheory.PDForm.rel_total_zero | exact GlobalTheory.PDForm.rel_total_zero | (intros; apply GlobalTheory.PDForm.rel_total_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftAffineThickenings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebra
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPFlat

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R} (κ : DividedPowers I)

def expS (z : R) (y : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ y ^ n * algebraMap R A (κ.dpow n z)

theorem expS_add_right {z : R} (hz : z ∈ I) (y y' : A) :
    expS κ z (y + y') = expS κ z y * expS κ z y' := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) *
      (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) =
      y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := κ.mul_dpow (m := p.1) (n := p.2) hz
    rw [hp] at h
    calc _ = y ^ p.1 * y' ^ p.2 * algebraMap R A (κ.dpow p.1 z * κ.dpow p.2 z) := by
            rw [map_mul]; ring
      _ = _ := by rw [h, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem expS_add_left {z z' : R} (hz : z ∈ I) (hz' : z' ∈ I) (y : A) :
    expS κ (z + z') y = expS κ z y * expS κ z' y := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]; ring

theorem expS_smul {z : R} (hz : z ∈ I) (a : R) (y : A) :
    expS κ z (algebraMap R A a * y) = expS κ (a * z) y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]
  ring

theorem expS_zero_left (y : A) : expS κ 0 y = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero hn, hn]

theorem expS_zero_right (z : R) (hz : z ∈ I) : expS κ z (0 : A) = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero hz]
  · simp [hn]

theorem expS_sum_right {z : R} (hz : z ∈ I) {K : Type} (s : Finset K) (f : K → A) :
    expS κ z (∑ k ∈ s, f k) = ∏ k ∈ s, expS κ z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_right κ z hz]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]

theorem expS_sum_left {K : Type} (s : Finset K) (f : K → R) (hf : ∀ k ∈ s, f k ∈ I) (y : A) :
    expS κ (∑ k ∈ s, f k) y = ∏ k ∈ s, expS κ (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_left κ y]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk,
      expS_add_left κ (hf k (Finset.mem_insert_self k s))
        (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

theorem prod_expS_eq_one [Module.Flat R A] (c : I →₀ A)
    (hc : (c.sum fun i a ↦ a * algebraMap R A i) = 0) :
    (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * algebraMap R A (κ.dpow n i)) = 1 := by
  have h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A) := by
    rw [Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h
  simp only at hx ha
  change (∏ i ∈ c.support, expS κ (i : R) (c i)) = 1
  rw [← Finset.prod_coe_sort]
  calc ∏ i : c.support, expS κ ((i.1 : I) : R) (c i.1)
      = ∏ i : c.support, ∏ j, expS κ (a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [hx i, expS_sum_right κ (i.1 : I).2]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, expS_smul κ (i.1 : I).2]
    _ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm
    _ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]
    _ = 1 := by
        refine Finset.prod_eq_one fun j _ ↦ ?_
        have : ∑ i : c.support, a i j * ((i.1 : I) : R) = 0 := by
          rw [← ha j]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
        rw [this, expS_zero_left]

theorem exists_isDPMorphism_of_flat : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I),
    ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  intro R A _ _ _ _ I κ
  let x : I → A := fun i ↦ algebraMap R A i
  have hspan : Ideal.span (Set.range x) = I.map (algebraMap R A) := by
    rw [Ideal.map]; congr 1; ext b; simp [x]
  obtain ⟨γ, hγ, hγx⟩ := GlobalTheory.T.exists_isPreDividedPowers_of_generators A I x (fun i n ↦ algebraMap R A (κ.dpow n i))
    (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2])
    (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n ↦ by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (prod_expS_eq_one κ)
  rw [hspan] at hγ
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators A _ γ (Set.range x) hγ hspan.symm (by
    rintro _ ⟨i, rfl⟩ m n hn
    rw [hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]
    simp only [κ.dpow_comp hn i.2, map_mul, map_natCast]
    rw [← hγx])
  exact ⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩

end GlobalTheory.DPFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPMorphismOfFlatAlgebraStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isDPMorphism_of_flat_algebra : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I), ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  first | exact @GlobalTheory.DPFlat.exists_isDPMorphism_of_flat | exact GlobalTheory.DPFlat.exists_isDPMorphism_of_flat | (intros; apply GlobalTheory.DPFlat.exists_isDPMorphism_of_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftAffineThickenings
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift.LiftEx

theorem isPDNilpotent_map {R A : Type} [CommRing R] [CommRing A] {I : Ideal R} {κ : DividedPowers I} (f : R →+* A)
    {δ : DividedPowers (I.map f)} (h : IsDPMorphism κ δ f) (hκ : IsNilDP κ) : IsNilDP δ := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel κ).1 hκ
  refine (isDPNilpotent_iff_exists_isLevel δ).2 ⟨N, ?_⟩
  have := fil_le_map_fil R I κ A _ δ f h rfl N
  rw [show fil κ N = ⊥ from hN, Ideal.map_bot] at this
  exact le_bot_iff.1 this

theorem isDPMorphism_algHom {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {I : Ideal R} {κ : DividedPowers I} {δ : DividedPowers (I.map (algebraMap R A))}
    {δ' : DividedPowers (I.map (algebraMap R A'))} (h : IsDPMorphism κ δ (algebraMap R A))
    (h' : IsDPMorphism κ δ' (algebraMap R A')) (φ : A →ₐ[R] A') : IsDPMorphism δ δ' (φ : A →+* A') := by
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R A '' I) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [RingHom.coe_coe, φ.commutes]
    exact Ideal.mem_map_of_mem _ ha
  · rintro n _ ⟨a, ha, rfl⟩
    rw [h.2 a ha, RingHom.coe_coe, φ.commutes, φ.commutes, h'.2 a ha]

abbrev ext (D : Data) (U : D.X.affineOpens) : Ideal (Sec D.s U.1) := D.I.map (algebraMap D.R (Sec D.s U.1))

theorem exists_pt (D : Data) (U : D.X.affineOpens) : ∃ x : Sp (Sec D.s U.1 ⧸ ext D U) ⟶ D.X₀,
    x ≫ D.i = spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U ∧
    x ≫ D.t = spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  let q : D.R ⧸ D.I →+* Sec D.s U.1 ⧸ ext D U :=
    Ideal.quotientMap (ext D U) (algebraMap D.R (Sec D.s U.1)) Ideal.le_comap_map
  have hq : spMap q ≫ spMap (Ideal.Quotient.mk D.I) =
      spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
    rw [← Cris.spMap_comp]; rfl
  refine ⟨hpb.lift (spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U) (spMap q) ?_, hpb.lift_fst _ _ _, ?_⟩
  · rw [hq, Category.assoc, affPt_w, Cris.spMap_comp]
  · rw [ht, ← Category.assoc, hpb.lift_snd, hq]

theorem exists_dp (D : Data) (U : D.X.affineOpens) :
    ∃ δ : DividedPowers (ext D U), IsDPMorphism D.κ δ (algebraMap D.R (Sec D.s U.1)) := by
  haveI := D.sec_smooth U
  exact GlobalTheory.T.exists_isDPMorphism_of_flat_algebra D.R (Sec D.s U.1) D.I D.κ

theorem thick_hom_ext {R : Type} [CommRing R] {I : Ideal R}
    {X : Scheme} {γ : DividedPowers I} {s : X ⟶ Sp R}
    {T T' : Thick γ s} {f g : T ⟶ T'}
    (h : ∀ b, f.φ b = g.φ b) : f = g := by
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := AlgHom.ext h
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem nonempty_lift : ∀ D : Data, Nonempty (Lift D) := by
  intro D
  choose δ hδ using exists_dp D
  choose x hx hw using exists_pt D
  haveI := D.mono_i
  let T : D.X.affineOpens → Thick D.κ D.t := fun U ↦
    { B := Sec D.s U.1
      J := ext D U
      δ := δ U
      nil := isPDNilpotent_map _ (hδ U) D.nil
      dp := hδ U
      B₀ := Sec D.s U.1 ⧸ ext D U
      π := Ideal.Quotient.mk _
      surj := Ideal.Quotient.mk_surjective
      ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
      x := x U
      w := hw U }
  let m : ∀ {U V : D.X.affineOpens}, V.1 ≤ U.1 → (T U ⟶ T V) := fun {U V} h ↦
    { φ := Sec.res D.s h
      φ₀ := Ideal.quotientMap (ext D V) (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1)
        (Ideal.map_le_iff_le_comap.1 (isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)).1)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)
      pt := by
        rw [← cancel_mono D.i, Category.assoc]
        change spMap _ ≫ x U ≫ D.i = x V ≫ D.i
        rw [hx, hx, ← affPt_res D.s h, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
        rfl }
  refine ⟨{ L := { obj := fun U ↦ T U.unop
                   map := fun a ↦ m (leOfHom a.unop)
                   map_id := fun U ↦ thick_hom_ext fun b ↦ mp_id (OAff D.s) U b
                   map_comp := fun a b ↦ thick_hom_ext fun c ↦ mp_comp (OAff D.s) a b c }
            e := fun _ ↦ AlgEquiv.refl
            nat := fun _ _ ↦ rfl
            gen := fun _ ↦ rfl
            pt := fun U ↦ (hx U.unop).symm
            mem := fun U ↦ ?_ }⟩
  change ⊤ ≤ (x U.unop ≫ D.i) ⁻¹ᵁ U.unop.1
  rw [hx, Scheme.Hom.comp_preimage]
  have : affPt D.s U.unop ⁻¹ᵁ U.unop.1 = ⊤ := U.unop.2.fromSpec_preimage_self
  rw [this]
  exact le_rfl

end GlobalTheory.SmoothLift.LiftEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftAffineThickeningsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_smoothLiftAffineThickenings : ∀ D : Data, Nonempty (Lift D) := by
  first | exact @GlobalTheory.SmoothLift.LiftEx.nonempty_lift | exact GlobalTheory.SmoothLift.LiftEx.nonempty_lift | (intros; apply GlobalTheory.SmoothLift.LiftEx.nonempty_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonRelationsRespectCup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonRelationsRespectCup
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem sgn_mem_rel_of_mem {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [sgn_ι]; exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem mul_ι_mem_rel {x : DR R B} (hx : x ∈ rel R δ) (ω : Ω[B⁄R]) : x * ι1 ω ∈ rel R δ := by
  have h := ι_mul ω (sgn x)
  rw [sgn_sgn] at h
  rw [← h]; exact Ideal.mul_mem_left _ _ (sgn_mem_rel_of_mem δ hx)

theorem mem_divPowerCompatFormRelSubmodule_two_iff {x : Om R B 2} : x ∈ N R δ 2 ↔ (x : DR R B) ∈ rel R δ := Iff.rfl

theorem wedge_mem_N {x y : Ω[B⁄R]} (h : x ∈ N1 R δ ∨ y ∈ N1 R δ) : wedge R B x y ∈ N R δ 2 := by
  rw [mem_divPowerCompatFormRelSubmodule_two_iff, coe_wedge]
  rcases h with h | h
  · exact mul_ι_mem_rel δ h y
  · exact Ideal.mul_mem_left _ _ h


variable (R) in
def kwedge : K1 R δ →ₗ[B] K1 R δ →ₗ[B] K R δ 2 :=
  LinearMap.liftQ₂ _ _ ((wedge R B).compr₂ (N R δ 2).mkQ)
    (fun x hx ↦ LinearMap.ext fun y ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inl hx)))
    (fun y hy ↦ LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inr hy)))

theorem kwedge_mk (x y : Ω[B⁄R]) :
    kwedge R δ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (wedge R B x y) := rfl

end Ring

section Ring2

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem kwedge_swap (x y : K1 R δ) : kwedge R δ x y = -kwedge R δ y x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, kwedge_mk, wedge_swap, Submodule.Quotient.mk_neg]

theorem divPowerCompatFunctionDifferential_mul (a b : B) : kd0 R δ (a * b) = a • kd0 R δ b + b • kd0 R δ a := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.leibniz, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul_eq_wedge_add (b : B) (x : K1 R δ) : kd1 R δ (b • x) = kwedge R δ (kd0 R δ b) x + b • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, divPowerCompatFunctionDifferential_apply, kwedge_mk, dOne_smul, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_wedge_of_closed {x y : K1 R δ} (hx : kd1 R δ x = 0) (hy : kd1 R δ y = 0) : kd2 R δ (kwedge R δ x y) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [divPowerCompatOneFormDerivative_mk, Submodule.Quotient.mk_eq_zero, mem_divPowerCompatFormRelSubmodule_two_iff, coe_dOne] at hx hy
  rw [kwedge_mk, divPowerCompatTwoFormDerivative_mk, Submodule.Quotient.mk_eq_zero]
  change dDR R B (ι1 x * ι1 y) ∈ rel R δ
  rw [dDR_mul, sgn_ι, neg_mul]
  exact add_mem (neg_mem (Ideal.mul_mem_left _ _ hy)) (mul_ι_mem_rel δ hx y)

variable {δ} {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul_function (b : B) (x : K1 R δ) : km1 h hd (b • x) = α b • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, h.oneFormMap_smul_semilinear, Submodule.Quotient.mk_smul]

theorem km_kwedge (x y : K1 R δ) : km h hd 2 (kwedge R δ x y) = kwedge R' δ' (km1 h hd x) (km1 h hd y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, km_mk, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, kwedge_mk, h.mOm_wedge]

end Ring2

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

def cupK (a b : (KK κ t).T1) : (KK κ t).T2 :=
  (fun _ T' T'' φ ψ ↦ (show T''.B from (KK κ t).M0.map ψ (a.1 _ T' φ)) * (show T''.B from b.1 T' T'' ψ),
    fun T T' φ ↦ (show T'.B from a.1 T T' φ) • b.2 T' - (show T'.B from b.1 T T' φ) • (KK κ t).M1.map φ (a.2 T),
    fun T ↦ kwedge R T.δ (a.2 T) (b.2 T))

theorem crystallineCompatibleFormsComplex_cocycleOne_components (k : (KK κ t).Z1) :
    (∀ {T T' T'' : Thick κ t} (φ : T ⟶ T') (ψ : T' ⟶ T''),
      (k.1.1 T T'' (φ ≫ ψ) : T''.B) = ψ.φ (k.1.1 T T' φ) + k.1.1 T' T'' ψ) ∧
    (∀ {T T' : Thick κ t} (φ : T ⟶ T'), k.1.2 T' = (KK κ t).M1.map φ (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ)) ∧
    ∀ T : Thick κ t, kd1 R T.δ (k.1.2 T) = 0 := by
  have h : (KK κ t).D1 k.1 = 0 := k.2
  refine ⟨fun {T T' T''} φ ψ ↦ ?_, fun {T T'} φ ↦ ?_, fun T ↦ ?_⟩
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change ψ.φ (k.1.1 T T' φ) - k.1.1 T T'' (φ ≫ ψ) + k.1.1 T' T'' ψ = 0 at this
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrArg (fun c ↦ c.2.1) h) T) T') φ
    change k.1.2 T' - (KK κ t).M1.map φ (k.1.2 T) - kd0 R T'.δ (k.1.1 T T' φ) = 0 at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · exact congrFun (congrArg (fun c ↦ c.2.2) h) T

end Site

section Site2

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem cupK_mem (a b : (KK κ t).Z1) : cupK a.1 b.1 ∈ (KK κ t).Z2 := by
  obtain ⟨ha1, ha2, ha3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components a
  obtain ⟨hb1, hb2, hb3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components b
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · change χ.φ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ) + χ.φ (a.1.1 T T'' (φ ≫ ψ)) * b.1.1 T'' T''' χ =
      (ψ ≫ χ).φ (a.1.1 T T' φ) * b.1.1 T' T''' (ψ ≫ χ) + χ.φ (a.1.1 T' T'' ψ) * b.1.1 T'' T''' χ
    rw [ha1 φ ψ, hb1 ψ χ, Thick.comp_φ, map_mul, map_add (f := _)]
    ring
  · have hs : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B) (x : K1 R T.δ),
        (KK κ t).M1.map φ (r • x) = φ.φ r • (KK κ t).M1.map φ x := fun φ r x ↦ divPowerCompatOneFormMap_smul_function (SemiHom.of_algHom φ.φ) φ.dp r x
    have hd : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B),
        (KK κ t).M1.map φ (kd0 R T.δ r) = kd0 R T'.δ (φ.φ r) := fun φ r ↦ divPowerCompatOneFormMap_functionDifferential (SemiHom.of_algHom φ.φ) φ.dp r
    change (a.1.1 T T'' (φ ≫ ψ) : T''.B) • b.1.2 T'' - (b.1.1 T T'' (φ ≫ ψ) : T''.B) • (KK κ t).M1.map (φ ≫ ψ) (a.1.2 T) =
      (KK κ t).M1.map ψ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T)) +
      ((a.1.1 T' T'' ψ : T''.B) • b.1.2 T'' - (b.1.1 T' T'' ψ : T''.B) • (KK κ t).M1.map ψ (a.1.2 T')) +
      kd0 R T''.δ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ)
    rw [ha1 φ ψ, hb1 φ ψ, (KK κ t).M1.map_comp, hb2 ψ, ha2 φ]
    simp only [map_add (f := _), map_sub, hs, hd, divPowerCompatFunctionDifferential_mul, smul_add, smul_sub, add_smul]
    module
  · have hd1 : kd1 R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) = 0 :=
      ((KK κ t).diffOne_natural φ _).trans (by rw [show (KK κ t).d1 T (a.1.2 T) = 0 from ha3 T, map_zero])
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = (KK κ t).M2.map φ (kwedge R T.δ (a.1.2 T) (b.1.2 T)) +
      kd1 R T'.δ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T))
    rw [map_sub, divPowerCompatOneFormDerivative_smul_eq_wedge_add, divPowerCompatOneFormDerivative_smul_eq_wedge_add, hb3 T', hd1, smul_zero, smul_zero, add_zero, add_zero]
    change _ = km (SemiHom.of_algHom φ.φ) φ.dp 2 _ + _
    rw [km_kwedge]
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = kwedge R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) ((KK κ t).M1.map φ (b.1.2 T)) + _
    rw [ha2 φ, hb2 φ]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [kwedge_swap T'.δ (kd0 R T'.δ (b.1.1 T T' φ))]
    abel
  · exact divPowerCompatTwoFormDerivative_wedge_of_closed T.δ (ha3 T) (hb3 T)

end Site2

section Main

variable {D : Data} (Λ : Lift D)

theorem Lift.lift_res2_cup {k k' : (KK D.κ D.t).T1} {w w' : Tot1 (OAff D.s)}
    (hk : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k) w) (hk' : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k') w') :
    Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 (cupK k k')) (cupTot (OAff D.s) w w') := by
  have e1 : ∀ U V a, (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w.1 U V a) := hk.1
  have e1' : ∀ U V a, (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w'.1 U V a) := hk'.1
  have e2 : ∀ U, k.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w.2 U)) := hk.2
  have e2' : ∀ U, k'.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w'.2 U)) := hk'.2
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · change (Λ.L.map b).φ (k.1 _ _ (Λ.L.map a)) * (k'.1 _ _ (Λ.L.map b) : (Λ.L.obj W).B) =
      Λ.e W (mp (OAff D.s) b (w.1 U V a) * w'.1 V W b)
    rw [e1, e1', map_mul, Λ.nat]
  · have key : ∀ x, (SemiHom.of_algHom (Λ.L.map a).φ).m1 ((Λ.semi U).m1 x) = (Λ.semi V).m1 (p1 (OAff D.s) a x) :=
      fun x ↦ (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom _) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
        (fun b ↦ (Λ.nat a b).symm) x).trans
        (SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
          (fun _ ↦ rfl) x).symm
    change (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • k'.2 (Λ.L.obj V) -
        (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (k.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi V).m1 (w.1 U V a • w'.2 V - w'.1 U V a • p1 (OAff D.s) a (w.2 U)))
    rw [e1, e1', e2' V, e2 U, divPowerCompatOneFormMap_mk, key, map_sub, SemiHom.oneFormMap_smul_semilinear, SemiHom.oneFormMap_smul_semilinear, Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
    rfl
  · change kwedge D.R (Λ.L.obj U).δ (k.2 (Λ.L.obj U)) (k'.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi U).mOm 2 (wedge D.R _ (w.2 U) (w'.2 U)))
    rw [e2, e2', kwedge_mk, SemiHom.mOm_wedge]

theorem Lift.lift_rel2_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' →
    Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  intro D Λ a b h h' ha hb
  obtain ⟨k, f, w, hf, hw, hkf, hr⟩ := ha
  obtain ⟨k', g, w', hg, hw', hkg, hr'⟩ := hb
  refine ⟨⟨cupK k.1 k'.1, cupK_mem k k'⟩, cupZ _ f g, cupZZ _ w w', ?_, ?_, ?_, Λ.lift_res2_cup hr hr'⟩
  · rw [← hf, ← hg]; rfl
  · rw [← hw, ← hw']; rfl
  · funext T T' T'' φ ψ
    change ψ.φ (k.1.1 T T' φ) * (k'.1.1 T' T'' ψ : T''.B) = ψ.φ (f.1 T T' φ) * g.1 T' T'' ψ
    rw [hkf, hkg]

end Main

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonRelationsRespectCupStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_relations_respect_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  first | exact @GlobalTheory.PDForm.Lift.lift_rel2_cup | exact GlobalTheory.PDForm.Lift.lift_rel2_cup | (intros; apply GlobalTheory.PDForm.Lift.lift_rel2_cup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftComparisonRelationsAddSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftComparisonRelationsAddSmul
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} {δ : DividedPowers J}

theorem divPowerCompatFunctionDifferential_smul (r : R) (b : B) : kd0 R δ (r • b) = r • kd0 R δ b := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul (r : R) (x : K1 R δ) : kd1 R δ (r • x) = r • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_smul (r : R) (x : K R δ 2) : kd2 R δ (r • x) = r • kd2 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatTwoFormDerivative_mk, divPowerCompatTwoFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

variable {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul (r : R) (x : K1 R δ) : km1 h hd (r • x) = σ r • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

theorem km_smul (j : ℕ) (r : R) (x : K R δ j) : km h hd j (r • x) = σ r • km h hd j x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, km_mk, km_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

end Ring

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem crystallineCompatibleFormsComplex_functionMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).M0.map φ (r • x) = r • (KK κ t).M0.map φ x := map_smul (mp (O κ t) φ) r x

theorem crystallineCompatibleFormsComplex_oneFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).M1.map φ (r • x) = r • (KK κ t).M1.map φ x := divPowerCompatOneFormMap_smul (SemiHom.of_algHom φ.φ) φ.dp r x

theorem crystallineCompatibleFormsComplex_twoFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).M2.map φ (r • x) = r • (KK κ t).M2.map φ x := km_smul (SemiHom.of_algHom φ.φ) φ.dp 2 r x

theorem crystallineCompatibleFormsComplex_functionDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).d0 T (r • x) = r • (KK κ t).d0 T x := divPowerCompatFunctionDifferential_smul r x

theorem crystallineCompatibleFormsComplex_oneFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).d1 T (r • x) = r • (KK κ t).d1 T x := divPowerCompatOneFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_twoFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).d2 T (r • x) = r • (KK κ t).d2 T x := divPowerCompatTwoFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_totalDifferentialOne_smul (r : R) (c : (KK κ t).T1) : (KK κ t).D1 (r • c) = r • (KK κ t).D1 c := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    show (KK κ t).M0.map ψ (r • c.1 T T' φ) - r • c.1 T T'' (φ ≫ ψ) + r • c.1 T' T'' ψ =
      r • ((KK κ t).M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ)
    rw [crystallineCompatibleFormsComplex_functionMap_smul, smul_add, smul_sub]
  · funext T T' φ
    show r • c.2 T' - (KK κ t).M1.map φ (r • c.2 T) - (KK κ t).d0 T' (r • c.1 T T' φ) =
      r • (c.2 T' - (KK κ t).M1.map φ (c.2 T) - (KK κ t).d0 T' (c.1 T T' φ))
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, smul_sub, smul_sub]
  · funext T
    exact crystallineCompatibleFormsComplex_oneFormDifferential_smul T r (c.2 T)

theorem crystallineCompatibleFormsComplex_cocyclesOne_smul_mem (r : R) {c : (KK κ t).T1} (hc : c ∈ (KK κ t).Z1) : r • c ∈ (KK κ t).Z1 := by
  have h0 : (KK κ t).D1 c = 0 := hc
  show (KK κ t).D1 (r • c) = 0
  rw [crystallineCompatibleFormsComplex_totalDifferentialOne_smul, h0, smul_zero]

theorem crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem (r : R) {c : (KK κ t).T2} (hc : c ∈ (KK κ t).Z2) : r • c ∈ (KK κ t).Z2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · show (KK κ t).M0.map χ (r • c.1 T T' T'' φ ψ) + r • c.1 T T'' T''' (φ ≫ ψ) χ =
      r • c.1 T T' T''' φ (ψ ≫ χ) + r • c.1 T' T'' T''' ψ χ
    rw [crystallineCompatibleFormsComplex_functionMap_smul, ← smul_add, ← smul_add, h1]
  · show r • c.2.1 T T'' (φ ≫ ψ) = (KK κ t).M1.map ψ (r • c.2.1 T T' φ) + r • c.2.1 T' T'' ψ +
      (KK κ t).d0 T'' (r • c.1 T T' T'' φ ψ)
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, ← smul_add, ← smul_add, h2]
  · show r • c.2.2 T' = (KK κ t).M2.map φ (r • c.2.2 T) + (KK κ t).d1 T' (r • c.2.1 T T' φ)
    rw [crystallineCompatibleFormsComplex_twoFormMap_smul, crystallineCompatibleFormsComplex_oneFormDifferential_smul, ← smul_add, h3]
  · show (KK κ t).d2 T (r • c.2.2 T) = 0
    rw [crystallineCompatibleFormsComplex_twoFormDifferential_smul, h4, smul_zero]

end Site

theorem rel_add_smul : ∀ (D : Data) (Λ : Lift D),
    (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧
    (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧
    (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧
    ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  intro D Λ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add (f := _), hf, hf'], by rw [map_add (f := _), hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V c ↦ (congrArg₂ (· + ·) (hr.1 U V c) (hr'.1 U V c)).trans (map_add (Λ.e V) _ _).symm,
        fun U ↦ (congrArg₂ (· + ·) (hr.2 U) (hr'.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (w.1.2 U + w'.1.2 U))
      rw [map_add (f := _), Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesOne_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V c ↦ (congrArg (r • ·) (hr.1 U V c)).trans (map_smul (Λ.e V) r _).symm,
        fun U ↦ (congrArg (r • ·) (hr.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (r • w.1.2 U))
      rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add (f := _), hf, hf'], by rw [map_add (f := _), hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V W c d ↦ (congrArg₂ (· + ·) (hr.1 U V W c d) (hr'.1 U V W c d)).trans (map_add (Λ.e W) _ _).symm,
        fun U V c ↦ (congrArg₂ (· + ·) (hr.2.1 U V c) (hr'.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg₂ (· + ·) (hr.2.2 U) (hr'.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (w.1.2.1 U V c + w'.1.2.1 U V c))
        rw [map_add (f := _), Submodule.Quotient.mk_add]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (w.1.2.2 U + w'.1.2.2 U))
        rw [map_add (f := _), Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V W c d ↦ (congrArg (r • ·) (hr.1 U V W c d)).trans (map_smul (Λ.e W) r _).symm,
        fun U V c ↦ (congrArg (r • ·) (hr.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg (r • ·) (hr.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (r • w.1.2.1 U V c))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (r • w.1.2.2 U))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftComparisonRelationsAddSmulStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothLift_comparisonRelations_add_smul : ∀ (D : Data) (Λ : Lift D), (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧ (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧ (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧ ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  first | exact @GlobalTheory.PDForm.rel_add_smul | exact GlobalTheory.PDForm.rel_add_smul | (intros; apply GlobalTheory.PDForm.rel_add_smul <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem exists_linearEquiv_of_rel {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : M → N → Prop) (h1 : ∀ c, ∃ h, p c h) (h2 : ∀ h, ∃ c, p c h)
    (h0 : ∀ c h, p c h → (c = 0 ↔ h = 0)) (hadd : ∀ a b h h', p a h → p b h' → p (a + b) (h + h'))
    (hsmul : ∀ (r : R) a h, p a h → p (r • a) (r • h)) : ∃ e : M ≃ₗ[R] N, ∀ c h, e c = h ↔ p c h := by
  choose f hf using h1
  have uniq : ∀ c h h', p c h → p c h' → h' = h := by
    intro c h h' ph ph'
    have q := hadd _ _ _ _ ph' (hsmul (-1) _ _ ph)
    rw [neg_one_smul, neg_one_smul, add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).1 rfl)
  let g : M →ₗ[R] N :=
    { toFun := f
      map_add' := fun a b ↦ uniq _ _ _ (hadd _ _ _ _ (hf a) (hf b)) (hf (a + b))
      map_smul' := fun r a ↦ uniq _ _ _ (hsmul r _ _ (hf a)) (hf (r • a)) }
  have inj : Function.Injective g := by
    intro a b hab
    have q := hadd _ _ _ _ (hf a) (hsmul (-1) _ _ (hf b))
    rw [neg_one_smul, neg_one_smul] at q
    have hab' : f a = f b := hab
    rw [hab', add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).2 rfl)
  have surj : Function.Surjective g := by
    intro h
    obtain ⟨c, hc⟩ := h2 h
    exact ⟨c, uniq _ _ _ hc (hf c)⟩
  refine ⟨LinearEquiv.ofBijective g ⟨inj, surj⟩, fun c h ↦ ⟨?_, fun ph ↦ uniq _ _ _ ph (hf c)⟩⟩
  rintro rfl
  exact hf c

end GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem crystallineSmoothLift_of_relations : GlobalTheory.Published.CrystallineSmoothLift := by
  have Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (GlobalTheory.T.nonempty_smoothLiftAffineThickenings D)
  obtain ⟨hr1, hr2⟩ := GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.1
  have E2 : ∀ D : Data, ∃ e : CatCoh.H2 (O D.κ D.t) ≃ₗ[D.R] HH2 D.s, ∀ c h, e c = h ↔ (Λ D).Rel2 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr2 D (Λ D)).1 (hr2 D (Λ D)).2.1 (hr2 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.2
  choose e₁ he₁ using E1
  choose e₂ he₂ using E2
  have r1 : ∀ D c, (Λ D).Rel1 c (e₁ D c) := fun D c ↦ (he₁ D c _).1 rfl
  have r2 : ∀ D c, (Λ D).Rel2 c (e₂ D c) := fun D c ↦ (he₂ D c _).1 rfl
  refine ⟨e₁, e₂, ?_, ?_, ?_⟩
  · intro D a b
    exact (he₂ D _ _).2 (GlobalTheory.T.comparison_relations_respect_cup D (Λ D) a b _ _ (r1 D a) (r1 D b))
  · intro D m c
    exact (he₁ D _ _).2 (GlobalTheory.T.smoothLift_degreeOne_comparisonRelation D (Λ D) m c)
  · intro D D' σ φ φ₀ h m hc
    exact ⟨fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r1 D c) (r1 D' _),
      fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.2 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r2 D c) (r2 D' _)⟩

end GlobalTheory.SmoothLift
