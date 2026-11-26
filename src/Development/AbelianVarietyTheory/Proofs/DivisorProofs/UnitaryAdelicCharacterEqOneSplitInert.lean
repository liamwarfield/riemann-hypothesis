module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInert
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInert
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLocalPoint

open GlobalTheory.BotClassDict GlobalTheory.NormRatio GlobalTheory.NormRatio.StdLevel

theorem idem_mul_idem {D : D7} {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε η : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hη : IsPlaceIdem D w η) (hne : w ≠ v) : η * ε = 0 := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨β, rfl, -, k0⟩ := hη
  refine Prod.ext (zero_mul (0 : Ainf D.host.F)) (FiniteAdeleRing.ext _ fun u => ?_)
  change β u * α u = 0
  by_cases hu : u = v
  · have : β u = 0 := k0 u (hu ▸ hne.symm)
    rw [this, zero_mul]
  · have : α u = 0 := h0 u hu
    rw [this, mul_zero]

theorem suppInert_finStd {D : D7} (V : HSp D) (hG : V.gram = 1) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) {g : GA D V} (hg : GlobalTheory.WeilParts.SuppPl ε V g) :
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q hq hnI i j
  have e : ((finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j -
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j = finQ D ((Formalism.L2.Theta.mt V g - 1) i j) := by
    rw [Matrix.sub_apply, RingHom.map_sub, finStd_apply]
    congr 1
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  rw [e]
  refine (GlobalTheory.ZeroAtPlaces.zeroAt_finQ_iff D q hq _).2 fun w η hη hqw => ?_
  have hne : w ≠ v := by
    rintro rfl
    exact hnI ((GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq w ε hv.1 hqw).2 hv)
  rw [← hg i j, ← mul_assoc, ← map_mul, idem_mul_idem hv.1 hη hne, map_zero, zero_mul]

theorem intG_finStd {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V}
    (h : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) ↔
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E
        ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) :
    Formalism.MainNotions.StandardLatticesGL3.IntG D (finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  have e1 : ∀ (k : GA D V) (i j : Fin V.rank),
      (((finStd V hG k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔
        (finHom V k).1 i j ∈ intAE D := fun k i j => by
    rw [← toAfE_int_iff, toAfE_finStd, mem_intAE_iff_swap]
  have e2 : ((↑(finStd V hG g) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) =
      ↑(finStd V hG g⁻¹) := by rw [map_inv, Subgroup.coe_inv]
  have hR : ∀ y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, y i ∈ intSub D) ↔ ∀ i, ((finHom V g).1 *ᵥ y) i ∈ intSub D := fun y =>
    (mem_latHat_stdLat V y).symm.trans ((h y).trans (mem_latHat_stdLat V _))
  have h1 : (finHom V g).1 * (finHom V g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : (finHom V g⁻¹).1 * (finHom V g).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  obtain ⟨ha, hb⟩ := (preserves_iff (intSub D) _ _ h1 h2).1 hR
  intro i j
  rw [e2]
  exact ⟨(e1 g i j).2 (ha i j), (e1 g⁻¹ i j).2 (hb i j)⟩

theorem suppInert_and_intG : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), GlobalTheory.WeilParts.NonSplitAt D v ε → ∀ g : Formalism.L2.Theta.GA D V, GlobalTheory.WeilParts.SuppPl ε V g → (∀ y : Fin V.rank → TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔ (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun V hG _ _ hv _ hg h => ⟨suppInert_finStd V hG hv hg, intG_finStd V hG h⟩

end GlobalTheory.InertLocalPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonSplitSupportedFinitePartIntegralInertStatement
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonSplitSupported_finitePart_integral_inert : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), GlobalTheory.WeilParts.NonSplitAt D v ε → ∀ g : Formalism.L2.Theta.GA D V, GlobalTheory.WeilParts.SuppPl ε V g → (∀ y : Fin V.rank → TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔ (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.BotClassDict.finStd V hG g : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.InertLocalPoint.suppInert_and_intG | exact GlobalTheory.InertLocalPoint.suppInert_and_intG | (intros; apply GlobalTheory.InertLocalPoint.suppInert_and_intG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleCharStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleChar
namespace GlobalTheory

noncomputable def circArgChar {G : Type} [Group G] (ν : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ), by
    have h : ‖(ν g : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν g).ne_zero
    simp [Submonoid.unitSphere, h]⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' a b := by
    apply Circle.ext
    show ((ν (a * b) : ℂˣ) : ℂ) / (‖((ν (a * b) : ℂˣ) : ℂ)‖ : ℂ) =
      ((ν a : ℂ) / (‖(ν a : ℂ)‖ : ℂ)) * ((ν b : ℂ) / (‖(ν b : ℂ)‖ : ℂ))
    rw [ν.map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

noncomputable def circNormChar {G : Type} [Group G] (ν : G →* ℂˣ) (t : ℝ) : G →* Circle where
  toFun g := Circle.exp (t * Real.log ‖(ν g : ℂ)‖)
  map_one' := by simp
  map_mul' a b := by
    have ha : ‖(ν a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν a).ne_zero
    have hb : ‖(ν b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν b).ne_zero
    show Circle.exp (t * Real.log ‖((ν (a * b) : ℂˣ) : ℂ)‖) = _
    rw [ν.map_mul, Units.val_mul, norm_mul, Real.log_mul ha hb, mul_add, Circle.exp_add]

private theorem coe_circArgChar_eq_div_norm {G : Type} [Group G] (ν : G →* ℂˣ) (g : G) :
    ((circArgChar ν g : Circle) : ℂ) = (ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ) := by
  rfl

theorem complexChar_eq_one_of_forall_circleChar :
    ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G),
      (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  intro G _ ν x h
  have hx0 : (ν x : ℂ) ≠ 0 := (ν x).ne_zero
  have hpos : 0 < ‖(ν x : ℂ)‖ := norm_pos_iff.mpr hx0

  have hn : ‖(ν x : ℂ)‖ = 1 := by
    by_contra hne
    have hlog : Real.log ‖(ν x : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hne
    have h2 := h (circNormChar ν (Real.pi / Real.log ‖(ν x : ℂ)‖)) (fun g hg => by
      simp [circNormChar, hg])
    have h3 := congrArg (fun z : Circle => (z : ℂ)) h2
    simp only [circNormChar, MonoidHom.coe_mk, OneHom.coe_mk, Circle.coe_exp,
      div_mul_cancel₀ _ hlog, Circle.coe_one] at h3
    norm_num [Complex.exp_pi_mul_I] at h3

  have h1 := h (circArgChar ν) (fun g hg => by
    apply Circle.ext
    rw [coe_circArgChar_eq_div_norm, hg]
    simp)
  have h4 := congrArg (fun z : Circle => (z : ℂ)) h1
  simp only [coe_circArgChar_eq_div_norm, Circle.coe_one, hn, Complex.ofReal_one, div_one] at h4
  apply Units.ext
  simpa using h4

end GlobalTheory
end

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_forall_circle_char_eq_one : ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G), (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  first | exact @GlobalTheory.complexChar_eq_one_of_forall_circleChar | exact GlobalTheory.complexChar_eq_one_of_forall_circleChar | (intros; apply GlobalTheory.complexChar_eq_one_of_forall_circleChar <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofinite
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertCofinite

open Matrix TensorProduct Formalism.UG Formalism.UG.P Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem eps_dvd_nat (D : D7) (P : ℕ → Prop) (n : ℕ) (hn : n ≠ 0) (h : ∀ q : ℕ, q.Prime → q ∣ n → ¬ P q) :
    ∃ t ∈ OhE D, eps D.host.E P = (n : AE D) * t := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => exact ⟨_, eps_mem P, by simp⟩
  | prime p hp =>
    obtain ⟨s, hs, e⟩ := eps_dvd (E := D.host.E) P hp (h p hp dvd_rfl) 1
    exact ⟨s, hs, by simpa using e⟩
  | mul a b ha hb =>
    obtain ⟨s, hs, es⟩ := ha (left_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_right _)
    obtain ⟨t, ht, et⟩ := hb (right_ne_zero_of_mul hn) fun q hq hd => h q hq (hd.mul_left _)
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    rw [← eps_idem P]
    conv_lhs => enter [1]; rw [es]
    rw [et]
    push_cast
    ring

theorem exists_denom (D : D7) (y : AE D) : ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (F := ℚ) y
  obtain ⟨z, rfl⟩ : ∃ z : ℤ, d = z := ⟨Rat.ringOfIntegersEquiv d, by
    apply Rat.ringOfIntegersEquiv.injective; simp⟩
  have hz : z.natAbs ≠ 0 := by rintro h; apply hd0; simp [Int.natAbs_eq_zero.1 h]
  have hC : levelafC (F := ℚ) D.host.E (z : 𝓞 ℚ) = (z : AE D) := by
    rw [levelafC, map_intCast]
    exact map_intCast (Algebra.TensorProduct.includeRight : _ →ₐ[ℚ] AE D) z
  refine ⟨z.natAbs, Nat.pos_of_ne_zero hz, ?_⟩
  rw [hC] at hd
  rcases Int.natAbs_eq z with e | e
  · rw [e] at hd; simpa [OhE] using hd
  · rw [e] at hd
    have := neg_mem hd
    simpa [OhE] using this

theorem exists_denom_zeroAt (D : D7) (y : AE D) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * y ∈ OhE D ∧ ∀ q : ℕ, q.Prime → q ∣ n → ¬ ZeroAt D q y := by
  have hex := exists_denom D y
  obtain ⟨h0, h1⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h0, h1, fun q hq hd hz => ?_⟩
  obtain ⟨m, hm, hc, s, hs, e⟩ := hz 0
  rw [pow_zero, one_mul] at e
  have hm' : (m : AE D) * y ∈ OhE D := e ▸ hs
  have hg : ((Nat.gcd (Nat.find hex) m : ℕ) : AE D) * y ∈ OhE D := by
    have := congrArg (Int.cast : ℤ → AE D) (Nat.gcd_eq_gcd_ab (Nat.find hex) m)
    push_cast at this
    rw [this]
    convert add_mem (mul_mem (intCast_mem (OhE D) (Nat.gcdA (Nat.find hex) m)) h1)
      (mul_mem (intCast_mem (OhE D) (Nat.gcdB (Nat.find hex) m)) hm') using 1
    ring
  have hle := Nat.find_min' hex ⟨Nat.gcd_pos_of_pos_left _ h0, hg⟩
  have heq : Nat.gcd (Nat.find hex) m = Nat.find hex := le_antisymm (Nat.gcd_le_left _ h0) hle
  have : q ∣ m := hd.trans (heq ▸ Nat.gcd_dvd_right _ _)
  exact (Nat.Prime.coprime_iff_not_dvd hq).1 hc.symm this

theorem intG_of_entries (D : D7) {N : ℕ} (g : GA D N)
    (h : ∀ i j, ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) :
    IntG D (g : GL (Fin N) (AE D)) := by
  have hg : cT (sgA D) ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g : GL (Fin N) (AE D)) =
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) := g.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hg
  intro i j
  refine ⟨h i j, ?_⟩
  rw [Units.inv_eq_of_mul_eq_one_left hg]
  exact csDual_sig_mem _ (h j i)

theorem intG_part_cofinite {D : D7} {N : ℕ} (y : GA D N) (hy : SuppInert D (y : GL (Fin N) (AE D))) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ InertQ D p) ∧
      IntG D (part D (fun p => p ∉ s) y : GL (Fin N) (AE D)) := by
  choose n h0 h1 h2 using fun ij : Fin N × Fin N => exists_denom_zeroAt D
    (((y : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) ij.1 ij.2)
  refine ⟨Finset.univ.biUnion fun ij => (n ij).primeFactors, fun p hp => ?_, intG_of_entries D _ fun i j => ?_⟩
  · obtain ⟨ij, -, hp⟩ := Finset.mem_biUnion.1 hp
    have hq := Nat.prime_of_mem_primeFactors hp
    refine ⟨hq, ?_⟩
    by_contra hi
    exact h2 ij p hq (Nat.dvd_of_mem_primeFactors hp) (hy p hq hi ij.1 ij.2)
  · obtain ⟨t, ht, e⟩ := eps_dvd_nat D (fun p => p ∉ Finset.univ.biUnion fun ij => (n ij).primeFactors) (n (i, j))
      (h0 _).ne' fun q hq hd hn => hn (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Nat.mem_primeFactors.2 ⟨hq, hd, (h0 _).ne'⟩⟩)
    have := add_mem (mul_mem ht (h1 (i, j))) (one_entry_mem (OhE D) i j)
    convert this using 1
    show cutM _ _ _ i j = _
    rw [cutM_apply, e]
    ring

end GlobalTheory.InertCofinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofiniteStatement
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ Formalism.MainNotions.StandardLatticesGL3.InertQ D p) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.NormSum.VacInt.part D (fun p => p ∉ s) y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.InertCofinite.intG_part_cofinite | exact GlobalTheory.InertCofinite.intG_part_cofinite | (intros; apply GlobalTheory.InertCofinite.intG_part_cofinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProd
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.NormSum.VacInt.PartFin

open GlobalTheory.NormSum.VacInt

section Cut

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem cutM_of_eq_zero (e : R) (he : e * e = e) (h : e = 0) (A : Matrix n n R) : cutM e he A = 1 := by
  subst h
  show (0 : R) • A + (1 - 0 : R) • (1 : Matrix n n R) = 1
  simp

theorem cutM_add (e e' f : R) (he : e * e = e) (he' : e' * e' = e') (hf : f * f = f) (h0 : e * e' = 0)
    (h : f = e + e') (A : Matrix n n R) : cutM f hf A = cutM e he A * cutM e' he' A := by
  subst h
  have h1 : e * (1 - e') = e := by linear_combination - h0
  have h2 : (1 - e) * e' = e' := by linear_combination - h0
  have h3 : (1 - e) * (1 - e') = 1 - (e + e') := by linear_combination h0
  show (e + e') • A + (1 - (e + e')) • (1 : Matrix n n R) =
    (e • A + (1 - e) • (1 : Matrix n n R)) * (e' • A + (1 - e') • (1 : Matrix n n R))
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, h0, h1, h2, h3,
    zero_smul, zero_add, add_smul]
  abel

end Cut

variable {E : Type} [Field E] [NumberField E]

theorem eps_empty : eps E (fun p => p ∈ (∅ : Finset ℕ)) = 0 :=
  ext_prV fun v => by rw [prV_eps, map_zero]; simp

theorem eps_insert (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p ∈ insert q s) = eps E (fun p => p = q) + eps E (fun p => p ∈ s) :=
  ext_prV fun v => by
    rw [map_add (f := _), prV_eps, prV_eps, prV_eps]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · by_cases h2 : pr v ∈ s <;> simp [h1, h2]

theorem eps_single_mul (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p = q) * eps E (fun p => p ∈ s) = 0 :=
  ext_prV fun v => by
    rw [map_mul, prV_eps, prV_eps, map_zero]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · simp [h1]

theorem part_finset : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  intro D N y
  exact ⟨Subtype.ext (Units.ext (cutM_of_eq_zero _ _ eps_empty _)), fun q s h =>
    Subtype.ext (Units.ext (cutM_add _ _ _ _ _ _ (eps_single_mul q s h) (eps_insert q s h) _))⟩

end GlobalTheory.NormSum.VacInt.PartFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPrimeComponentFinsetProdStatement
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPrimeComponent_finset_prod : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  first | exact @GlobalTheory.NormSum.VacInt.PartFin.part_finset | exact GlobalTheory.NormSum.VacInt.PartFin.part_finset | (intros; apply GlobalTheory.NormSum.VacInt.PartFin.part_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimesStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppInertUnitaryAdelicPointComponentAtPrimes
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.PartSupp

open Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum.VacInt

theorem zeroAt_mul_left (D : Formalism.BasicNotions.D7) {q : ℕ} {e z : AE D} (he : e ∈ OhE D) (hz : ZeroAt D q z) :
    ZeroAt D q (e * z) := by
  intro k
  obtain ⟨m, hm, hc, s, hs, h⟩ := hz k
  exact ⟨m, hm, hc, e * s, mul_mem he hs, by linear_combination e * h⟩

theorem trivAt_part_of_trivAt (D : Formalism.BasicNotions.D7) {N : ℕ} (P : ℕ → Prop) (g : GA D N) {q : ℕ}
    (h : TrivAt D q (g : GL (Fin N) (AE D))) : TrivAt D q (part D P g : GL (Fin N) (AE D)) := by
  intro i j
  have := zeroAt_mul_left D (e := eps D.host.E P) (eps_mem P) (h i j)
  convert this using 1
  show cutM _ _ _ i j - _ = _
  rw [cutM_apply]
  ring

theorem suppInert_part_of_suppInert : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N),
    Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :=
  fun {D} {_} P y hy q hq h => trivAt_part_of_trivAt D P y (hy q hq h)

end GlobalTheory.NormSum.PartSupp
end

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (P : ℕ → Prop) (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (GlobalTheory.NormSum.VacInt.part D P y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | exact GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert | (intros; apply GlobalTheory.NormSum.PartSupp.suppInert_part_of_suppInert <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePart
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes _root_.Formalism.L2.Theta GlobalTheory.BotClassDict GlobalTheory.NormSum.VacInt

variable {D : D7}

theorem idem_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D w ε') (hv : v ≠ w) : ε * ε' = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, k1, k0⟩ := h'
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext _ fun u => ?_)
  change α u * α' u = 0
  by_cases hu : u = v
  · subst hu
    exact (congrArg (α u * ·) (k0 u hv)).trans (mul_zero _)
  · exact (congrArg (· * α' u) (h0 u hu)).trans (zero_mul _)

theorem cut_mul_cut {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] {e f : R} (h : e * f = 0) (A : Matrix n n R) :
    (e • A + (1 - e • (1 : Matrix n n R))) * (f • A + (1 - f • (1 : Matrix n n R))) =
      (e + f) • A + (1 - (e + f) • (1 : Matrix n n R)) := by
  have h' : f * e = 0 := by rw [mul_comm, h]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, smul_sub, smul_add,
    h, h', zero_smul, add_smul]
  abel

theorem mt_mul (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_prod (V : HSp D) (g : GA D V) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (L : List (HeightOneSpectrum (𝓞 D.host.F))) (hL : L.Nodup) :
    Formalism.L2.Theta.mt V (L.map fun v => GlobalTheory.VacStab.locPart V v g).prod =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (L.map ε).sum • 1) := by
  induction L with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, RingHom.map_zero, zero_smul, zero_smul, zero_add, sub_zero]
    rfl
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    have h0 : ε v * (L.map ε).sum = 0 := by
      rw [← List.sum_map_mul_left]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact idem_orth (hε v) (hε w) fun e => hL.1 (e ▸ hw)
    rw [List.map_cons, List.prod_cons, mt_mul, GlobalTheory.VacStab.mt_locPart V (hε v), ih hL.2, List.map_cons, List.sum_cons,
      RingHom.map_add]
    exact cut_mul_cut (by rw [← RingHom.map_mul, h0, RingHom.map_zero]) _

theorem natCast_mem_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) : (q : 𝓞 F) ∈ (Q.under (𝓞 F)).asIdeal ↔ (q : 𝓞 E) ∈ Q.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 E) _ ∈ Q.asIdeal ↔ _
  rw [map_natCast]

theorem finQ_sum_idem {q : ℕ} (hq : q.Prime) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F)
    (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    finQ D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (∑ v ∈ S, ε v)) = eps D.host.E fun p => p = q := by
  apply (GlobalTheory.BotFormula.toFinE D).injective
  refine FiniteAdeleRing.ext _ fun Q => ?_
  have hev : ∀ w : HeightOneSpectrum (𝓞 D.host.F), (∑ v ∈ S, ε v).2 w = if w ∈ S then 1 else 0 := by
    intro w
    have e1 : (∑ v ∈ S, ε v).2 w = ∑ v ∈ S, evalV D.host.F w (sndA D.host.F (ε v)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← map_sum]
      rfl
    have e2 : ∀ v, evalV D.host.F w (sndA D.host.F (ε v)) = if w = v then 1 else 0 := by
      intro v
      obtain ⟨α, h, h1, h0⟩ := hε v
      rw [h]
      change evalV D.host.F w α = _
      split_ifs with hw
      · subst hw; exact h1
      · exact h0 w hw
    rw [e1, Finset.sum_congr rfl fun v _ => e2 v, Finset.sum_ite_eq]
  have hr : GlobalTheory.BotFormula.toFinE D (eps D.host.E fun p => p = q) Q =
      GlobalTheory.AdeleBaseChange.locMap ℚ Q (if pr (Q.under (𝓞 ℚ)) = q then 1 else 0) := by
    have := toFinE_tmul (D := D) 1 (idem fun p => p = q)
    rw [map_one, one_mul] at this
    refine (congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) this).trans ?_
    refine (GlobalTheory.AdeleBaseChange.adMap_apply _ Q).trans (congrArg _ ?_)
    rw [idem, mkInt_apply]
    congr
  have hiff : Q.under (𝓞 D.host.F) ∈ S ↔ pr (Q.under (𝓞 ℚ)) = q := by
    rw [hS, natCast_mem_under, ← Nat.prime_dvd_prime_iff_eq (pr_prime _) hq, pr_dvd_iff, natCast_mem_under]
  rw [GlobalTheory.ZeroAtPlaces.comp_base, hev, hr]
  by_cases h : Q.under (𝓞 D.host.F) ∈ S
  · rw [if_pos h, if_pos (hiff.1 h), map_one, map_one]
  · rw [if_neg h, if_neg (fun e => h (hiff.2 e)), map_zero, map_zero]

theorem exists_prod_eq_part : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  intro D V hG q hq g
  have hI : Ideal.span {(q : 𝓞 D.host.F)} ≠ ⊥ := by simpa using hq.ne_zero
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := (Ideal.finite_factors hI).toFinset
  have hS : ∀ v, v ∈ S ↔ (q : 𝓞 D.host.F) ∈ v.asIdeal := fun v => by
    simp [S, Ideal.dvd_span_singleton]
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  refine ⟨S.toList.map fun v => GlobalTheory.VacStab.locPart V v g, ?_, ?_⟩
  · intro h hh
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hh
    exact ⟨v, ε v, hε v, (hS v).1 (Finset.mem_toList.1 hv), GlobalTheory.VacStab.suppPl_locPart V (hε v) g⟩
  · have hm := mt_prod V g ε hε S.toList (Finset.nodup_toList S)
    rw [Finset.sum_map_toList] at hm
    have he := finQ_sum_idem hq S hS ε hε
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    have h1 : finQ D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact RingHom.map_one _
      · exact RingHom.map_zero _
    change finQ D (Formalism.L2.Theta.mt V _ i j) = eps D.host.E (fun p => p = q) * finQ D (Formalism.L2.Theta.mt V g i j) +
      (1 - eps D.host.E fun p => p = q) * (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j
    rw [hm, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, he, h1, sub_mul, one_mul]

end GlobalTheory.PrimePart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProdLocalComponentsEqPrimePartStatement
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prod_localComponents_eq_primePart : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  first | exact @GlobalTheory.PrimePart.exists_prod_eq_part | exact GlobalTheory.PrimePart.exists_prod_eq_part | (intros; apply GlobalTheory.PrimePart.exists_prod_eq_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterEqOneSplitInert
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertSuppChar

theorem eq_one_at_inert {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (μ : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* Circle)
    (hμ : ∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
      Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → μ k = 1)
    {q : ℕ} (hq : q.Prime) (hi : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) :
    μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 := by
  obtain ⟨g, hg⟩ := GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG y rfl
  rw [← GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hg]
  obtain ⟨l, hl, e⟩ := GlobalTheory.T.exists_prod_localComponents_eq_primePart V hG q hq g
  rw [← e, map_list_prod, map_list_prod, List.map_map]
  refine List.prod_eq_one (M := Circle) fun z hz => ?_
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hz
  obtain ⟨v, ε, hε, hqv, hs⟩ := hl h hh
  have hn : GlobalTheory.WeilParts.NonSplitAt D v ε := (GlobalTheory.InertPlace.inertQ_iff_nonSplitAt D q hq v ε hε hqv).1 hi
  refine GlobalTheory.InertChar.char_eq_one_of_nonSplit D V _
    (GlobalTheory.NormRatio.SphCoset.isSelfDualC_of_gram_one hG (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D V.rank)) v ε hn
    (μ.comp (GlobalTheory.BotClassDict.finStd V hG)) (fun k hk hst => ?_) h hs
  obtain ⟨a1, a2⟩ := GlobalTheory.T.nonSplitSupported_finitePart_integral_inert V hG v ε hn k hk hst
  exact hμ _ a1 a2

theorem char_eq_one : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D), V.gram = 1 → ∀ (ν : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* ℂˣ),
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
    Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  ∀ x, ν x = 1 := by
  intro D V hG ν hs hi x
  refine GlobalTheory.T.eq_one_of_forall_circle_char_eq_one ν x fun μ hμ => ?_
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun q => ¬ Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x, map_mul,
    hμ _ (hs _ (GlobalTheory.NormSum.VacInt.suppSplit_part D x)), one_mul]
  have hy := GlobalTheory.NormSum.VacInt.suppInert_part D x
  generalize GlobalTheory.NormSum.VacInt.part D (fun q => ¬¬Formalism.MainNotions.StandardLatticesGL3.InertQ D q) x = y at hy ⊢
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite y hy
  rw [← GlobalTheory.NormSum.VacInt.part_mul_compl D (fun p => p ∈ s) y, map_mul,
    hμ _ (hi _ (GlobalTheory.T.suppInert_unitaryAdelicPointComponentAtPrimes _ _ hy) hs2), mul_one]
  have hloc : ∀ q, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → μ (GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y) = 1 :=
    fun q hq hqi => eq_one_at_inert V hG μ (fun k a1 a2 => hμ _ (hi k a1 a2)) hq hqi y
  clear hs2
  induction s using Finset.induction_on with
  | empty => rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).1, map_one]
  | insert q s hq ih =>
    rw [(GlobalTheory.T.unitaryPrimeComponent_finset_prod y).2 q s hq, map_mul, hloc q (hs1 q (Finset.mem_insert_self q s)).1
      (hs1 q (Finset.mem_insert_self q s)).2, one_mul]
    exact ih fun p hp => hs1 p (Finset.mem_insert_of_mem hp)

end GlobalTheory.InertSuppChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterEqOneSplitInertStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (ν : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* ℂˣ),
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  (∀ k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, Formalism.MainNotions.StandardLatticesGL3.SuppInert D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
    Formalism.MainNotions.StandardLatticesGL3.IntG D (k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ν k = 1) →
  ∀ x, ν x = 1 := by
  first | exact @GlobalTheory.InertSuppChar.char_eq_one | exact GlobalTheory.InertSuppChar.char_eq_one | (intros; apply GlobalTheory.InertSuppChar.char_eq_one <;> assumption)
end
