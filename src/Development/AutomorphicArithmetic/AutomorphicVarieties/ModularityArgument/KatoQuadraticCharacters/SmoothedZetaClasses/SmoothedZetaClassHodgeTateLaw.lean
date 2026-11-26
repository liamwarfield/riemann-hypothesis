module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertia
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuationNewformCongruence
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedPresOfShCoc
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousOfCg
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHtPresNu7
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyProdInv
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_trans {m : ℕ} {x y z : Qbar l} (h : Cg m x y) (h' : Cg m y z) : Cg m x z := by
  unfold Cg at *
  have hm := IsUltrametricDist.norm_add_le_max (x - y) (y - z)
  rw [sub_add_sub_cancel] at hm
  exact hm.trans (max_le h h')

theorem cg_symm {m : ℕ} {x y : Qbar l} (h : Cg m x y) : Cg m y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_sum {m : ℕ} {ι : Type} (S : Finset ι) {x y : ι → Qbar l} (h : ∀ i ∈ S, Cg m (x i) (y i)) :
    Cg m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

theorem cg_mul_left {m : ℕ} {o x y : Qbar l} (ho : ‖o‖ ≤ 1) (h : Cg m x y) : Cg m (o * x) (o * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖o‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ho (norm_nonneg _)
    _ = ‖x - y‖ := one_mul _
    _ ≤ _ := h

end GlobalTheory.KumUnit
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ.UnitPres

open GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem kumVal_int {n : ℕ} {ζ u v : Ω} {s : G ℚ Ω} {j : ℤ} (hζ : ζ ^ (l ^ n) = 1) (hv : v ^ (l ^ n) = u)
    (hs : s v = ζ ^ j * v) : GlobalTheory.Col.KumVal (l := l) n ζ u s (j : ZMod (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hpos.ne'] at hζ; exact zero_ne_one hζ
  refine ⟨v, hv, ?_⟩
  rw [hs, ← zpow_natCast, ZMod.val_intCast]
  congr 1
  conv_lhs => rw [← Int.emod_add_mul_ediv j ((l ^ n : ℕ) : ℤ)]
  rw [zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem cg_intCast (n : ℕ) (j : ℤ) : Cg (l := l) n (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) (j : Qbar l) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h1 : (((j : ZMod (l ^ n)).val : ℕ) : ℤ) - j = ((l ^ n : ℕ) : ℤ) * (-(j / ((l ^ n : ℕ) : ℤ))) := by
    rw [ZMod.val_intCast, Int.emod_def]; ring
  have e : (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) - (j : Qbar l) =
      (l : Qbar l) ^ n * ((-(j / ((l ^ n : ℕ) : ℤ)) : ℤ) : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) h1
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_pow] at this
    exact this
  rw [Cg, e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one (Qbar l) _)

theorem exists_open [IsAlgClosure ℚ Ω] (h : G ℚ Ω → Qbar l) (hc : Continuous h) (h1 : h 1 = 0) (m : ℕ) :
    ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ s ∈ U, Cg m (h s) 0 := by
  have hl : (0 : ℝ) < ‖((l : ℕ) : Qbar l) ^ m‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have hn : {s | ‖h s‖ < ‖((l : ℕ) : Qbar l) ^ m‖} ∈ nhds (1 : G ℚ Ω) :=
    (isOpen_lt hc.norm continuous_const).mem_nhds (by simpa [h1] using hl)
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hn
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun s hs => ?_⟩
  rw [Cg, sub_zero]
  exact le_of_lt (hsub hs)

theorem layer_one {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) : z 1 1 = 0 := by
  have h := hz.2 1 (one_mem _) 1 (one_mem _) 1
  rw [mul_one, map_one, inv_one, mul_one] at h
  have h' : (ν 1 : Qbar l) * z 1 1 = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h').resolve_left (ν 1).ne_zero

theorem layer_add {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) {s t : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A)
    (ht : t ∈ Dec (F := ℚ) A) (hc : cycMod ℚ Ω l r s = 1) : z (s * t) 1 = z s 1 + (ν s : Qbar l) * z t 1 := by
  have h := hz.2 s hs t ht 1
  rwa [hc, inv_one, mul_one] at h

end GlobalTheory.KZ.UnitPres
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.AllRoots

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem pres_of_vanish (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → Z m s 1 = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A c m 0 Z ζ P o := by
  refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, hζ, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
  have h := GlobalTheory.Col.kumPres_empty A (n := m - 0) (r := m) (ζ := ζ ^ l ^ 0) (by simpa using hζ) (by omega) (Z m) hZ
  convert h using 2 <;> exact Empty.elim ‹_›

theorem continuous_of_cg [Algebra.IsAlgebraic ℚ Ω] (f : G ℚ Ω → Qbar l)
    (h : ∀ n : ℕ, ∃ E0 : Finset Ω, ∀ s s' : G ℚ Ω, (∀ z ∈ E0, s' z = z) → Cg n (f (s * s')) (f s)) : Continuous f := by
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt1
  obtain ⟨E0, hE⟩ := h n
  have hopen : ∀ᶠ t in nhds (1 : G ℚ Ω), ∀ z ∈ E0, t z = z := by
    rw [Filter.eventually_all_finset]
    intro z _
    have ho := stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Ω) z
    exact ho.mem_nhds (one_mem _)
  have hcont : Filter.Tendsto (fun t : G ℚ Ω => s⁻¹ * t) (nhds s) (nhds 1) := by
    have := (continuous_const_mul s⁻¹).tendsto s
    rwa [inv_mul_cancel] at this
  filter_upwards [hcont.eventually hopen] with t ht
  have := hE s (s⁻¹ * t) ht
  rw [mul_inv_cancel_left, Cg, norm_pow, hnl] at this
  rw [dist_eq_norm]
  exact this.trans_lt hn

end GlobalTheory.LambdaValuationPowers.AllRoots
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.Smooth

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_sub_sub {m : ℕ} {a b a' b' : Qbar l} (h : Cg m a a') (h' : Cg m b b') : Cg m (a - b) (a' - b') := by
  have e : a - b - (a' - b') = (a - a') + -(b - b') := by ring
  rw [Cg, e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h (by rw [norm_neg]; exact h'))

theorem isUnit_natCast_padic {d : ℕ} (hd : Nat.Coprime d l) : IsUnit (d : ℤ_[l]) := by
  have hlp : l.Prime := Fact.out
  by_contra h
  have h1 : ‖((d : ℤ) : ℤ_[l])‖ < 1 := by
    rw [← PadicInt.mem_nonunits]; simpa using h
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h1
  exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hd.symm (Int.natCast_dvd_natCast.mp h1)

theorem smoothed_pres [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (hL : ∀ r, Layer2 c A ν r (Z r)) (hc : ∀ r, Continuous fun s => Z r s 1)
    (hI : ∀ s ∈ Ine (F := ℚ) A, ν s = 1) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Z r s y - (d₀ : Qbar l) * Z r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)))
        ζ P o := by
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i =>
    haveI : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (pow_pos hlp.pos i).ne'⟩
    inferInstance
  have hpos : 0 < l ^ m := pow_pos hlp.pos _
  haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
  have hz := hL m
  set z := Z m with hzdef
  set uu := ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right m hd₀) with huu
  have hl : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hlv⟩ := hA
    have := (hv (l : 𝓞 ℚ)).2 hlv
    simpa using this
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker
  have hH : ∀ s, s ∈ H ↔ s ∈ Ine (F := ℚ) A ∧ cycMod ℚ Ω l m s = 1 := fun s => Iff.rfl
  have hfix : ∀ s, cycMod ℚ Ω l m s = 1 → s ζ = ζ := fun s hs =>
    GlobalTheory.Col.fix_of_cycMod le_rfl hs hζ.pow_eq_one

  have hu₀ := isUnit_natCast_padic (l := l) hd₀
  obtain ⟨ρ, hρ, hρc⟩ := GlobalTheory.CycInertia.exists_mem_Ine_toZModPow Ω l A hl hu₀.unit m
  rw [hu₀.unit_spec, map_natCast] at hρc
  have hρD : ρ ∈ Dec (F := ℚ) A := Ine_le_Dec A hρ
  have hρi : ρ⁻¹ ∈ Ine (F := ℚ) A := inv_mem hρ
  have hρζ : ρ ζ = ζ ^ d₀ := by
    have hspec : ρ ζ = ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l ρ : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω ρ) ζ hζ.pow_eq_one
    rw [hspec, hρc, ZMod.val_natCast, hζ.eq_orderOf, pow_mod_orderOf]
  have hcρ : (cycMod ℚ Ω l m ρ⁻¹)⁻¹ = uu := by
    rw [map_inv, inv_inv]
    exact Units.ext (by rw [huu, ZMod.coe_unitOfCoprime]; exact hρc)
  have z11 : z 1 1 = 0 := GlobalTheory.KZ.UnitPres.layer_one hz
  have key : ∀ s ∈ H, z s uu = z (ρ⁻¹ * s * ρ) 1 := by
    intro s hs
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    have hsD := Ine_le_Dec A hsI
    have e1 := hz.2 ρ⁻¹ (inv_mem hρD) (s * ρ) (mul_mem hsD hρD) 1
    have e2 := hz.2 s hsD ρ hρD uu
    have e3 := hz.2 ρ⁻¹ (inv_mem hρD) ρ hρD 1
    rw [hcρ] at e1 e3
    rw [inv_mul_cancel, z11, hI _ hρi, Units.val_one, one_mul, one_mul] at e3
    rw [hI _ hρi, Units.val_one, one_mul, one_mul] at e1
    rw [hI _ hsI, Units.val_one, one_mul, hsc, inv_one, mul_one] at e2
    rw [mul_assoc]
    linear_combination -e1 - e2 + e3
  have hHρ : ∀ s ∈ H, ρ⁻¹ * s * ρ ∈ H := fun s hs => by
    obtain ⟨hsI, hsc⟩ := (hH s).1 hs
    refine (hH _).2 ⟨?_, ?_⟩
    · have := conj_mem_Ine (inv_mem hρD) hsI
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, hsc, mul_one, map_inv, inv_mul_cancel]
  obtain ⟨ι, hι, o, crd, ho, hadd, hzero, hcrd, -⟩ := GlobalTheory.CoefCoord.coord_mod_pow l c m
  obtain ⟨U, hU, hUz⟩ := GlobalTheory.KZ.UnitPres.exists_open (fun s => z s 1) (hc m) z11 m
  have hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ H, s u = u) ∧
      ∀ s ∈ H, GlobalTheory.Col.KumVal (l := l) m ζ u s (crd (z s 1) i) := fun i =>
    GlobalTheory.KumFix.exists_kumVal l Ω m H (GlobalTheory.isClosed_Ine_inf_ker_cycMod l Ω A _) ζ hζ
      (fun s hs => hfix s hs.2) (fun s => crd (z s 1) i)
      (fun s hs t ht => by
        show crd (z (s * t) 1) i = crd (z s 1) i + crd (z t 1) i
        rw [GlobalTheory.KZ.UnitPres.layer_add hz (Ine_le_Dec A hs.1) (Ine_le_Dec A ht.1) hs.2, hI s hs.1, Units.val_one, one_mul,
          hadd _ (hz.1 _ _) _ (hz.1 _ _), Pi.add_apply])
      U hU (fun s _ hs => by
        show crd (z s 1) i = 0
        rw [hzero _ (hz.1 _ _) (hUz s hs), Pi.zero_apply])
  choose u hu0 hufix huk using hex

  have hw0 : ∀ i, u i * (ρ (u i))⁻¹ ≠ 0 := fun i =>
    mul_ne_zero (hu0 i) (inv_ne_zero ((map_ne_zero ρ).2 (hu0 i)))
  have hvw : ∀ i, A.valuation (u i * (ρ (u i))⁻¹) = 1 := fun i => by
    rw [map_mul, map_inv₀, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hρD, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).2 (hu0 i)
  have hwfix : ∀ i, ∀ s ∈ H, s (u i * (ρ (u i))⁻¹) = u i * (ρ (u i))⁻¹ := fun i s hs => by
    have e : s (ρ (u i)) = ρ ((ρ⁻¹ * s * ρ) (u i)) := by
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
    rw [map_mul, map_inv₀, hufix i s hs, e, hufix i _ (hHρ s hs)]
  have hP : ∀ i, ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧
      P.eval ζ = u i * (ρ (u i))⁻¹ := fun i =>
    GlobalTheory.CycIne.exists_poly_of_fixed l Ω A hA m ζ hζ _ ((A.valuation_le_one_iff _).1 (hvw i).le)
      (fun s h1 h2 => hwfix i s ((hH s).2 ⟨h1, h2⟩))
  choose P hPc hPe using hP
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpos.ne'

  have hkw : ∀ s ∈ H, ∀ i, GlobalTheory.Col.KumVal (l := l) m ζ (u i * (ρ (u i))⁻¹) s
      ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)) := by
    intro s hs i
    obtain ⟨v, hv, hsv⟩ := huk i s hs
    obtain ⟨v', hv', hsv'⟩ := huk i _ (hHρ s hs)
    refine GlobalTheory.KZ.UnitPres.kumVal_int hζ.pow_eq_one (v := v * (ρ v')⁻¹) ?_ ?_
    · rw [mul_pow, inv_pow, ← map_pow, hv', hv]
    · have e : s (ρ v') = ρ ((ρ⁻¹ * s * ρ) v') := by
        rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]; congr 1; group
      rw [map_mul, map_inv₀, hsv, e, hsv', map_mul, map_pow, hρζ, zpow_sub₀ hζ0, zpow_mul]
      simp only [zpow_natCast]
      ring
  refine ⟨ι, hι, P, o, hζ, hPc, fun i => (ho i).1, fun i => by rw [hPe]; exact hw0 i, ?_⟩
  show GlobalTheory.Col.KumPres A m m (ζ ^ l ^ 0) _ _ _
  rw [pow_zero, pow_one]
  refine ⟨hζ, le_rfl, fun i => ?_, fun i => (ho i).2, fun s hs hc' _ => ?_⟩
  · simp only [hPe]
    refine ⟨(A.valuation_le_one_iff _).1 (hvw i).le, hw0 i, (A.valuation_le_one_iff _).1 ?_⟩
    rw [map_inv₀, hvw i, inv_one]
  · have hsH : s ∈ H := (hH s).2 ⟨hs, hc'⟩
    refine ⟨fun i => ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : ZMod (l ^ m)),
      fun i => by simp only [hPe]; exact hkw s hsH i, ?_⟩
    show Cg m (z s 1 - (d₀ : Qbar l) * z s (1 * uu)) _
    rw [one_mul, key s hsH]
    have h2 := hcrd _ (hz.1 s 1)
    have h3 := hcrd _ (hz.1 (ρ⁻¹ * s * ρ) 1)
    have h4 := cg_sub_sub h2 (GlobalTheory.KumUnit.cg_mul_left (o := (d₀ : Qbar l)) (IsUltrametricDist.norm_natCast_le_one (Qbar l) d₀) h3)
    refine GlobalTheory.KumUnit.cg_trans h4 (GlobalTheory.KumUnit.cg_symm (GlobalTheory.KumUnit.cg_trans
      (GlobalTheory.KumUnit.cg_sum _ fun i _ => GlobalTheory.KumUnit.cg_mul_left (ho i).2 (GlobalTheory.KZ.UnitPres.cg_intCast _ _)) ?_))
    have e : (∑ i, o i * ((((crd (z s 1) i).val : ℤ) - (d₀ : ℤ) * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : ℤ) : ℤ) : Qbar l)) =
        (∑ i, o i * ((crd (z s 1) i).val : Qbar l)) - (d₀ : Qbar l) * ∑ i, o i * ((crd (z (ρ⁻¹ * s * ρ) 1) i).val : Qbar l) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [e, Cg, sub_self, norm_zero]
    exact norm_nonneg _

theorem smoothed_pres_of_shCoc [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) (c : Coef l)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hD : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0)
    (hI : ∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hY : ∀ r, GlobalTheory.KA.ShCoc (fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l))) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r))
    (hc : ∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : G ℚ Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) →
      Cg n (Y r (s * s') y 1) (Y r s y 1))
    (hO : ∀ r s y, Y r s y 1 ∈ c.O) (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l) (m : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m)) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m 0 (fun r s y => Y r s y 1 - (d₀ : Qbar l) *
        Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  classical
  have hnz : ∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 := by
    intro s hs h
    have := (ρ s).det_ne_zero
    rw [Matrix.det_fin_two, hD s hs, h] at this
    simp at this
  let ν : G ℚ Ω → (Qbar l)ˣ := fun s =>
    if h : (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 ≠ 0 then Units.mk0 _ h else 1
  have hν : ∀ s ∈ Dec (F := ℚ) A, (ν s : Qbar l) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 := by
    intro s hs
    simp only [ν, dif_pos (hnz s hs), Units.val_mk0]
  refine smoothed_pres A hA c ν (fun r s y => Y r s y 1) (fun r => ⟨hO r, fun s hs u _ x => ?_⟩)
    (fun r => GlobalTheory.LambdaValuationPowers.AllRoots.continuous_of_cg _ fun n => ?_) (fun s hs => ?_) d₀ hd₀ m ζ hζ
  · have := congrFun (hY r s u x) 1
    show Y r (s * u) x 1 = Y r s x 1 + (ν s : Qbar l) * Y r u (x * (cycMod ℚ Ω l r s)⁻¹) 1
    rw [this, hν s hs]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hD s hs]
  · obtain ⟨E0, hE⟩ := hc r n
    exact ⟨E0, fun s s' h => hE s s' 1 h⟩
  · exact Units.ext (by rw [hν s (Ine_le_Dec A hs), hI s hs, Units.val_one])

theorem exists_pres_smoothed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
    AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
    (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
    (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
    (∀ r s y, Y r s y 1 ∈ cf.O) →
  ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
  ∃ (m₀ c₀' : ℕ), ∀ m, m₀ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
    HTPresNuOfPolys A cf m c₀' (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o := by
  intro l _ Ω _ _ _ ι e S A W g hN hS ε X pr N _ cw c d gm ψ₀ cf α _ _ _ hAdm _ j _ c₀ Y hZ hY hc hO d₀ hd₀ _
  refine ⟨0, 0, fun m _ ζ hζ => ?_⟩
  by_cases hcw : ∃ x, cw x ≠ 0
  · obtain ⟨x, hx⟩ := hcw
    obtain ⟨ρ, hρ, -, hD, hI, -⟩ := GlobalTheory.RhoAdm.rho_ordinary_shape l Ω ι e S A W g ψ₀ hN hS
      (hAdm.1 x hx).2.2.2.2.2.2.2.2.2.2.2
    have hfun : rhoK W e ψ₀ = fun s => (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) := funext fun s => (hρ s).symm
    exact smoothed_pres_of_shCoc A hN.atL cf ρ hD hI Y (fun r => hfun ▸ hY r) hc hO d₀ hd₀ m ζ hζ
  · refine GlobalTheory.LambdaValuationPowers.AllRoots.pres_of_vanish A cf _ m ζ hζ fun s _ _ => ?_
    obtain ⟨Yx, -, hs⟩ := hZ
    push_neg at hcw
    simp [hs, hcw]

end GlobalTheory.LambdaValuationPowers.Smooth
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SmoothedZetaClasses.Imports
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SmoothedZetaClasses.Hco
noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.KZ GlobalTheory.Ord2 GlobalTheory.K4

namespace GlobalTheory.LambdaValuationPowers

open ZetaCoef

theorem _root_.UpperTheory.V.Z.Kato.K5.hco : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], l ≠ 2 →
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω) (j : Ω →+* Qbar l), OverL l A → (∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) →
  ∀ (N : ℕ) [NeZero N], ¬ l ∣ N → ∀ (c d e : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), 1 ≤ e →
  ∀ (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (pr : X.Fn l → Fin 2 → Qbar l) (ψ : ZMod l → Qbar l) (cf : Coef l),
  ∀ (α : Qbar l), GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l 1 s = 1 → rhoK W e ψ s 1 0 = 0 ∧ rhoK W e ψ s 1 1 = 1) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χ δ)) → (∀ a b : ℕ, χ (a * b) = χ a * χ b) →
    (∀ a b : ℕ, a % N = b % N → χ a = χ b) →
  ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χ j pr cf lam →
  ∀ (c₀ : ℕ), ∃ (c' : ℕ) (κ₀ : Qbar l) (per : ℕ → Qbar l), κ₀ ≠ 0 ∧ (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧ ∀ (x : ZMod N),
  GlobalTheory.K4.AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf →
  ∀ (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y →
  ∀ m : ℕ, 1 ≤ m → ∀ (y : (ZMod (l ^ m))ˣ) (β : ℕ) (t : ℤ),
    (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
    GlobalTheory.LambdaValuationPowers.HTCoL A cf j (fun r s y' => Y r s y' 1) m c' y
      ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ * ∑ δ : (ZMod N)ˣ,
        (algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]))⁻¹ *
        lam (fun i => (l : Qbar l) ^ m * j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m)
          (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
            ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0)
            (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
            ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i))) := by
  intro Ω _ _ _ ε X l _ hl2 hφ A j hA hj N _ hlN c d e gm he ι gN W pr ψ cf α hadm hIne χ hχu hχmul hχper lam hlam c₀
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨h5, hlcop, hgm, hα, hU⟩ := hadm
  obtain ⟨hdχ, hfin, hfixL, cL, per, hper, hLF⟩ := hlam
  obtain ⟨S, hS⟩ := GlobalTheory.KummerEisensteinGalois.FinSupp.exists_sum hfin
  obtain ⟨k, hk⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l (∑ i ∈ S, ‖lam (Pi.single i 1)‖)
  have hLk : ∀ i ∈ S, ‖lam (Pi.single i 1)‖ ≤ (l : ℝ) ^ k := fun i hi =>
    le_trans (Finset.single_le_sum (f := fun i => ‖lam (Pi.single i 1)‖) (fun _ _ => norm_nonneg _) hi) hk
  set M : Qbar l := ((Fintype.card (ZMod N)ˣ : ℕ) : Qbar l) with hM
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact_mod_cast Fintype.card_ne_zero
  obtain ⟨v, hv⟩ : ∃ v : ℕ, ‖(l : Qbar l) ^ v‖ ≤ ‖M‖ := by
    obtain ⟨v, hv⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hM0) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l))
    exact ⟨v, by rw [norm_pow]; exact hv.le⟩
  by_cases hex : ∃ x, GlobalTheory.K4.AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf
  swap
  · refine ⟨0, 1, per, one_ne_zero, fun n => ⟨(hper n).1, (hper n).2.1⟩, fun x hx => ?_⟩
    exact absurd ⟨x, hx⟩ hex
  obtain ⟨x₀, hx₀⟩ := hex
  obtain ⟨c₁, κ', hκ', H⟩ := UpperTheory.Kd.L.thdiam Ω ε X l hl2 hφ A j hA hj N hlN c d e gm hx₀.1 hx₀.2.1 hx₀.2.2.1 hx₀.2.2.2.1 he hx₀.2.2.2.2.2.2.2.2.2.1 hx₀.2.2.2.2.2.2.2.2.2.2.1 pr α ⟨h5, hlcop, hgm, hα, hU⟩
  refine ⟨c₁ + k + v, κ' / M, per, div_ne_zero hκ' hM0, fun n => ⟨(hper n).1, (hper n).2.1⟩, fun x hx3 Y hY m hm y β t hβy hβ1 hmt => ?_⟩
  obtain ⟨hc1, hd1, hcc, hdc, hpradd, hprsmul, hprO, hprgal, -, -, -, -⟩ := hx3
  have hw : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hcopδ : ∀ δ : (ZMod N)ˣ, Nat.Coprime (δ : ZMod N).val N := fun δ => ZMod.val_coe_unit_coprime δ
  set u : (ZMod N)ˣ → ℤ_[l] := fun δ => (((hχu _ (hcopδ δ)).unit⁻¹ : (ℤ_[l])ˣ) : ℤ_[l]) with hu
  have huχ : ∀ δ, u δ * χ (δ : ZMod N).val = 1 := fun δ => (hχu _ (hcopδ δ)).val_inv_mul
  have hualg : ∀ δ, algebraMap ℤ_[l] (Qbar l) (u δ) = (algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]))⁻¹ := by
    intro δ
    have h1 : algebraMap ℚ_[l] (Qbar l) ((u δ : ℤ_[l]) : ℚ_[l]) * algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [← map_mul, ← PadicInt.coe_mul, huχ δ, PadicInt.coe_one, map_one]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) (u δ)]
    exact eq_inv_of_mul_eq_one_left h1
  set Qf : (ZMod N)ˣ → ℕ → Qbar l := fun δ i => j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m)
          (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
            ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0)
            (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
            ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i) with hQf
  set E : Qbar l := (l : Qbar l) ^ c₀ * κ' * ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) * lam (fun i => (l : Qbar l) ^ m * Qf δ i) with hE
  obtain ⟨kE, hkE⟩ := GlobalTheory.KummerEisensteinGalois.exists_le_l_pow l ‖E‖
  obtain ⟨bB, hbB, b, hbO, hYb⟩ := hY m (m + kE + cL)
  rw [hw] at hbB
  choose g hgA hg using fun δ => H x m (m + kE + cL) c₀ hm (by omega) bB hbB y δ
  apply GlobalTheory.LambdaValuationPowers.ZetaCoef.htCoL_of_fintype (ι := ↥S × (ZMod N)ˣ)
    (fun p => (l : Qbar l) ^ v / M * (per (m + kE + cL))⁻¹ * ((l : Qbar l) ^ k * lam (Pi.single (p.1 : ℕ) 1)) * algebraMap ℤ_[l] (Qbar l) (u p.2))
    (fun p => (g p.2).coeff ((p.1 : ℕ) : ℚ))
  · have hfm : ∀ a b : Qbar l, FixIc cf a → FixIc cf b → FixIc cf (a * b) := by
      intro a b ha hb σ h1 h2
      rw [map_mul, ha σ h1 h2, hb σ h1 h2]
    have hfi : ∀ a : Qbar l, FixIc cf a → FixIc cf a⁻¹ := by
      intro a ha σ h1 h2
      rw [map_inv₀, ha σ h1 h2]
    have hfn : ∀ q : ℕ, FixIc cf ((l : Qbar l) ^ q) := by
      intro q σ _ _
      rw [map_pow, map_natCast]
    have hfM : FixIc cf M := by
      intro σ _ _
      exact map_natCast σ _
    have hfu : ∀ a : ℤ_[l], FixIc cf (algebraMap ℤ_[l] (Qbar l) a) := by
      intro a σ _ _
      exact (σ.restrictScalars ℤ_[l]).commutes a
    intro p
    refine ⟨?_, ?_, (hj _).1 (hgA p.2 _)⟩
    · have h1 : ‖(l : Qbar l) ^ v / M‖ ≤ 1 := by
        rw [norm_div]
        exact div_le_one_of_le₀ hv (norm_nonneg _)
      have h2 : ‖(per (m + kE + cL))⁻¹‖ ≤ 1 := by
        rw [norm_inv, (hper _).1, inv_one]
      have h3 : ‖(l : Qbar l) ^ k * lam (Pi.single (p.1 : ℕ) 1)‖ ≤ 1 :=
        GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le (hLk _ p.1.2)
      have h4 := GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le (l := l) (u p.2)
      rw [norm_mul, norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3) (norm_nonneg _) h4
    · refine hfm _ _ (hfm _ _ (hfm _ _ ?_ (hfi _ (hper _).2.2)) (hfm _ _ (hfn k) (hfixL _))) (hfu _)
      rw [div_eq_mul_inv]
      exact hfm _ _ (hfn v) (hfi _ hfM)
  intro s hs hsm
  set n := m + kE + cL with hn
  have hsumle : ∀ {ι' : Type} (T : Finset ι') (f : ι' → Qbar l) (r : ℝ), 0 ≤ r → (∀ i ∈ T, ‖f i‖ ≤ r) → ‖∑ i ∈ T, f i‖ ≤ r :=
    fun T f r hr h => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr h
  have hcgsum : ∀ {ι' : Type} (T : Finset ι') (a b : ι' → Qbar l) (q : ℕ), (∀ i ∈ T, Cg q (a i) (b i)) →
      Cg q (∑ i ∈ T, a i) (∑ i ∈ T, b i) := by
    intro ι' T a b q h
    unfold Cg
    rw [← Finset.sum_sub_distrib]
    exact hsumle T _ _ (norm_nonneg _) h
  have hcgmul : ∀ (q : ℕ) (r a b : Qbar l), ‖r‖ ≤ 1 → Cg q a b → Cg q (r * a) (r * b) := by
    intro q r a b hr h
    unfold Cg at *
    rw [← mul_sub, norm_mul]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hr) h
  have hcgtrans : ∀ (q : ℕ) (a b c' : Qbar l), Cg q a b → Cg q b c' → Cg q a c' := by
    intro q a b c' h1 h2
    unfold Cg at *
    have : a - c' = (a - b) + (b - c') := by ring
    rw [this]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h1 h2)
  have hnpow : ∀ q : ℕ, ‖(l : Qbar l) ^ q‖ ≤ 1 := fun q => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)).le
  have hlnon : (l : Ω) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hmem
    have h1 := (hj _).1 hmem
    rw [map_inv₀, map_natCast, norm_inv] at h1
    have h2 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)
    have h3 : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 GlobalTheory.LambdaValuationPowers.natCast_ne_zero
    have h4 : 1 < ‖(l : Qbar l)‖⁻¹ := one_lt_inv₀ h3 |>.2 h2
    linarith
  have hs1 := GlobalTheory.LambdaValuationPowers.ZetaCoef.cycMod_one_of hm hsm
  have hrho := hIne s hs hs1
  have hgal : ∀ (s' : Gal(Ω/ℚ)), ∀ b' ∈ X.B N l (2 * e - 1), (X.galB l s') b' ∈ X.B N l (2 * e - 1) :=
    GlobalTheory.KZ.StabGal.galB_mem_B ε X ε.injective hφ N l (2 * e - 1) hl2 h5 hlcop.symm hodd
  obtain ⟨hfB, hfpr⟩ := GlobalTheory.LambdaValuationPowers.ZetaCoef.pushB_spec X (N := N) (2 * e - 1) n m pr W e ψ hgal hpradd hprgal bB
    (fun σ hσ => (hbB σ hσ).1) s y
  set f := GlobalTheory.LambdaValuationPowers.ZetaCoef.pushB X l n m N bB s y with hf
  have hdB : ∀ δ : (ZMod N)ˣ, X.diam N l (δ : ZMod N).val f ∈ X.B N l (2 * e - 1) := fun δ =>
    GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l (2 * e - 1) _ (NeZero.pos N) hlcop.symm (hcopδ δ) f hfB
  have hφ' : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs := by
    obtain ⟨φ, h1, h2⟩ := hφ
    exact ⟨φ, h2, h1⟩
  choose φδ hφδ _ using fun δ : (ZMod N)ˣ =>
    GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l halg hφ' hl2 hlN h5 hlnon n (2 * e - 1) hodd _ (hdB δ)
  obtain ⟨Φ, hΦ, hΦc⟩ := GlobalTheory.LambdaValuationPowers.ZetaCoef.exists_isThB_sum X hj hlnon Finset.univ Finset.univ_nonempty u
    (fun δ => X.diam N l (δ : ZMod N).val f) φδ hdB hφδ
  have hInChi := GlobalTheory.LambdaValuationPowers.ZetaCoef.inChi_avg X (N := N) hlcop.symm (w := 2 * e - 1) (χ := χ)
    (fun a b k _ _ hk => by rw [← hχmul]; exact hχper _ _ hk) u huχ hfB
  have hF := hLF n (by omega) _ hInChi Φ hΦ
  have hprsum : pr (∑ δ : (ZMod N)ˣ, u δ • X.diam N l (δ : ZMod N).val f) =
      ∑ δ : (ZMod N)ˣ, pr (u δ • X.diam N l (δ : ZMod N).val f) :=
    map_sum (AddMonoidHom.mk' pr hpradd) _ _
  have hpr1 : pr (∑ δ : (ZMod N)ˣ, u δ • X.diam N l (δ : ZMod N).val f) 1 = M * pr f 1 := by
    rw [hprsum, Finset.sum_apply]
    have h1 : ∀ δ : (ZMod N)ˣ, pr (u δ • X.diam N l (δ : ZMod N).val f) 1 = pr f 1 := by
      intro δ
      rw [hprsmul, hdχ _ (hcopδ δ) f hfB, smul_smul, Pi.smul_apply, smul_eq_mul, ← map_mul, ← PadicInt.coe_mul,
        huχ, PadicInt.coe_one, map_one, one_mul]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hM]
  obtain ⟨tt, htt, v', u', hv', hu', htteq⟩ := GlobalTheory.LambdaValuationPowers.ZetaCoef.exists_isLamG ε hl2 hm (by omega : m ≤ n) hsm
  have hT : ∀ (δ : (ZMod N)ˣ) (i : ℕ), Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j (φδ δ) i)
      ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ' * (tt.val : Qbar l) * (l : Qbar l) ^ m * Qf δ i) +
        (j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ)))) :=
    fun δ i => hg δ s hs hsm (φδ δ) (hφδ δ) tt htt β t hβy hβ1 hmt i
  have hY1 : Cg n (Y m s y 1) (pr f 1) := by
    have h := hYb s y 1
    rw [hsm, inv_one, mul_one, ← hfpr] at h
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hrho.1, hrho.2, Matrix.vecHead, Matrix.vecTail] using h
  set Cs : Qbar l := ∑ i ∈ S, ∑ δ : (ZMod N)ˣ, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * algebraMap ℤ_[l] (Qbar l) (u δ) *
      (j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ))) with hCs
  have hlm : ‖(l : Qbar l) ^ m‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)) (by omega)
  have hMle : ‖M‖ ≤ 1 := by
    have := GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le (l := l) ((Fintype.card (ZMod N)ˣ : ℕ) : ℤ_[l])
    simpa [hM] using this
  have hsA : ∀ w ∈ A, s w ∈ A := by
    intro w hw
    have h1 := hs.2 w ((A.valuation_le_one_iff w).2 hw)
    have h2 : s w - w ∈ A := (A.valuation_le_one_iff _).1 h1.le
    simpa using A.add_mem _ _ h2 hw
  have hDle : ∀ (δ : (ZMod N)ˣ) (i : ℕ), ‖j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ))‖ ≤ 1 := by
    intro δ i
    rw [← map_sub]
    exact (hj _).1 (A.sub_mem (hsA _ (hgA δ _)) (hgA δ _))
  have hCle : ‖Cs‖ ≤ 1 := by
    refine hsumle _ _ _ zero_le_one fun i hi => hsumle _ _ _ zero_le_one fun δ _ => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le (hLk i hi)) (norm_nonneg _)
      (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le _)) (norm_nonneg _) (hDle δ i)
  have hPle : ‖M * pr f 1‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hMle (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hprO f hfB 1))
  have hYP : ‖M * Y m s y 1 - M * pr f 1‖ ≤ ‖(l : Qbar l) ^ m‖ :=
    hcgmul m M _ _ hMle (GlobalTheory.KummerEisensteinGalois.cg_mono (by omega) hY1)
  have hFP : ‖lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ) - per n * (M * pr f 1)‖ ≤ ‖(l : Qbar l) ^ m‖ := by
    have := GlobalTheory.KummerEisensteinGalois.cg_mono (by omega : m ≤ n - cL) hF
    rw [hpr1] at this
    exact this
  have hpp : ‖per n - per m‖ ≤ ‖(l : Qbar l) ^ m‖ :=
    GlobalTheory.LambdaValuationPowers.ZetaCoef.cg_per (fun q => (hper q).2.1) (by omega : m ≤ n)
  have hEν : ‖E * (l : Qbar l) ^ n‖ ≤ ‖(l : Qbar l) ^ m‖ := by
    have h1 := GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le hkE
    have h2 : E * (l : Qbar l) ^ n = ((l : Qbar l) ^ kE * E) * (l : Qbar l) ^ (m + cL) := by
      rw [hn]
      ring
    rw [h2, norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) h1) ?_
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) (GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one (l := l)).le (by omega)
  have hLc : ‖(l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ) -
      ((l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) + Cs)‖ ≤ ‖(l : Qbar l) ^ m‖ := by
    have hl : ∀ δ : (ZMod N)ˣ, lam (fun i => (l : Qbar l) ^ m * Qf δ i) =
        ∑ i ∈ S, lam (Pi.single i 1) * ((l : Qbar l) ^ m * Qf δ i) := fun δ => hS _
    have h1 : (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) =
        ∑ i ∈ S, ∑ δ : (ZMod N)ˣ, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * algebraMap ℤ_[l] (Qbar l) (u δ) *
          ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ' * (tt.val : Qbar l) * (l : Qbar l) ^ m * Qf δ i)) := by
      rw [hE, Finset.sum_congr rfl (fun δ _ => by rw [hl δ])]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    have hR : ∑ i ∈ S, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) *
        ((l : Qbar l) ^ c₁ * ((l : Qbar l) ^ c₀ * κ' * (tt.val : Qbar l) * (l : Qbar l) ^ m * Qf δ i) +
          (j (s ((g δ).coeff (i : ℚ))) - j ((g δ).coeff (i : ℚ)))) =
        (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) + Cs := by
      rw [h1, hCs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun δ _ => ?_
      ring
    have hL : (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ) =
        ∑ i ∈ S, ((l : Qbar l) ^ k * lam (Pi.single i 1)) * ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ i) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hcg : Cg n ((l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ))
        ((l : Qbar l) ^ c₁ * (l : Qbar l) ^ k * (E * (tt.val : Qbar l)) + Cs) := by
      rw [hL, ← hR]
      refine hcgsum _ _ _ n fun i hi => hcgmul n _ _ _ (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_pow_mul_le (hLk i hi)) ?_
      have h2 : Cg n ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ i)
          ((l : Qbar l) ^ c₁ * ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) * j ((φδ δ).coeff ((i : ℚ) / ((1 : ℕ) : ℚ)))) :=
        hcgmul n _ _ _ (hnpow c₁) (hΦc _)
      refine hcgtrans n _ _ _ h2 ?_
      rw [Finset.mul_sum]
      refine hcgsum _ _ _ n fun δ _ => ?_
      have h3 := hcgmul n (algebraMap ℤ_[l] (Qbar l) (u δ)) _ _ (GlobalTheory.LambdaValuationPowers.ZetaCoef.norm_algebraMap_le _) (hT δ i)
      have h4 : (l : Qbar l) ^ c₁ * (algebraMap ℤ_[l] (Qbar l) (u δ) * j ((φδ δ).coeff ((i : ℚ) / ((1 : ℕ) : ℚ)))) =
          algebraMap ℤ_[l] (Qbar l) (u δ) * ((l : Qbar l) ^ c₁ * GlobalTheory.KummerEisensteinGalois.seqN 1 j (φδ δ) i) := by
        unfold GlobalTheory.KummerEisensteinGalois.seqN
        ring
      rw [h4]
      exact h3
    exact GlobalTheory.KummerEisensteinGalois.cg_mono (by omega) hcg
  have hch := GlobalTheory.LambdaValuationPowers.ZetaCoef.chain (l := l) (Y := M * Y m s y 1) (P := M * pr f 1) (F := lam (GlobalTheory.KummerEisensteinGalois.seqN 1 j Φ))
    (pn := per n) (pm := per m) (E := E) (t := (tt.val : Qbar l)) (a := lamv l m s) (v := v') (u := u') (C := Cs)
    (lc := (l : Qbar l) ^ c₁ * (l : Qbar l) ^ k) (μ := (l : Qbar l) ^ m) (ν := (l : Qbar l) ^ n)
    hlm (by rw [← pow_add]; exact hnpow _) hPle hCle hv' hu' (hper n).1 (hper m).1 htteq hYP hFP hLc hpp hEν
  have hvM : ‖(l : Qbar l) ^ v / M‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hv (norm_nonneg _)
  have hsumeq : ∑ p : ↥S × (ZMod N)ˣ, (l : Qbar l) ^ v / M * (per n)⁻¹ * ((l : Qbar l) ^ k * lam (Pi.single (p.1 : ℕ) 1)) *
      algebraMap ℤ_[l] (Qbar l) (u p.2) * (j (s ((g p.2).coeff ((p.1 : ℕ) : ℚ))) - j ((g p.2).coeff ((p.1 : ℕ) : ℚ))) =
      (l : Qbar l) ^ v / M * (per n)⁻¹ * Cs := by
    rw [Fintype.sum_prod_type, hCs, Finset.mul_sum, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    ring
  have hsumχ : ∑ δ : (ZMod N)ˣ, (algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]))⁻¹ *
      lam (fun i => (l : Qbar l) ^ m * Qf δ i) =
      ∑ δ : (ZMod N)ˣ, algebraMap ℤ_[l] (Qbar l) (u δ) * lam (fun i => (l : Qbar l) ^ m * Qf δ i) := by
    simp only [hualg]
  unfold Cg
  rw [hsumeq, hsumχ]
  refine le_trans (le_of_eq ?_) (le_trans (mul_le_of_le_one_left (norm_nonneg _) hvM) hch)
  rw [← norm_mul]
  congr 1
  rw [hE]
  field_simp
  ring

end GlobalTheory.LambdaValuationPowers
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.HTLawZeta

theorem _root_.UpperTheory.V.Z.Kato.K5.top : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
    AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
    (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
    (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
    (∀ r s y, Y r s y 1 ∈ cf.O) →
  ∀ (χd : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χd δ)) → (∀ a b : ℕ, χd (a * b) = χd a * χd b) →
    (∀ a b : ℕ, a % N = b % N → χd a = χd b) → ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χd j pr cf lam →
  ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
  ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
    HTLawCsOfCoef A cf (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) j m₀ c₁
      (fun m ψ z => (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
        lam (GlobalTheory.KummerEisensteinGalois.up (l ^ m) (fun i => ∑ x : ZMod N, cw x *
          GlobalTheory.LambdaValuationPowers.chiProj N l m (2 * e + 1) ψ (fun n => ((χd n : ℤ_[l]) : Qbar l)) (c : ℤ) (d : ℤ) (x.val : ℤ) i))) :=
  law_of_inputs UpperTheory.V.Z.Kato.K5.hco GlobalTheory.LambdaValuationPowers.Smooth.exists_pres_smoothed

end GlobalTheory.HTLawZeta
end

theorem UpperTheory.V.Z.Kato.K5.smoothedZetaClass_hodgeTateLaw : UpperTheory.V.Z.Kato.Joint.SmoothedZetaClassHodgeTateLawStatement := UpperTheory.V.Z.Kato.K5.top
