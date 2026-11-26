module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerValuationLowerBoundSumPowTwelve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSpMapComp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepTrivialAbove
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TrivAbove

variable {E : Type} [Field E] [NumberField E]

theorem one_coord' (w : HeightOneSpectrum (𝓞 E)) : (1 : Af E) w = 1 := rfl

theorem mul_coord' (x y : Af E) (w : HeightOneSpectrum (𝓞 E)) : (x * y) w = x w * y w := rfl

theorem inv_coord' (z : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) : (↑z⁻¹ : Af E) w = ((z : Af E) w)⁻¹ := by
  show (((coord w z)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
  rw [Units.val_inv_eq_inv_val, coe_coord]


open Classical in
theorem prod_single_coord (S : Finset (HeightOneSpectrum (𝓞 E)))
    (x : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (w' : HeightOneSpectrum (𝓞 E)) :
    ((∏ w ∈ S, single w (x w) : (Af E)ˣ) : Af E) w' = if w' ∈ S then (x w' : w'.adicCompletion E) else 1 := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Units.val_one, one_coord']; simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul, mul_coord', ih]
    by_cases h : w' = a
    · subst h; simp [ha, single_self]
    · rw [suppAt_single a (x a) w' h]; simp [h]

theorem mem_hatOUnits [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥) (z : (Af E)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((z : Af E) w - 1) <
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) :
    z ∈ hatOUnits c := by
  have key : ∀ z : Af E, (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z w - 1) ≤
      WithZero.exp (-(multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))) → z ∈ hatO c :=
    fun z h => (GlobalTheory.T.mem_completedOrder_iff_placewise E c hc z).2 ⟨1, one_mem _, fun w => by rw [one_coord', map_one], h⟩
  refine ⟨key _ fun w => (hz w).le, key _ fun w => ?_⟩
  have h1 : Valued.v ((z : Af E) w - 1) < Valued.v (1 : w.adicCompletion E) := by
    rw [map_one]
    exact (hz w).trans_le (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hv : Valued.v ((z : Af E) w) = 1 := by
    have := Valuation.map_eq_of_sub_lt _ h1
    rwa [map_one] at this
  have hz0 : (z : Af E) w ≠ 0 := by rw [← coe_coord]; exact (coord w z).ne_zero
  show Valued.v ((↑z⁻¹ : Af E) w - 1) ≤ _
  rw [inv_coord']
  have he : ((z : Af E) w)⁻¹ - 1 = -(((z : Af E) w - 1) * ((z : Af E) w)⁻¹) := by
    field_simp; ring
  rw [he, Valuation.map_neg, map_mul, map_inv₀, hv, inv_one, mul_one]
  exact (hz w).le

theorem exists_rep_trivial_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (l : ℕ),
    c ≠ ⊥ → l.Prime → ∀ q : PicO c, ∃ y : (Af E)ˣ, (QuotientGroup.mk y : PicO c) = q ∧
      ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1 := by
  intro E _ _ _ c l hc hl q
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | (l : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hl0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
    exact (Ideal.finite_factors hl0).subset fun w hw => Ideal.dvd_span_singleton.2 hw
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, ha, -⟩ := PI.FinOrdValD.WA.weakApprox_units hfin.toFinset (fun w => (coord w y0)⁻¹)
    (fun w => (multiplicity w.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) : ℤ))
  set A : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom a with hAdef
  set y1 : (Af E)ˣ := A * y0 with hy1
  set u : (Af E)ˣ := ∏ w ∈ hfin.toFinset, single w (coord w y1) with hudef
  have hA : A ∈ princ ⊔ hatOUnits c := Subgroup.mem_sup_left ⟨a, rfl⟩
  have hu : u ∈ princ ⊔ hatOUnits c := by
    refine Subgroup.mem_sup_right (mem_hatOUnits hc u fun w => ?_)
    rw [hudef, prod_single_coord]
    split_ifs with hw
    · rw [coe_coord, hy1, Units.val_mul, mul_coord']
      have hAw : (A : Af E) w = algebraMap E (w.adicCompletion E) (a : E) := rfl
      have := ha w hw
      rw [hAw]
      simpa [Units.val_inv_eq_inv_val, coe_coord] using this
    · rw [sub_self, map_zero]; exact WithZero.exp_pos.bot_lt
  refine ⟨y1 * u⁻¹, ?_, fun w hw => ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hy1, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff A).2 hA, (QuotientGroup.eq_one_iff u).2 hu, one_mul, inv_one, mul_one]
  · have hwT : w ∈ hfin.toFinset := hfin.mem_toFinset.2 hw
    rw [Units.val_mul, mul_coord', inv_coord', hudef, prod_single_coord, if_pos hwT, coe_coord]
    exact mul_inv_cancel₀ (by rw [← coe_coord]; exact (coord w y1).ne_zero)

end GlobalTheory.CMVal.TrivAbove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerValuationLowerBoundSumPowTwelveStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve : ∀ (l : ℕ), l.Prime → ∀ (r : ℝ) (J : Type) [Fintype J] (u x : J → ℂ), (∀ j, IntAt l (u j)) → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r (x j ^ 12)) → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r ((∑ j, u j * x j) ^ 12) := by
  first | exact @GlobalTheory.LatValSum.valGe_sum_pow_twelve | exact GlobalTheory.LatValSum.valGe_sum_pow_twelve | (intros; apply GlobalTheory.LatValSum.valGe_sum_pow_twelve <;> assumption)
end

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomRow

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem beta_eq_pow (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) {Ω : ℂ} (hΩ : Ω ^ 12 = latDisc Λ) (T : ℂ) :
    beta E d s κ Λ T = ((C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
  rw [beta, div_pow, ← pow_mul, mul_comm _ 12, pow_mul, hΩ]

theorem classTerm_rep [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)}
    (hc : c ≠ ⊥) {χ : HChar E} (hinf : HasInf χ φ (fun i => (κ i : ℤ) + s)) (htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1)
    {l : ℕ} (hl : l.Prime) (hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S)
    (y : (Af E)ˣ) (S : ℂ → ℂ) (hS : IsLatSum φ (2 * s) κ (lattice c y) S) :
    ∃ y' : (Af E)ˣ, OneOver l y' ∧ ∃ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' ∧ ∃ u : ℂ, IntAt l u ∧
      ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = u * S' 0 := by
  obtain ⟨y', hy', hone⟩ := GlobalTheory.CMVal.TrivAbove.exists_rep_trivial_above E c l hc hl (QuotientGroup.mk y)
  obtain ⟨S', hS'⟩ := hex y'
  refine ⟨y', hone, S', hS', ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹, ?_, ?_⟩
  · have hu := GlobalTheory.CMVal.value_unitAt E I φ hφ s κ c χ l hc hl hinf htriv y' fun w hw => by
      rw [hone w hw, map_one]
    exact (GlobalTheory.CMVal.LUnit.unitAt_inv hu).2.1
  · exact GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ c χ hinf htriv y y' S S' hy'.symm hS hS'

theorem toricDenominator (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hR : LatIntRam) (hU : LatIntUnr) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  intro E _ _ _ _ I _ d φ s hd hs
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  have hzc : IsClassZetaVals (2 * s) z := hz
  refine ⟨z, hzc, fun κ 𝔣 Λ χ hb hΛ hχ => ?_⟩
  have hUr : UnramFin E := hd.2.2.1
  have hφ : IsCMType φ := hd.2.2.2.2.2.2.1
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  intro l hl Q hQ hQl
  set c := condQ 𝔣 Q with hcdef
  have hc : c ≠ ⊥ := mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  have h0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hUr hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1 := fun u hu => h0 u (hatOUnits_mono hle hu)
  have hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := fun y =>
    GlobalTheory.CMVal.LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 c χ hUr hs hb
      (dvd_mul_right _ _) hc hχ.1 hχ.2.2.1 htriv y
  set x : ℂ → ℂ := fun T => (C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ with hxdef
  have hx : ∀ T, beta E d s κ Λ T = x T ^ 12 := fun T => beta_eq_pow d s κ Λ hΩ T
  have hxmul : ∀ u T, x (u * T) = u * x T := fun u T => by simp only [hxdef]; ring

  have hlat : ∀ y' : (Af E)ˣ, OneOver l y' → ∀ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (x (S' 0) ^ 12) := fun y' hy' S' hS' => by
    rw [← hx]
    by_cases h : c_vp 𝔣 l = 0
    · exact hU E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'
    · exact hR E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'

  have hterm : ∀ χ' : HChar E, HasInf χ' φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ' u = 1) →
      ∀ (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice c y) S →
      ∃ u w : ℂ, IntAt l u ∧ ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (w ^ 12) ∧
        x (((finPart χ' y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0) = u * w := by
    intro χ' hinf' htriv' y S hS
    obtain ⟨y', hy', S', hS', u, hu, e⟩ := classTerm_rep hφ hc hinf' htriv' hl hex y S hS
    exact ⟨u, x (S' 0), hu, hlat y' hy' S' hS', by rw [e, hxmul]⟩
  refine ⟨fun y T ⟨S, hS, hT⟩ => ?_, fun ψ T hψ ⟨hfin, S, hS, hT⟩ => ?_⟩
  · obtain ⟨u, w, hu, hw, e⟩ := hterm χ hχ.2.2.1 htriv y S hS
    have := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) Unit (fun _ => u) (fun _ => w) (fun _ => hu) (fun _ => hw)
    rw [hx, hT, e]
    simpa using this
  · have hinf' : HasInf (χ * ψ) φ (fun i => (κ i : ℤ) + s) := hχ.2.2.1.mul_triv hψ.1
    have htriv' : ∀ u ∈ hatOUnits c, finPart (χ * ψ) u = 1 := fun u hu => by
      show finPart χ u * finPart ψ u = 1
      rw [htriv u hu, hψ.2 u hu, one_mul]
    have := Fintype.ofFinite (PicO c)
    choose u w hu hw e using fun q : PicO c => hterm (χ * ψ) hinf' htriv' q.out (S q) (hS q)
    have key := GlobalTheory.T.powerValuationLowerBound_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) (PicO c) u w hu hw
    rw [hx, hT, finsum_eq_sum_of_fintype]
    have : x (∑ q, ((finPart (χ * ψ) q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) = ∑ q, u q * w q := by
      rw [← Finset.sum_congr rfl fun q _ => e q]
      simp only [hxdef, Finset.mul_sum, Finset.sum_div]
    rw [this]
    exact key

end GlobalTheory.ToricDenomRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabEqStabilizer
noncomputable section

namespace GlobalTheory.LKCount

def LeftCosets {Γ G : Type} [Group Γ] [Group G] (_ι : Γ →* G) (K : Subgroup G) : Type := G ⧸ K

namespace LeftCosets

variable {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (K : Subgroup G)

instance : MulAction Γ (LeftCosets ι K) := MulAction.compHom (G ⧸ K) ι

def mk (x : G) : LeftCosets ι K := ((x : G ⧸ K) : G ⧸ K)

def rep (y : LeftCosets ι K) : G := Quotient.out (y : G ⧸ K)

variable {ι K}

theorem mk_rep (y : LeftCosets ι K) : mk ι K (rep ι K y) = y :=
  QuotientGroup.out_eq' (s := K) (y : G ⧸ K)

theorem mk_eq_mk {x y : G} : mk ι K x = mk ι K y ↔ x⁻¹ * y ∈ K :=
  QuotientGroup.eq

theorem smul_mk (η : Γ) (x : G) : η • mk ι K x = mk ι K (ι η * x) := rfl

theorem rep_mk (x : G) : ∃ k ∈ K, rep ι K (mk ι K x) = x * k := by
  have h : mk ι K x = mk ι K (rep ι K (mk ι K x)) := (mk_rep _).symm
  rw [mk_eq_mk] at h
  exact ⟨_, h, by group⟩

theorem mem_map_conj {x g : G} : g ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem stabilizer_mk (x : G) :
    MulAction.stabilizer Γ (mk ι K x) = (K.map (MulAut.conj x).toMonoidHom).comap ι := by
  ext η
  rw [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_mk, Subgroup.mem_comap, mem_map_conj]
  constructor
  · intro h
    have := K.inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := K.inv_mem h
    simpa [mul_assoc] using this

end LeftCosets

section Terms

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

theorem stab_eq_stabilizer (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = MulAction.stabilizer Γ (LeftCosets.mk (ι₁.prod ι₂) (K₁.prod K₂) x) := by
  rw [LeftCosets.stabilizer_mk]
  ext η
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, LeftCosets.mem_map_conj, Subgroup.mem_prod,
    MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

end Terms

end GlobalTheory.LKCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.HCFct

theorem exists_interp {K : Type} (W : Submodule ℂ (K → ℂ)) (hW : FiniteDimensional ℂ W) :
    ∃ (s : Finset K) (b : s → W), ∀ w ∈ W, ∀ k, w k = ∑ i : s, w i.1 * (b i).1 k := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.finiteDim_functions_detected_by_finset K W hW
  let ev : W →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun i =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) i.1).comp W.subtype
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hs w.1 w.2 fun k hk => congrFun hw ⟨k, hk⟩)
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective ev hev
  refine ⟨s, fun i => ψ (fun j => if i = j then 1 else 0), fun w hw k => ?_⟩
  have e1 : (⟨w, hw⟩ : W) = ψ (ev ⟨w, hw⟩) := (LinearMap.congr_fun hψ _).symm
  rw [LinearMap.pi_apply_eq_sum_univ ψ (ev ⟨w, hw⟩)] at e1
  have e2 := congrArg (fun u : W => u.1 k) e1
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ev,
    LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using e2

theorem constTerm_cptTranslate_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ W := by
  intro E _ _ _ a L W hW X N r _ _ μ 𝓕 hμ h𝓕 _ φ hφ g
  have hP : Continuous φ.1 ∧ (∀ γ h, φ.1 (ratGL E a γ * h) = φ.1 h) ∧
      ∀ h, (fun k : Kinf E a => φ.1 (h * infGL E a (Unitary.toUnits k))) ∈ W := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left, fun h => hx.2.2.1 h⟩
    | zero => exact ⟨continuous_const, fun _ _ => rfl, fun _ => W.zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2.1 γ h) (hy.2.1 γ h),
        fun h => W.add_mem (hx.2.2 h) (hy.2.2 h)⟩
    | smul c x _ hx =>
      exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2.1 γ h), fun h => W.smul_mem c (hx.2.2 h)⟩
  obtain ⟨hc, hl, hK⟩ := hP
  obtain ⟨s, b, hb⟩ := exists_interp W hW
  haveI := hμ
  have hint : ∀ h, IntegrableOn (fun x => φ.1 (unip x * h)) 𝓕 μ := fun h =>
    CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 h
  have hpt : ∀ k (x : BlockIx a r → Ad E), φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) =
      ∑ i : s, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) * (b i).1 k := fun k x => by
    have := hb _ (hK (unip x * g)) k
    simpa only [mul_assoc] using this
  have e : (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) =
      ∑ i : s, (∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) ∂μ) • (b i).1 := by
    funext k
    simp only [hpt k]
    rw [integral_finsetSum _ fun i _ => (hint _).mul_const _]
    simp only [integral_mul_const, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact W.sum_mem fun i _ => W.smul_mem _ (b i).2

end GlobalTheory.HCFct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFiniteStatement
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_measure_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ W := by
  first | exact @GlobalTheory.HCFct.constTerm_cptTranslate_mem | exact GlobalTheory.HCFct.constTerm_cptTranslate_mem | (intros; apply GlobalTheory.HCFct.constTerm_cptTranslate_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevTrans

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem frGL_conj {n : ℕ} (β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (u y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (β' * intGL F E n u * β⁻¹) * frGL β y * (β' * intGL F E n u * β⁻¹)⁻¹ = frGL β' (u * y * u⁻¹) := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

theorem transport {n n' : ℕ} (h : n = n') (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (β' x' : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (u : GL (Fin n') (Formalism.L2.Herm.intAf F E))
    (j : Matrix (Fin n') (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hc : HMul.hMul x'.val j = HMul.hMul j x.val)
    (hf : HMul.hMul j β.val = (β' * intGL F E n' u).val.submatrix id (Fin.cast h))
    (Pg : Finset (Pl E)) (hu : ∀ PP ∈ Pg, Formalism.UG.bc (resS F PP) u = 1) (r t : ℕ) (hr : r ≤ n) (hr' : r ≤ n') :
    (x ∈ St β ↔ x' ∈ St β') ∧ (x ∈ St β → ∀ PP ∈ Pg,
      (redFn β PP x ∈ blockTri (blkOf r t) ↔ redFn β' PP x' ∈ blockTri (blkOf r t)) ∧
        upperLeftBlock hr' (redFn β' PP x') = upperLeftBlock hr (redFn β PP x)) := by
  subst h
  have hf' : j * β.val = (β' * intGL F E n u).val := hf
  set J : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := β' * intGL F E n u * β⁻¹ with hJ
  have hj : j = J.val := by
    rw [hJ, Units.val_mul, ← hf', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hx : x' = J * x * J⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    show x'.val * J.val = J.val * x.val
    rw [← hj]
    exact hc
  have key : ∀ y, J * frGL β y * J⁻¹ = frGL β' (u * y * u⁻¹) := frGL_conj β β' u
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨u * y * u⁻¹, by rw [hx, key]⟩
  · rintro ⟨y, hy⟩
    refine ⟨u⁻¹ * y * u, ?_⟩
    have h1 := key (u⁻¹ * y * u)
    rw [show u * (u⁻¹ * y * u) * u⁻¹ = y by group, hy, hx] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · rintro ⟨y, rfl⟩ PP hP
    have h2 : redFn β' PP x' = redFn β PP (frGL β y) := by
      rw [hx, key, redFn_frGL, redFn_frGL, map_mul, map_mul, map_inv, hu PP hP]
      simp
    rw [h2]
    exact ⟨Iff.rfl, rfl⟩

end General

variable {D : D7}

theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

theorem finE_unitary (V : HSp D) (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have h2 := congrArg (fun M => Matrix.map M ((swapAE D).comp (finPart D))) h
  simp only [Matrix.map_mul] at h2
  show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _
  rw [show (finE V g).1 = (Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D)) from rfl]
  have e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map ((swapAE D).comp (finPart D)) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D))) := by
    ext i j
    exact fin_cA _
  rw [e1] at h2
  exact h2

theorem levtrans : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  intro D V V' β β' r t hr hr' Pg χ χ' j Φ hI κ
  obtain ⟨h, u, hf, hu⟩ := hI.frame
  obtain ⟨h1, h2⟩ := transport h β (finE V (κ : GA D V)) β' (finE V' (Φ κ : GA D V')) u j (hI.conj κ) hf Pg hu r t hr hr'
  refine ⟨?_, fun hm => ?_⟩
  · rw [mem_parLev, mem_parLev]
    constructor
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.1 a, fun PP hP => ((h2 a PP hP).1).1 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.2 a, fun PP hP => ((h2 (h1.2 a) PP hP).1).2 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
  · funext PP
    exact (h2 (parLev_St hm) PP.1 PP.2).2

end GlobalTheory.LevTrans

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_matches_parahoric_levels : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  exact @GlobalTheory.LevTrans.levtrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjAGphiEqSum
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacProj

theorem mem_vset {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (Λ : Formalism.L2.Pj.GenLat E n) (hU : Λ.Unimod) (hfg : Λ.La.FG) : Λ.La ∈ Vset E n 1 := by
  have hU' := (GenLatCmp.unimod_iff Λ.La).1 hU
  obtain ⟨N, hN, h⟩ := TensLat.exists_mul_le (B := stdL E n) (B' := Λ.La)
    (Submodule.fg_span (Set.finite_range _)) (DualFamily.span_eq_top Λ.La hfg fun x => (hU' x).2)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {N}))
  have h4 : ∀ u ∈ stdL E n, ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) • u ∈ Λ.La := fun u hu => by
    have e : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) = (a : E) * (N : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      rw [map_mul, map_natCast] at this
      exact this.symm
    rw [e, mul_smul]
    exact TensLat.int_smul_mem a.isIntegral_coe (h u hu)
  refine ⟨hfg, hU', _, Nat.pos_of_ne_zero ?_, Nat.coprime_one_right _,
    GenLatCmp.smul_mem_std hU' h4, h4⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hN

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem heisG_sum {ι : Type} (y : Matrix (Fin n) (Fin r) E) (s : Finset ι) (f : ι → TF n g) :
    heisG X bas y (∑ i ∈ s, f i) = ∑ i ∈ s, heisG X bas y (f i) := by
  funext x; simp [heisG, heisS, Finset.sum_mul]

theorem rho_eq_iff (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    {a b : Matrix (Fin n) (Fin r) E} (ha : a ∈ A) (hb : b ∈ A) :
    epsW X w a • heisG X bas a v = epsW X w b • heisG X bas b v ↔ -a + b ∈ A' := by
  have hfix : ∀ y, epsW X w y • heisG X bas y v = v ↔ y ∈ A' := by
    refine fun y => ⟨fun h => ?_, hv.2.2 y⟩
    by_contra hy
    have := hA'.ip_eq_zero idx hs hn hv hy
    rw [h, hv.2.1] at this
    exact one_ne_zero this
  rw [← hfix, ← hA.rho_rho idx hs hn (A.neg_mem ha) hb hv.1]
  constructor
  · intro h
    rw [← h, hA.rho_rho idx hs hn (A.neg_mem ha) ha hv.1, neg_add_cancel,
      TensVac.rho_zero idx hs hn hv.1]
  · intro h
    conv_lhs => rw [← h]
    rw [hA.rho_rho idx hs hn ha (A.neg_mem ha) (TensVac.rho_sb idx hs hn b hv.1), add_neg_cancel,
      TensVac.rho_zero idx hs hn (TensVac.rho_sb idx hs hn b hv.1)]

theorem proj_eq (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    (R : Finset (Matrix (Fin n) (Fin r) E)) (hR : ∀ y ∈ R, y ∈ A)
    (hR' : ∀ y ∈ A, ∃! y', y' ∈ R ∧ y - y' ∈ A') :
    R.card = A'.relIndex A ∧
      projA X bas w A v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧
      IsVac X bas w A ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w A v) := by
  set f : Matrix (Fin n) (Fin r) E → TF n g := fun y => epsW X w y • heisG X bas y v with hf
  have hiff : ∀ a ∈ A, ∀ b ∈ A, f a = f b ↔ -a + b ∈ A' := fun a ha b hb =>
    rho_eq_iff idx hs hn hA hA' hv ha hb
  have hinj : Set.InjOn f R := fun a ha b hb h => by
    have h1 := (hiff a (hR a ha) b (hR b hb)).1 h
    rw [neg_add_eq_sub] at h1
    exact (hR' b (hR b hb)).unique ⟨ha, h1⟩ ⟨hb, by rw [sub_self]; exact A'.zero_mem⟩
  have him : f '' A = f '' R := by
    refine Set.Subset.antisymm ?_ (Set.image_mono fun y hy => hR y hy)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, ⟨hb, h⟩, -⟩ := hR' a ha
    exact ⟨b, hb, (hiff b (hR b hb) a ha).2 (by rwa [neg_add_eq_sub])⟩
  have hc : (f '' A).ncard = R.card := by
    rw [him, hinj.ncard_image, Set.ncard_coe_finset]
  have hidx : R.card = A'.relIndex A := hc.symm.trans (TensVac.ncard_image_eq f hiff)
  refine ⟨hidx, ?_, ?_⟩
  · have h1 : ∑ᶠ ψ ∈ f '' R, ψ = ∑ y ∈ R, f y :=
      (finsum_mem_image (f := fun ψ : TF n g => ψ) hinj).trans (finsum_mem_coe_finset _ _)
    rw [projA, ← hf, hc, him, h1]
  · obtain ⟨u, hu, -⟩ := hA.vac hs
    have hov := hA.overlap idx hs hn hA' hu hv
    rw [(hA.proj idx hs hn hv.1 hu).2, smul_smul]
    set a := (Real.sqrt (R.card : ℝ) : ℂ) * SW.ip v u with ha
    have hn1 : ‖a‖ ^ 2 = 1 := by
      rw [ha, TensVac.ip_conj hu.1 hv.1, norm_mul, Complex.norm_conj, Complex.norm_real, mul_pow,
        Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _), hidx, hov]
    refine ⟨TensVac.sb_smul a hu.1, ?_, fun y hy => ?_⟩
    · rw [TensVac.ip_smul_left a hu.1 (TensVac.sb_smul a hu.1), TensVac.ip_smul_right a hu.1 hu.1,
        hu.2.1, _root_.mul_one, Complex.mul_conj']
      exact_mod_cast hn1
    · rw [TensVac.heisG_smul, smul_comm, hu.2.2 y hy]

end

theorem projA_gphi_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ (Λ₀ Λ : Formalism.L2.Pj.GenLat E n), Λ₀.Unimod → Λ.Unimod → Λ₀.La.FG → Λ.La.FG → ∀ v : TF n g, IsVac X bas w (tens Λ₀.La L) v → ∀ R : Finset (Matrix (Fin n) (Fin r) E), (∀ y ∈ R, y ∈ tens Λ.La L) → (∀ y ∈ tens Λ.La L, ∃! y', y' ∈ R ∧ y - y' ∈ tens Λ₀.La L) → R.card = ((Λ.La ⊓ Λ₀.La).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ r ∧ projA X bas w (tens Λ.La L) v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧ IsVac X bas w (tens Λ.La L) ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w (tens Λ.La L) v) ∧ ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E), gphi X bas w Λ.La L v c Y = ((R.card : ℂ))⁻¹ • ∑ q, ∑ y ∈ R, (c q * epsW X w y) • heisG X bas (Y q) (heisG X bas y v) := by
  intro E _ _ _ r g n X bas idx hs hn w hw hw1 L hL Λ₀ Λ hU₀ hU hf₀ hf v hv R hR hR'
  have h₀ := mem_vset Λ₀ hU₀ hf₀
  have h₁ := mem_vset Λ hU hf
  obtain ⟨a1, a2, a3, -, -, a4⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₁
  obtain ⟨b1, b2, b3, -⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₀
  obtain ⟨c1, c2, c3⟩ := proj_eq idx hs hn ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ hv R hR hR'
  refine ⟨?_, c2, c3, fun Q _ c Y => ?_⟩
  · rw [c1, a4 _ h₀, ← AddSubgroup.inf_relIndex_left]
    rfl
  · rw [gphi, finsum_eq_sum_of_fintype, c2]
    refine Eq.trans ?_ Finset.smul_sum.symm
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [TensVac.heisG_smul, heisG_sum, smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [TensVac.heisG_smul, smul_smul]

end GlobalTheory.AdTh.VacProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CplxOfFrame
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameCplx

theorem gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ (-Gᵀ) x = -(xᴴ * G.map τ * x)ᵀ := by
  ext a b
  simp only [FD.gram, hermC, FD.col, of_apply, Matrix.neg_apply, transpose_apply, Matrix.mul_apply, map_neg, map_apply,
    conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  simp_rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hermC_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) (v : Fin r → ℂ) :
    hermC τ (-Gᵀ) (FD.col x a) v = -((star v ᵥ* (G.map τ * x)) a) := by
  simp only [hermC, FD.col, Matrix.neg_apply, transpose_apply, Matrix.mul_apply, map_neg, map_apply, vecMul, dotProduct,
    Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  simp_rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

section lin
variable {r : ℕ} {G x S s : Matrix (Fin r) (Fin r) ℂ}

theorem isUnit_det (hS : S * S = 1) (hG : xᴴ * G * x = -S) : IsUnit x.det := by
  have h : (-(S * (xᴴ * G))) * x = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, hG, Matrix.mul_neg, neg_neg, hS]
  exact Matrix.isUnit_det_of_left_inverse h

theorem inv_mul_inv (hS : S * S = 1) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : x⁻¹ * s = -(S * x⁻¹) := by
  have hx := isUnit_det hS hG
  have : s = -(x * S) * x⁻¹ := by rw [← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  rw [this, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hx]

open scoped ComplexOrder in
theorem cartan (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) : IsCartanInv G s := by
  have hx := isUnit_det hS hG
  have hxH : IsUnit xᴴ.det := by rw [Matrix.det_conjTranspose]; exact hx.star
  have hs' : s = -(x * S * x⁻¹) := by rw [← Matrix.neg_mul, ← hs, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have hG' : G = -((x⁻¹)ᴴ * S * x⁻¹) := by
    rw [← Matrix.neg_mul, ← Matrix.mul_neg, ← hG, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc xᴴ,
      Matrix.nonsing_inv_mul_cancel_left _ _ hxH, Matrix.mul_nonsing_inv_cancel_right _ _ hx]
  have c1 : ∀ M : Matrix (Fin r) (Fin r) ℂ, x⁻¹ * (x * M) = M := fun M => Matrix.nonsing_inv_mul_cancel_left _ _ hx
  have c2 : ∀ M : Matrix (Fin r) (Fin r) ℂ, S * (S * M) = M := fun M => by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  have c3 : ∀ M : Matrix (Fin r) (Fin r) ℂ, xᴴ * ((x⁻¹)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hx, conjTranspose_one, Matrix.one_mul]
  have hGs : G * s = (x⁻¹)ᴴ * x⁻¹ := by
    rw [hG', hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs']; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, c1, c2]
    exact Matrix.mul_nonsing_inv _ hx
  · rw [Matrix.mul_assoc, hGs, hG', hs']
    simp only [conjTranspose_neg, conjTranspose_mul, hH, Matrix.neg_mul, Matrix.mul_assoc, c3]
  · rw [hGs]
    have hu : IsUnit x⁻¹ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hx)
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit hu)

theorem adj_inv (hS : S * S = 1) (hH : Sᴴ = S) (hG : xᴴ * G * x = -S) (hs : s * x = -(x * S)) :
    sᴴ * (G * x) = -(G * x * S) := by
  obtain ⟨h1, h2, -⟩ := cartan hS hH hG hs
  have : x = -(s * (x * S)) := by
    rw [← Matrix.mul_assoc, hs, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hS, Matrix.mul_one]
  calc sᴴ * (G * x) = -((sᴴ * G * s) * (x * S)) := by
        conv_lhs => rw [this]
        simp only [Matrix.mul_neg, Matrix.mul_assoc]
    _ = _ := by rw [h2, Matrix.mul_assoc]
end lin

theorem sgnM_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : sgnM X * sgnM X = 1 := by
  rw [sgnM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext a; unfold FD.sgn; split_ifs <;> simp

theorem sgnM_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : (sgnM X)ᴴ = sgnM X := by
  rw [sgnM, diagonal_conjTranspose]
  congr 1; funext a; simp

theorem per_cplx {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x s : Matrix (Fin r) (Fin r) ℂ) (hG : xᴴ * G.map τ * x = -sgnM X)
    (hs : s * x = -(x * sgnM X)) (v : Fin r → ℂ) (a : Fin r) :
    (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) (I • (s *ᵥ v)) else (x⁻¹ *ᵥ (I • (s *ᵥ v))) a) =
      I * (if (a : ℕ) < X.p0 then hermC τ (-Gᵀ) (FD.col x a) v else (x⁻¹ *ᵥ v) a) := by
  split_ifs with h
  · rw [hermC_eq, hermC_eq, star_smul, star_mulVec, smul_vecMul, vecMul_vecMul,
      adj_inv (sgnM_sq X) (sgnM_herm X) hG hs, vecMul_neg, ← vecMul_vecMul, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, vecMul_diagonal]
    simp [FD.sgn, h]
  · rw [mulVec_smul, mulVec_mulVec, inv_mul_inv (sgnM_sq X) hG hs, neg_mulVec, ← mulVec_mulVec, sgnM]
    simp only [Pi.smul_apply, Pi.neg_apply, mulVec_diagonal]
    simp [FD.sgn, h]


open scoped ComplexOrder in
theorem cplx_of_frame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧ (∀ τ, IsCartanInv (gramAt D V τ) 1) ∧ ∀ (τ : D.what₂.Tau) (u : Matrix (Fin W.rank) (Fin V.rank) ℂ), zOf θ V W hr X idx x (lineAt θ τ (cplxO 1 (s τ) u) 1) = I • zOf θ V W hr X idx x (lineAt θ τ u 1) := by
  intro D ψ θ V W r g hr X bas idx _ hθ hV _ hM _ x s hx hs
  subst hr
  have hGm : X.Gm = -(HSpace.gram W)ᵀ := hM.model.1
  have hG : ∀ τ : X.Ψ, (mat x τ)ᴴ * (HSpace.gram W).map τ.1 * mat x τ = -sgnM X := fun τ => by
    have h := hx τ
    rw [hGm, gram_eq] at h
    have h2 : (sgnM X)ᵀ = sgnM X := by rw [sgnM, diagonal_transpose]
    rw [← h2, ← h, transpose_neg, transpose_transpose, neg_neg]
  have hs' : ∀ (ρ : D.what₂.Tau) (τ : X.Ψ), τ.1 = tauE D ρ → s ρ * mat x τ = -(mat x τ * sgnM X) := hs
  refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ u => ?_⟩
  · have h := hG ⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩
    exact cartan (sgnM_sq X) (sgnM_herm X) h (hs' ρ _ rfl)
  · have : gramAt D V ρ = 1 := by
      rw [gramAt, hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this]
    refine ⟨by simp, by simp, ?_⟩
    rw [Matrix.mul_one]; exact Matrix.PosDef.one
  · have hL : ∀ z : Matrix (Fin W.rank) (Fin V.rank) ℂ, IsLineAt θ ρ z (lineAt θ ρ z) := fun z =>
      Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ ρ z)
    funext b j
    simp only [zOf, Pi.smul_apply, smul_eq_mul, perC]
    obtain ⟨τ, a⟩ := idx j
    have hτ : ∃ ρ', τ.1 = tauE D ρ' := (hM.psi _).1 τ.2
    simp only [realM, dif_pos hτ, (hL _).2.2, hGm]
    by_cases e : hτ.choose = ρ
    · simp only [if_pos e]
      have := per_cplx X τ.1 (HSpace.gram W) (mat x τ) (s ρ) (hG τ) (hs' ρ τ (e ▸ hτ.choose_spec)) (fun k => u k b) a
      convert this using 3 <;> (try funext k) <;> simp [cplxO, Matrix.mul_apply, mulVec, dotProduct]
    · simp only [if_neg e]
      simp [hermC, mulVec, dotProduct]

end GlobalTheory.FrameCplx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdempotentCoefficientConjugate
noncomputable section

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

namespace GlobalTheory.GoodIdemFlip

section Local

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ}

def invParam (s : SSParam p K r) : SSParam p K r := ⟨s.1, fun c => (s.2 c)⁻¹⟩

theorem cycChar_invParam (s : SSParam p K r) (c : Cyc (invParam s).1) : cycChar (invParam s) c = (cycChar s c)⁻¹ := by
  ext x; rfl

theorem rootChar_invParam (s : SSParam p K r) (x : Σ c : Cyc (invParam s).1, Fin (cycLen (invParam s).1 c)) :
    rootChar (invParam s) x = (rootChar s x)⁻¹ := by
  have h : rootChar (invParam s) x = (cycChar s x.1)⁻¹ ^ (p ^ x.2.val) := by
    rw [← cycChar_invParam s x.1]; rfl
  rw [h, inv_pow]
  rfl

theorem congrMod_inv {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b⁻¹ ↔ CongrMod l a b := by
  have : a⁻¹ / b⁻¹ = (a / b)⁻¹ := by rw [inv_div_inv, inv_div]
  simp only [CongrMod, this, inv_pow, inv_eq_one]

theorem congrMod_inv_left {A : Type} [CommGroup A] (l : ℕ) (a b : A) : CongrMod l a⁻¹ b ↔ CongrMod l a b⁻¹ := by
  rw [← congrMod_inv, inv_inv]

theorem inv_comp_baseNorm (χ : (ZMod p)ˣ →* Kˣ) (D : ℕ) :
    χ⁻¹.comp (baseNorm p D) = (χ.comp (baseNorm p D))⁻¹ := by
  ext x; rfl

theorem goodAt_flip {ι J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ)) (s s' : ι → SSParam p K r)
    (h : ∀ v, s' v = s v ∨ s' v = invParam (s v)) (hs : GoodAt χ s) : GoodAt χ s' := by
  obtain ⟨h1, h2, ⟨h3, h3'⟩, h4, v5, h5⟩ := hs
  refine ⟨fun v => ?_, fun l hl hl' v => ?_, ⟨fun l hl hl' v => ?_, fun v => ?_⟩, ?_, v5, ?_⟩
  · rcases h v with e | e <;> rw [e]
    · exact h1 v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam] at hxy
      exact h1 v (inv_injective hxy)
  · rcases h v with e | e <;> rw [e]
    · exact h2 l hl hl' v
    · intro x y hxy
      rw [rootChar_invParam, rootChar_invParam, congrMod_inv]
      exact h2 l hl hl' v x y hxy
  · rcases h v with e | e <;> rw [e]
    · exact h3 l hl hl' v
    · intro j c
      have := h3 l hl hl' v j c
      rw [inv_comp_baseNorm] at this
      rw [cycChar_invParam, inv_comp_baseNorm, congrMod_inv, congrMod_inv_left]
      exact this.symm
  · rcases h v with e | e <;> rw [e]
    · exact h3' v
    · intro j x
      have := h3' v j x
      rw [inv_comp_baseNorm] at this
      rw [rootChar_invParam, inv_comp_baseNorm, Ne, Ne, inv_inj, inv_eq_iff_eq_inv]
      exact this.symm
  · rintro ⟨a, ha, ha', hA⟩
    refine h4 ⟨a, ha, ha', fun v => ?_⟩
    have := hA v
    rcases h v with e | e <;> rw [e] at this <;> exact this
  · rcases h v5 with e | e <;> rw [e] <;> exact h5

theorem isConj_inv_inv {G : Type} [Group G] {a b : G} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by group⟩

end Local

section Global

variable {R : Ranks} {H : Host R} {K : Type} [Field K]


open Classical in
def flipAt (S : Set (Sq H)) (x : LevelGroup H) : LevelGroup H := fun v => if v ∈ S then (x v)⁻¹ else x v


open Classical in
def flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) : ∀ v : Sq H, SSParam (H.g v.1) K R.r :=
  fun v => if v ∈ S then invParam (s v) else s v

theorem flipAt_flipAt (S : Set (Sq H)) (x : LevelGroup H) : flipAt S (flipAt S x) = x := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

theorem flipAt_one (S : Set (Sq H)) : flipAt S 1 = 1 := by
  funext v
  by_cases hv : v ∈ S <;> simp [flipAt, hv]

theorem tupleChar_flipParam (S : Set (Sq H)) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) :
    tupleChar (flipParam S s) = tupleChar s ∘ flipAt S := by
  funext x
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ S
  · simp only [flipParam, flipAt, if_pos hv]
    exact (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).2 (x v)
  · simp only [flipParam, flipAt, if_neg hv]

theorem tupleChar_congr (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) {x y : LevelGroup H}
    (h : ∀ v, IsConj (x v) (y v)) : tupleChar s x = tupleChar s y :=
  Finset.prod_congr rfl fun v _ => (GlobalTheory.TypeCharacterConjugateInverse.typeChar_conj_inv _ K _ (s v)).1 _ _ (h v)

theorem comp_flipAt_mem (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (S : Set (Sq H)) {τ : LevelGroup H → K}
    (hτ : τ ∈ goodTypes om) : τ ∘ flipAt S ∈ goodTypes om := by
  obtain ⟨s, hs, rfl⟩ := hτ
  refine ⟨flipParam S s, fun i => goodAt_flip _ _ _ (fun w => ?_) (hs i), tupleChar_flipParam S s⟩
  by_cases hv : (⟨i, w⟩ : Sq H) ∈ S
  · exact Or.inr (if_pos hv)
  · exact Or.inl (if_neg hv)

end Global

theorem coeff_goodIdem_flip (R : Ranks) (H : Host R) (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* ℂˣ) (S : Set (Sq H))
    (x y : LevelGroup H) (h1 : ∀ v ∈ S, IsConj (x v)⁻¹ (y v)) (h2 : ∀ v ∉ S, IsConj (x v) (y v)) :
    (goodIdem om).coeff y = (goodIdem om).coeff x := by
  simp only [goodIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, GlobalTheory.SumWCompare.coeff_centralIdem]
  have inv : ∀ τ : LevelGroup H → ℂ, (τ ∘ flipAt S) ∘ flipAt S = τ := fun τ => by
    funext z; simp [flipAt_flipAt]
  refine Finset.sum_nbij' (fun τ => τ ∘ flipAt S) (fun τ => τ ∘ flipAt S) ?_ ?_ (fun τ _ => inv τ) (fun τ _ => inv τ) ?_
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    exact (Set.Finite.mem_toFinset _).2 (comp_flipAt_mem om S ((Set.Finite.mem_toFinset _).1 hτ))
  · intro τ hτ
    obtain ⟨s, -, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
    have key : tupleChar s y⁻¹ = tupleChar s (flipAt S x⁻¹) := by
      refine tupleChar_congr s fun v => ?_
      by_cases hv : v ∈ S
      · simp only [flipAt, if_pos hv, Pi.inv_apply]
        exact isConj_inv_inv (h1 v hv).symm
      · simp only [flipAt, if_neg hv, Pi.inv_apply]
        exact isConj_inv_inv (h2 v hv).symm
    rw [Function.comp_apply, Function.comp_apply, flipAt_one, key]

end GlobalTheory.GoodIdemFlip
end
end
