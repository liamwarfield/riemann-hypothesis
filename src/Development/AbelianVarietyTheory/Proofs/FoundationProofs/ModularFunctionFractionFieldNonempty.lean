module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionAtInfinityOfSomeLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionAtInfinityOfSomeLevel
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_isExp : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f →
    ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  intro Ω _ ε f hf
  obtain ⟨N, w, hN, -, hq⟩ := hf
  obtain ⟨a, ha, hmem⟩ := hq 1
  choose b hb using fun n => (hmem n : a n ∈ ε.range)
  have hg : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    intro τ
    have := ha τ
    simp only [one_smul] at this
    simpa only [hb] using this
  obtain ⟨hg', hexg, -, -⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN hg
  obtain ⟨hD, hexD, hD0, -, -⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hring, -, hconst, -, hinv⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  have hDi := hinv DD hD hD0 hexD
  have hpow : ∀ k : ℕ, IsExp ε (DD⁻¹ ^ k) (hD⁻¹ ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hconst 1
      simp only [map_one, HahnSeries.C_one] at this
      rw [pow_zero, pow_zero]
      exact this
    | succ k ih =>
      simpa [pow_succ] using (hring _ _ _ _ ih hDi).2.2
  have hprod := (hring _ _ _ _ hexg (hpow w)).2.2
  refine ⟨hg' * hD⁻¹ ^ w, ?_⟩
  convert hprod using 1
  funext τ
  have := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  rw [inv_pow, mul_comm (DD τ ^ w), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ this), mul_one]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionAtInfinityOfSomeLevelStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspExpansionAtInfinity_of_someLevel : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f → ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  first | exact @GlobalTheory.FN.exists_isExp | exact GlobalTheory.FN.exists_isExp | (intros; apply GlobalTheory.FN.exists_isExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHom
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

variable {Ω : Type} [Field Ω] (ε : Ω →+* ℂ)

theorem exists_isExp_of_mem_ring (a : ring ε.range) : ∃ h : HahnSeries ℚ Ω, IsExp ε a h :=
  GlobalTheory.T.exists_cuspExpansionAtInfinity_of_someLevel Ω ε a (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2)

def expan (a : ring ε.range) : HahnSeries ℚ Ω := Classical.choose (exists_isExp_of_mem_ring ε a)

theorem isExp_expan (a : ring ε.range) : IsExp ε a (expan ε a) :=
  Classical.choose_spec (exists_isExp_of_mem_ring ε a)

theorem expan_eq_of_isExp {a : ring ε.range} {h : HahnSeries ℚ Ω} (ha : IsExp ε a h) : expan ε a = h :=
  (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 _ _ _ (isExp_expan ε a) ha

def expanHom : ring ε.range →+* HahnSeries ℚ Ω where
  toFun := expan ε
  map_one' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 1
    have e1 : ((1 : ring ε.range) : ℍ → ℂ) = fun _ => ε 1 := by ext; simp
    rw [e1]; simpa using h
  map_mul' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.2
    simpa using h
  map_zero' := by
    apply expan_eq_of_isExp
    have h := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.1 0
    have e0 : ((0 : ring ε.range) : ℍ → ℂ) = fun _ => ε 0 := by ext; simp
    rw [e0]; simpa using h
  map_add' a b := by
    apply expan_eq_of_isExp
    have h := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).1
    simpa using h

theorem expanHom_injective : Function.Injective (expanHom ε) := by
  intro a b hab
  have hsub := ((GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).1 _ _ _ _ (isExp_expan ε a) (isExp_expan ε b)).2.1
  have h0 : expan ε a - expan ε b = 0 := sub_eq_zero.mpr hab
  rw [h0] at hsub
  have hmem : ((a - b : ring ε.range) : ℍ → ℂ) ∈ ring ε.range := (a - b).2
  have hin : InR ε.range ((a - b : ring ε.range) : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 hmem
  have hhol := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ε.range _ hin
  push_cast at hhol
  have := (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.2.2.1 _ hhol hsub
  exact Subtype.ext (sub_eq_zero.mp this)

theorem expansion_injective_ringHom :
    ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω,
      Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) :=
  fun _ _ ε => ⟨expanHom ε, expanHom_injective ε, isExp_expan ε⟩

end GlobalTheory.FN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHomStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_cuspExpansion_ringHom : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω, Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) := by
  first | exact @GlobalTheory.FN.expansion_injective_ringHom | exact GlobalTheory.FN.expansion_injective_ringHom | (intros; apply GlobalTheory.FN.expansion_injective_ringHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjugateModularFunctionSomeLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjugateModularFunctionSomeLevel
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_of_inR : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω) (f : ℍ → ℂ), InR ε.range f → ∃ f' : ℍ → ℂ, InR ε.range f' ∧ ∀ h h' : HahnSeries ℚ Ω, IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s f hf
  obtain ⟨N, w, hN, hLv⟩ := hf
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s
  have hgE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨s y, (hg y).symm⟩
  obtain ⟨d, hd⟩ := GlobalTheory.WpFam.exists_unit_zetaAct N g
  obtain ⟨f', hLv', hconj⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N d w f hgE hd hLv
  refine ⟨f', ⟨N, w, hN, hLv'⟩, ?_⟩
  intro h h' hh hh' r
  have h1 : dg d * redGL N 1 = redGL N 1 * dg d := by
    rw [GlobalTheory.WpFam.Act.redGL_one]; simp
  have hc := hconj 1 1 h1
  simp only [one_smul] at hc
  have hq := hLv.2 1
  simp only [one_smul] at hq
  exact GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingHom g N w f f' h h' hg hN hq hc hh hh' r

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjugateModularFunctionSomeLevelStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisConjugate_modularFunction_someLevel : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω) (f : ℍ → ℂ), InR ε.range f → ∃ f' : ℍ → ℂ, InR ε.range f' ∧ ∀ h h' : HahnSeries ℚ Ω, IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  first | exact @GlobalTheory.FN.exists_conj_of_inR | exact GlobalTheory.FN.exists_conj_of_inR | (intros; apply GlobalTheory.FN.exists_conj_of_inR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConj
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_coeff_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω),
    ∃ σ : GlobalTheory.FN.ring ε.range ≃+* GlobalTheory.FN.ring ε.range, ∀ (a : GlobalTheory.FN.ring ε.range) (h h' : HahnSeries ℚ Ω),
      IsExp ε a h → IsExp ε (σ a : GlobalTheory.FN.ring ε.range) h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s
  obtain ⟨e, he_inj, he⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1
  have key : ∀ t : Ω ≃+* Ω, ∃ c : ring ε.range → ring ε.range, ∀ a,
      (∀ r, (e (c a)).coeff r = t ((e a).coeff r)) ∧
      ∀ h h' : HahnSeries ℚ Ω, IsExp ε a h → IsExp ε (c a : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
    intro t
    have hex : ∀ a : ring ε.range, ∃ b : ring ε.range, ∀ h h' : HahnSeries ℚ Ω,
        IsExp ε a h → IsExp ε (b : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
      intro a
      obtain ⟨f', hf', hp⟩ := GlobalTheory.T.exists_galoisConjugate_modularFunction_someLevel Ω ε t a ((hmem a).1 a.2)
      exact ⟨⟨f', (hmem f').2 hf'⟩, hp⟩
    choose c hc using hex
    exact ⟨c, fun a => ⟨hc a (e a) (e (c a)) (he a) (he (c a)), hc a⟩⟩
  have mapc : ∀ t : Ω ≃+* Ω, ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω, ∀ h r, (Φ h).coeff r = t (h.coeff r) := by
    intro t
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω t.toRingHom 1 (fun _ => 1) one_pos rfl (by simp)
    exact ⟨Φ, fun h r => by simpa using hΦ h r⟩
  obtain ⟨c, hc⟩ := key s
  obtain ⟨d, hd⟩ := key s.symm
  obtain ⟨Φ, hΦ⟩ := mapc s
  have ec : ∀ a, e (c a) = Φ (e a) := fun a => by
    ext r
    rw [(hc a).1, hΦ]
  refine ⟨{ toFun := c, invFun := d, left_inv := ?_, right_inv := ?_, map_add' := ?_, map_mul' := ?_ },
    fun a h h' => (hc a).2 h h'⟩
  · intro a
    apply he_inj
    ext r
    rw [(hd _).1, (hc a).1]
    simp
  · intro a
    apply he_inj
    ext r
    rw [(hc _).1, (hd a).1]
    simp
  · intro a b
    apply he_inj
    simp only [map_mul, ec]
  · intro a b
    apply he_inj
    simp only [map_add (f := _), ec]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConjStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω), ∃ σ : GlobalTheory.FN.ring ε.range ≃+* GlobalTheory.FN.ring ε.range, ∀ (a : GlobalTheory.FN.ring ε.range) (h h' : HahnSeries ℚ Ω), IsExp ε a h → IsExp ε (σ a : GlobalTheory.FN.ring ε.range) h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  first | exact @GlobalTheory.FN.exists_ringEquiv_coeff_conj | exact GlobalTheory.FN.exists_ringEquiv_coeff_conj | (intros; apply GlobalTheory.FN.exists_ringEquiv_coeff_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomain
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem ring_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  intro E
  haveI : Nontrivial (GlobalTheory.FN.ring E) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) UpperHalfPlane.I) h
    simp at h1
  haveI : NoZeroDivisors (GlobalTheory.FN.ring E) := by
    refine ⟨fun {a b} hab => ?_⟩
    have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1
    have ha := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E a ((hmem a).1 a.2)
    have hb := GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver E b ((hmem b).1 b.2)
    have h0 : ∀ τ, (a : ℍ → ℂ) τ * (b : ℍ → ℂ) τ = 0 := by
      intro τ
      have := congrArg (fun x : GlobalTheory.FN.ring E => (x : ℍ → ℂ) τ) hab
      simpa using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff a b ha hb h0 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  exact NoZeroDivisors.to_isDomain _

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomainStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionRingOver_isDomain : ∀ E : Subring ℂ, IsDomain (GlobalTheory.FN.ring E) := by
  first | exact @GlobalTheory.FN.ring_isDomain | exact GlobalTheory.FN.ring_isDomain | (intros; apply GlobalTheory.FN.ring_isDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFun
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFun
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_mem_ring (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) {f : ℍ → ℂ} (hf : f ∈ ring E) :
    cmp g f ∈ ring E :=
  ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 _).2 (GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat E g f hE (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 f).1 hf))

noncomputable def cmpHom (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) : ring E →+* ring E where
  toFun a := ⟨cmp g a, cmp_mem_ring E g hE a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cmp_cmp_inv (g : GQ) (f : ℍ → ℂ) : cmp g (cmp g⁻¹ f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, inv_mul_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_inv_cmp (g : GQ) (f : ℍ → ℂ) : cmp g⁻¹ (cmp g f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, mul_inv_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_ringEquiv : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  intro E g hE
  refine ⟨{ cmpHom E g hE with
    invFun := cmpHom E g⁻¹ hE
    left_inv := fun a => Subtype.ext (cmp_inv_cmp g a)
    right_inv := fun a => Subtype.ext (cmp_cmp_inv g a) }, fun a => rfl⟩

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFunStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  first | exact @GlobalTheory.FN.cmp_ringEquiv | exact GlobalTheory.FN.cmp_ringEquiv | (intros; apply GlobalTheory.FN.cmp_ringEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMaps
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fraction_field_extension : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  intro Ω R L M _ _ _ _ _ _ G S c e sl ga A he hce hsl hA
  letI alg : Algebra Ω (FractionRing R) := ((algebraMap R (FractionRing R)).comp c).toAlgebra
  have hΩ : ∀ x, algebraMap Ω (FractionRing R) x = algebraMap R (FractionRing R) (c x) := fun _ => rfl
  let e0 : FractionRing R →+* L := IsFractionRing.lift he
  have he0 : ∀ a, e0 (algebraMap R (FractionRing R) a) = e a := fun a => IsFractionRing.lift_algebraMap he a
  have hcom : ∀ x, e0 (algebraMap Ω (FractionRing R) x) = algebraMap Ω L x := fun x => by
    rw [hΩ, he0, hce]
  let e' : FractionRing R →ₐ[Ω] L :=
    { e0 with commutes' := hcom }
  let s0 : G → FractionRing R ≃+* FractionRing R := fun g => IsFractionRing.ringEquivOfRingEquiv (sl g)
  have hs0 : ∀ g a, s0 g (algebraMap R (FractionRing R) a) = algebraMap R (FractionRing R) (sl g a) :=
    fun g a => IsFractionRing.ringEquivOfRingEquiv_algebraMap (sl g) a
  let sl' : G → FractionRing R ≃ₐ[Ω] FractionRing R := fun g =>
    AlgEquiv.ofRingEquiv (f := s0 g) (fun x => by rw [hΩ, hs0, hsl])
  let ga' : S → FractionRing R ≃+* FractionRing R := fun s => IsFractionRing.ringEquivOfRingEquiv (ga s)
  have hunit : ∀ y : nonZeroDivisors R, IsUnit (A y) := fun y =>
    hA y (nonZeroDivisors.ne_zero y.2)
  let A' : FractionRing R →+* M := IsLocalization.lift (M := nonZeroDivisors R) hunit
  refine ⟨FractionRing R, inferInstance, alg, algebraMap R (FractionRing R), e', sl', ga', A',
    IsFractionRing.injective R (FractionRing R), ?_, fun x => (hΩ x).symm, he0, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R f
    refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
    have hy' : algebraMap R (FractionRing R) y ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    rw [← hxy, div_mul_cancel₀ _ hy']
  · intro g a
    exact hs0 g a
  · intro s a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (ga s) a
  · intro a
    exact IsLocalization.lift_eq hunit a

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMapsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionField_extension_of_maps : ∀ (Ω R L M : Type) [Field Ω] [CommRing R] [IsDomain R] [Field L] [Algebra Ω L] [CommRing M] (G S : Type) (c : Ω →+* R) (e : R →+* L) (sl : G → R ≃+* R) (ga : S → R ≃+* R) (A : R →+* M), Function.Injective e → (∀ x, e (c x) = algebraMap Ω L x) → (∀ g x, sl g (c x) = c x) → (∀ a, a ≠ 0 → IsUnit (A a)) → ∃ (K : Type) (_ : Field K) (_ : Algebra Ω K) (io : R →+* K) (e' : K →ₐ[Ω] L) (sl' : G → K ≃ₐ[Ω] K) (ga' : S → K ≃+* K) (A' : K →+* M), Function.Injective io ∧ (∀ f : K, ∃ a b : R, b ≠ 0 ∧ f * io b = io a) ∧ (∀ x, io (c x) = algebraMap Ω K x) ∧ (∀ a, e' (io a) = e a) ∧ (∀ g a, sl' g (io a) = io (sl g a)) ∧ (∀ s a, ga' s (io a) = io (ga s a)) ∧ ∀ a, A' (io a) = A a := by
  first | exact @GlobalTheory.fraction_field_extension | exact GlobalTheory.fraction_field_extension | (intros; apply GlobalTheory.fraction_field_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ),
    Nonempty (Frac Ω ε) := by
  intro Ω _ _ _ ε
  classical
  haveI : IsDomain (ring ε.range) := GlobalTheory.T.modularFunctionRingOver_isDomain ε.range
  obtain ⟨hmem, hconst⟩ := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  obtain ⟨-, huniq, hC, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨e, he_inj, he_exp⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  obtain ⟨hexp_mem, -, -, -, -, -⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  obtain ⟨⟨G, hG⟩, hmd, -, -, hHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units

  let cst : Ω →+* ring ε.range :=
    { toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (funext fun _ => by simp)
      map_mul' := fun x y => Subtype.ext (funext fun _ => by simp)
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun x y => Subtype.ext (funext fun _ => by simp) }
  have hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x := fun _ => rfl
  have hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x := by
    intro x
    refine huniq _ _ _ (he_exp (cst x)) ?_
    simpa [hcst, HahnSeries.algebraMap_apply'] using hC x

  have hsl := fun g : GQ => GlobalTheory.T.exists_ringEquiv_compGLTwoPosRatFun ε.range g hexp_mem
  choose σ hσ using hsl
  have hslc : ∀ g x, σ g (cst x) = cst x := by
    intro g x
    apply Subtype.ext
    rw [hσ]
    rfl

  have hga := fun s : Ω ≃ₐ[ℚ] Ω => GlobalTheory.T.exists_ringEquiv_fn_ring_coeff_eq_apply Ω ε s.toRingEquiv
  choose τ hτ using hga

  let A : ring ε.range →+* Mero := G.comp (ring ε.range).subtype
  have hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) := fun a => hG a
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs :=
    fun a => (hmd _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ ((hmem _).1 a.2))
  have hAunit : ∀ a, a ≠ 0 → IsUnit (A a) := by
    intro a ha
    rw [hA]
    refine (hunit _ (hdiff a) ?_).2
    intro h0
    apply ha
    have h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero) := by
      rw [h0, ← hA, map_zero]
    have heq := hid _ _ (hdiff a) (hdiff 0) h0'
    apply Subtype.ext
    funext t
    have := heq t (hHs t)
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  obtain ⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩ :=
    GlobalTheory.T.exists_fractionField_extension_of_maps Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit
  refine ⟨{
    K := K
    fld := fK
    alg := aK
    io := io
    io_inj := hinj
    io_surj := hsurj
    io_c := fun x a ha => ?_
    exp := e'
    exp_io := fun a => ?_
    sl := sl'
    sl_io := fun g a a' ha => ?_
    gal := ga'
    gal_exp := fun s f r => ?_
    an := A'
    an_io := fun a => ?_ }⟩
  · have : a = cst x := Subtype.ext ha
    rw [this, hioc]
  · rw [he']
    exact he_exp a
  · rw [hsl']
    congr 1
    exact Subtype.ext ((hσ g a).trans ha.symm)
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)
    have hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r) := by
      intro h r
      have := hΦ h r
      simpa using this
    have key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a)) := by
      intro a
      rw [hga', he', he']
      ext r
      rw [hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']
      rfl
    obtain ⟨a, b, hb, hf⟩ := hsurj f
    have hib : io b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hf' : f = io a * (io b)⁻¹ := by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]
    have hfe : e' (ga' s f) = Φ (e' f) := by
      rw [hf']
      simp only [map_mul, map_inv₀, key]
    rw [hfe, hΦ']
  · rw [hA', hA]
    rfl

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonemptyStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Nonempty (Frac Ω ε) := by
  first | exact @GlobalTheory.FN.frac_nonempty | exact GlobalTheory.FN.frac_nonempty | (intros; apply GlobalTheory.FN.frac_nonempty <;> assumption)
end
