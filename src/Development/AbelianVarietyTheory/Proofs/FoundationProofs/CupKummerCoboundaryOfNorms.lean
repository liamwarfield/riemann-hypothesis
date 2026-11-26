module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycle
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem hilbert90_locallyConstant_cocycle :
    ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
      IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) →
        ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  intro K Ω _ _ _ _ _ w hw hc
  have h1 : w 1 = 1 := by
    apply Units.ext
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    have h' : ((w 1 : Ωˣ) : Ω) * 1 = (w 1 : Ω) * (w 1 : Ω) := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ (w 1).ne_zero h').symm
  have hopen : IsOpen (w ⁻¹' {1}) := hw _
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 (hopen.mem_nhds (by simp [h1]))
  haveI := hfin
  obtain ⟨β, hβ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_of_cocycle (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) (fun h => w h.1) E
    (fun h hh => hE hh) (fun g h => Units.ext (by simp [hc]))
  refine ⟨β, fun g => ?_⟩
  have := congrArg Units.val (hβ ⟨g, Subgroup.mem_top g⟩)
  simpa [div_eq_mul_inv] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycleStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_div_of_locallyConstant_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
  IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) → ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  first | exact @GlobalTheory.hilbert90_locallyConstant_cocycle | exact GlobalTheory.hilbert90_locallyConstant_cocycle | (intros; apply GlobalTheory.hilbert90_locallyConstant_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycle
open GlobalTheory.NeedB Polynomial

noncomputable section

open IntermediateField

namespace GlobalTheory.Hilbert90CupCoboundary

theorem isLocallyConstant_eval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (τ : Ω) : IsLocallyConstant (fun g : Ω ≃ₐ[K] Ω => g τ) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮τ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral τ)
  have hopen : IsOpen ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮τ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfτ : (g⁻¹ * g') τ = τ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' τ
        (IntermediateField.mem_adjoin_simple_self K τ)
    have e : g' = g * (g⁻¹ * g') := by group
    show g' τ = g τ
    rw [e, AlgEquiv.mul_apply, hfτ]

theorem zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN0 hζ hfix c v hv hcoc
  classical
  haveI : NeZero N := ⟨by omega⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let u : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => v g ^ N
  have hu_lc : IsLocallyConstant u := hv.comp (fun x : Ωˣ => x ^ N)
  have hu_coc : ∀ g h, ((u (g * h) : Ωˣ) : Ω) = u g * g (u h) := by
    intro g h
    simp only [u, Units.val_pow_eq_pow_val, map_pow]
    rw [← mul_pow, hcoc g h, mul_pow, ← pow_mul, mul_comm (c g h).val N, pow_mul, hζ.pow_eq_one,
      one_pow, one_mul]
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_eq_div_of_locallyConstant_cocycle K Ω u hu_lc hu_coc
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_pow_nat_eq (t : Ω) hN0
  have ht0 : (t : Ω) ≠ 0 := t.ne_zero
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne'] at hτ
    exact ht0 hτ.symm
  have hgτ0 : ∀ g : Ω ≃ₐ[K] Ω, g τ ≠ 0 := fun g => (map_ne_zero g).2 hτ0
  let w : (Ω ≃ₐ[K] Ω) → Ω := fun g => (v g : Ω) * τ / g τ
  have hw_lc : IsLocallyConstant w :=
    (hv.comp (fun x : Ωˣ => (x : Ω))).comp₂ (isLocallyConstant_eval (K := K) τ) (fun a b => a * τ / b)
  have hw_pow : ∀ g, w g ^ N = 1 := by
    intro g
    have h1 : (v g : Ω) ^ N = g t / t := by rw [← Units.val_pow_eq_pow_val]; exact ht g
    have h2 : (g τ) ^ N = g t := by rw [← map_pow, hτ]
    have h3 : g (t : Ω) ≠ 0 := (map_ne_zero g).2 ht0
    simp only [w]
    rw [div_pow, mul_pow, h1, h2, hτ]
    field_simp
  have hw_coc : ∀ g h, w g * g (w h) = ζ ^ (c g h).val * w (g * h) := by
    intro g h
    have hghτ : g (h τ) ≠ 0 := (map_ne_zero g).2 (hgτ0 h)
    have hg := hgτ0 g
    have e1 : w g * g (w h) = ((v g : Ω) * g (v h)) * τ / g (h τ) := by
      simp only [w, map_div₀, map_mul]
      field_simp
    rw [e1, hcoc g h]
    simp only [w, AlgEquiv.mul_apply]
    ring
  let E : Ω → ZMod N := fun x => if hx : ∃ i : ZMod N, ζ ^ i.val = x then hx.choose else 0
  let η : (Ω ≃ₐ[K] Ω) → ZMod N := fun g => E (w g)
  have hη : ∀ g, ζ ^ (η g).val = w g := by
    intro g
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one (hw_pow g)
    have hex : ∃ j : ZMod N, ζ ^ j.val = w g := ⟨(i : ZMod N), by rw [ZMod.val_cast_of_lt hi, hi']⟩
    simp only [η, E, dif_pos hex]
    exact hex.choose_spec
  refine ⟨η, hw_lc.comp E, ?_⟩
  intro g h
  have key : ζ ^ (η g + η h).val = ζ ^ (c g h + η (g * h)).val := by
    rw [KumLemma.pow_val_add hζ, KumLemma.pow_val_add hζ, hη g, hη h, hη (g * h)]
    have : g (w h) = w h := by rw [← hη h, map_pow, hfix]
    rw [← hw_coc, this]
  have hinj : η g + η h = c g h + η (g * h) :=
    ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) key)
  linear_combination -hinj

end GlobalTheory.Hilbert90CupCoboundary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycleStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyConstant_zmod_coboundary_of_mu_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  first | exact @GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | exact GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | (intros; apply GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochain
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochain
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB.TwistCochain

theorem pow_mod_of_pow_eq_one' {Ω : Type} [Field Ω] {N : ℕ} {ζ : Ω} (hN : ζ ^ N = 1) (n : ℕ) :
    ζ ^ (n % N) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n N, pow_add, pow_mul, hN, one_pow, one_mul]

theorem twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  intro K Ω _ _ _ _ N ζ hN hζ hζfix a b α β ha hb hα hβ w hw hcoc
  haveI : NeZero N := ⟨hN.ne'⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha ((algebraMap K Ω).injective (by rw [← hα, map_zero]))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((algebraMap K Ω).injective (by rw [← hβ, map_zero]))
  obtain ⟨-, hgα, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hζfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hylc, -, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hζfix hβ0 ⟨b, hβ.symm⟩
  refine ⟨fun g => Units.mk0 α hα0 ^ (kum (N := N) ζ β g).val * (w g)⁻¹, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hylc hw (fun (i : ZMod N) (u : Ωˣ) => Units.mk0 α hα0 ^ i.val * u⁻¹)
  · intro g h
    have hwg : (w g : Ω) ≠ 0 := (w g).ne_zero
    have hwh : g (w h : Ω) ≠ 0 := by simpa using (w h).ne_zero
    have hwgh : (w (g * h) : Ω) ≠ 0 := (w (g * h)).ne_zero
    have hz : ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val =
        (ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val := by
      rw [ZMod.val_mul, pow_mod_of_pow_eq_one' hζ.pow_eq_one, pow_mul]
    have hc := hcoc g h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, hgα g, hz]
    rw [pow_add] at hc
    field_simp
    rw [mul_pow]
    linear_combination -(ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val * hc

end GlobalTheory.NeedB.TwistCochain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochainStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_carry_coboundary_twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  first | exact @GlobalTheory.NeedB.TwistCochain.twist_cochain | exact GlobalTheory.NeedB.TwistCochain.twist_cochain | (intros; apply GlobalTheory.NeedB.TwistCochain.twist_cochain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCocycleCoboundaryOfNormsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCocycleCoboundaryOfNorms
open GlobalTheory.NeedB Polynomial
open scoped IntermediateField

namespace GlobalTheory.NeedB.NormCob

theorem hom_pow {G : Type*} [Group G] {N : ℕ} (y : G → ZMod N) (hy : ∀ g h, y (g * h) = y g + y h) (σ : G) (q : ℕ) :
    y (σ ^ q) = q * y σ := by
  have h1 : y 1 = 0 := by
    have := hy 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  induction q with
  | zero => simp [h1]
  | succ q ih => rw [pow_succ, hy, ih]; push_cast; ring

theorem exists_generator {G : Type*} [Group G] {N : ℕ} (hN : 0 < N) (y : G → ZMod N)
    (hy : ∀ g h, y (g * h) = y g + y h) :
    ∃ (d m : ℕ) (σ : G), 0 < m ∧ m * d = N ∧ y σ = m ∧ ∀ g, m ∣ (y g).val := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  have h1 : y 1 = 0 := by simpa using hom_pow y hy 1 0
  have hex : ∃ m : ℕ, 0 < m ∧ ∃ g, y g = m := ⟨N, hN, 1, by simp [h1]⟩
  obtain ⟨hm, σ, hσ⟩ := Nat.find_spec hex
  set m := Nat.find hex with hmdef
  have key : ∀ n : ℕ, (∃ g, y g = n) → m ∣ n := by
    rintro n ⟨g, hg⟩
    by_contra hnd
    have hr : 0 < n % m := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    refine Nat.find_min hex (Nat.mod_lt n hm) ⟨hr, g * (σ ^ (n / m))⁻¹, ?_⟩
    have h2 := hy (g * (σ ^ (n / m))⁻¹) (σ ^ (n / m))
    rw [inv_mul_cancel_right, hg, hom_pow y hy, hσ] at h2
    have h3 : (n : ZMod N) = ((n % m : ℕ) : ZMod N) + ((n / m : ℕ) : ZMod N) * m := by
      conv_lhs => rw [← Nat.mod_add_div' n m]
      push_cast; ring
    exact (add_right_cancel (h2.symm.trans h3))
  obtain ⟨d, hd⟩ := key N ⟨1, by simp [h1]⟩
  exact ⟨d, m, σ, hm, hd.symm, hσ, fun g => key _ ⟨g, by simp⟩⟩

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem agree {β : Ω} {g g' : Ω ≃ₐ[K] Ω} (h : g β = g' β) (x : K⟮β⟯) : g x = g' x := by
  have : (g : Ω →ₐ[K] Ω).comp K⟮β⟯.val = (g' : Ω →ₐ[K] Ω).comp K⟮β⟯.val := by
    apply IntermediateField.adjoin_algHom_ext
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact h
  exact DFunLike.congr_fun this x

theorem norm_eq_prod [CharZero K] [IsAlgClosure K Ω] {β : Ω} (σ : Ω ≃ₐ[K] Ω) (d : ℕ)
    (hinj : ∀ i < d, ∀ j < d, (σ ^ i) β = (σ ^ j) β → i = j)
    (hsurj : ∀ g : Ω ≃ₐ[K] Ω, ∃ j < d, g β = (σ ^ j) β) (γ : K⟮β⟯) :
    algebraMap K Ω (Algebra.norm K γ) = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  rw [Algebra.norm_eq_prod_embeddings K Ω γ]
  symm
  refine Finset.prod_bij (fun j _ => ((σ ^ j : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp K⟮β⟯.val) (by simp) ?_ ?_ ?_
  · intro i hi j hj hij
    exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
      (DFunLike.congr_fun hij (IntermediateField.AdjoinSimple.gen K β))
  · intro τ _
    obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := K) (E := Ω) (K := Ω)
      (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) τ
    let g : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    obtain ⟨j, hj, hg⟩ := hsurj g
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    rw [← hφ]
    ext x
    exact (agree hg x).symm
  · intro j _
    rfl

theorem carry_coboundary : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨hlc, hdef, hhom, -⟩ := GlobalTheory.NeedB.KumLemma.kummer_character_main K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  set y := kum (N := N) (K := K) ζ β with hydef
  obtain ⟨d, m, σ, hm, hmd, hσ, hdvd⟩ := exists_generator hN y hhom
  have hpow : ∀ j : ℕ, y (σ ^ j) = ((m * j : ℕ) : ZMod N) := fun j => by
    rw [hom_pow y hhom, hσ]; push_cast; ring
  have hval : ∀ g, (y g).val = m * ((y g).val / m) := fun g => (Nat.mul_div_cancel' (hdvd g)).symm
  have hlt : ∀ g, (y g).val / m < d := fun g => by
    apply Nat.div_lt_of_lt_mul
    rw [hmd]; exact ZMod.val_lt _
  have hyk : ∀ g, y g = y (σ ^ ((y g).val / m)) := fun g => by
    rw [hpow, ← hval, ZMod.natCast_zmod_val]
  have hag : ∀ g g', y g = y g' → g β = g' β := fun g g' h => by rw [hdef g, hdef g', h]
  haveI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral β)
  obtain ⟨γ, hγ⟩ := hnorm K⟮β⟯ inferInstance a ha
  have hγ0 : (γ : Ω) ≠ 0 := by
    intro h
    have : γ = 0 := Subtype.ext h
    rw [this, Algebra.norm_zero] at hγ
    exact ha hγ.symm
  have hprod : algebraMap K Ω a = ∏ j ∈ Finset.range d, (σ ^ j) γ := by
    rw [← hγ]
    refine norm_eq_prod σ d ?_ (fun g => ⟨_, hlt g, hag _ _ (hyk g)⟩) γ
    intro i hi j hj hij
    have hi' : m * i < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hi hm
    have hj' : m * j < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hj hm
    rw [hdef, hdef (σ ^ j), hpow, hpow, ZMod.val_cast_of_lt hi', ZMod.val_cast_of_lt hj'] at hij
    exact Nat.eq_of_mul_eq_mul_left hm (hζ.pow_inj hi' hj' (mul_right_cancel₀ hβ0 hij))
  let P : ℕ → Ω := fun n => ∏ j ∈ Finset.range n, (σ ^ j) γ
  have hP0 : ∀ n, P n ≠ 0 := fun n => Finset.prod_ne_zero_iff.mpr fun j _ => (_root_.map_ne_zero _).mpr hγ0
  have hPadd : ∀ (g : Ω ≃ₐ[K] Ω) (i n : ℕ), y g = y (σ ^ i) → P i * g (P n) = P (i + n) := by
    intro g i n hg
    simp only [P]
    rw [Finset.prod_range_add, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    have : y (g * σ ^ j) = y (σ ^ (i + j)) := by rw [pow_add, hhom, hhom, hg]
    exact agree (hag _ _ this) γ
  have hPd : ∀ r, P (d + r) = algebraMap K Ω a * P r := by
    intro r
    have h1 : y 1 = y (σ ^ d) := by
      rw [hpow, hmd, ← pow_zero σ, hpow]; simp
    rw [← hPadd 1 d r h1, hprod]
    rfl
  refine ⟨fun g => Units.mk0 (P ((y g).val / m)) (hP0 _),
    hlc.comp (fun z : ZMod N => Units.mk0 (P (z.val / m)) (hP0 _)), fun g h => ?_⟩
  simp only [Units.val_mk0]
  rw [hPadd g _ _ (hyk g), hhom, ZMod.val_add]
  have hg := hlt g
  have hh := hlt h
  rw [hval g, hval h, ← mul_add, Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel_left _ hm]
  generalize (y g).val / m = i at *
  generalize (y h).val / m = j at *
  by_cases hij : i + j < d
  · have : m * (i + j) < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hij hm
    rw [Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, mul_comm]
  · obtain ⟨r, hr⟩ : ∃ r, i + j = d + r := ⟨i + j - d, by omega⟩
    have hrd : r < d := by omega
    have : m * r < N := hmd ▸ Nat.mul_lt_mul_of_pos_left hrd hm
    rw [hr, mul_add, hmd, Nat.add_mod_left, Nat.mod_eq_of_lt this, Nat.mul_div_cancel_left _ hm, hPd, pow_add, hα]
    ring

end GlobalTheory.NeedB.NormCob
end

open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  first | exact @GlobalTheory.NeedB.NormCob.carry_coboundary | exact GlobalTheory.NeedB.NormCob.carry_coboundary | (intros; apply GlobalTheory.NeedB.NormCob.carry_coboundary <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerCoboundaryOfNorms
open GlobalTheory.NeedB Polynomial

theorem GlobalTheory.cup_kummer_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨w, hwc, hw⟩ := GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms K Ω N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  obtain ⟨v, hvc, hv⟩ := GlobalTheory.T.kummer_carry_coboundary_twist_cochain K Ω N ζ hN hζ hfix a b α β ha hb hα hβ w hwc hw
  exact GlobalTheory.T.exists_locallyConstant_zmod_coboundary_of_mu_cocycle K Ω N ζ hN hζ hfix (fun g h => kum ζ α g * kum ζ β h) v hvc hv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerCoboundaryOfNormsStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyConstant_kum_cup_coboundary_of_norm_surj : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g := by
  first | exact @GlobalTheory.cup_kummer_coboundary_of_norms | exact GlobalTheory.cup_kummer_coboundary_of_norms | (intros; apply GlobalTheory.cup_kummer_coboundary_of_norms <;> assumption)
end
