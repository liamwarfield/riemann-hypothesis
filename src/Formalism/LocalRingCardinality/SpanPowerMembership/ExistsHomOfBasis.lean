module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

theorem norm_le_one_iff_val {F C : Type} [Field F] [NumberField F] [NormedField C] (φ : F →+* C)
    (w : HeightOneSpectrum (𝓞 F)) (h1 : ∀ x : 𝓞 F, ‖φ (x : F)‖ ≤ 1)
    (h2 : ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1) (x : F) : ‖φ x‖ ≤ 1 ↔ w.valuation F x ≤ 1 := by
  have hu : ∀ d : 𝓞 F, d ∉ w.asIdeal → ‖φ (d : F)‖ = 1 := fun d hd =>
    le_antisymm (h1 d) (not_lt.mp fun h => hd ((h2 d).mpr h))
  have key : ∀ y : F, w.valuation F y ≤ 1 → ∃ n : 𝓞 F, ‖φ y‖ = ‖φ (n : F)‖ ∧
      w.valuation F y = w.valuation F (n : F) := fun y hy => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
    have hd : w.valuation F (algebraMap (𝓞 F) F d) = 1 := w.valuation_eq_one_iff_notMem.mpr d.2
    refine ⟨n, ?_, ?_⟩
    · have := congrArg (fun t => ‖φ t‖) h
      simp only [map_mul, norm_mul] at this
      rwa [show ‖φ (algebraMap (𝓞 F) F d)‖ = 1 from hu _ d.2, mul_one] at this
    · have := congrArg (w.valuation F) h
      rwa [map_mul, hd, mul_one] at this
  refine ⟨fun h => not_lt.mp fun hlt => ?_, fun h => ?_⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at hlt
    have hi : w.valuation F x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨n, e1, e2⟩ := key _ hi.le
    have hn : n ∈ w.asIdeal := (w.valuation_lt_one_iff_mem n).mp (e2 ▸ hi)
    have := (h2 n).mp hn
    rw [← e1, map_inv₀, norm_inv, inv_lt_one₀ (norm_pos_iff.mpr ((map_ne_zero φ).mpr hx))] at this
    exact absurd h (not_le.mpr this)
  · obtain ⟨n, e1, -⟩ := key x h
    rw [e1]; exact h1 n

theorem resChar_mem' (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hp := D.what₂.places.resChar_prime w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h := D.what₂.places.val_resChar w
  rw [D.val_eq w _ hne] at h
  have h1 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
    WithTop.coe_injective h
  have h2 : (0 : ℤ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL)]
  show (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL _) < 1
  have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hne
  rw [map_natCast, ← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  unfold vAdd at h1
  omega

theorem mem_intW_iff (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    x ∈ intW D.what₂.places w ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔ _
  by_cases hx : x = 0
  · subst hx; simp
  · have hv := (Valuation.ne_zero_iff ((D.plEq w).valuation D.what₂.LL)).mpr hx
    rw [D.val_eq w x hx, ← WithTop.coe_zero, WithTop.coe_le_coe, vAdd, neg_nonneg]
    conv_rhs => rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]

theorem exists_lamExt {K : Type} [Field K] [NumberField K] (e : K →+* ℂ) {C : Type} [Field C] [IsAlgClosed C]
    (f : K →+* C) : ∃ lam : (algebraicClosure ℚ ℂ) →+* C, ∀ x : K, ∃ hx : e x ∈ algebraicClosure ℚ ℂ,
      f x = lam ⟨e x, hx⟩ := by
  have hmem : ∀ x : K, e x ∈ algebraicClosure ℚ ℂ := fun x =>
    (mem_algebraicClosure_iff).mpr ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom e.toRatAlgHom)
  let j : K →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ).toSubring hmem
  let _ : Algebra K (algebraicClosure ℚ ℂ) := j.toAlgebra
  let _ : Algebra K C := f.toAlgebra
  have h0 : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let l : algebraicClosure ℚ ℂ →ₐ[K] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨l.toRingHom, fun x => ⟨hmem x, (l.commutes x).symm⟩⟩

theorem exists_placeEmb (D : D7) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime] :
    ∃ (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
      (iL : D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]),
      (∀ x, ∃ hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ, iL x = lam ⟨D.what₂.embLL x, hx⟩) ∧
      ∀ x, x ∈ intW D.what₂.places w ↔ ‖iL x‖ ≤ 1 := by
  obtain ⟨φ, hφ⟩ := LB.exists_embAt (l := D.what₂.places.resChar w) (D.plEq w) (resChar_mem' D w)
  let iL := (algebraMap (PadicAlgCl (D.what₂.places.resChar w)) ℂ_[D.what₂.places.resChar w]).comp φ
  have hn : ∀ x, ‖iL x‖ = ‖φ x‖ := fun x => PadicComplex.norm_extends _ (φ x)
  obtain ⟨lam, hl⟩ := exists_lamExt D.what₂.embLL iL
  refine ⟨lam, iL, hl, fun x => ?_⟩
  rw [mem_intW_iff, hn]
  refine (norm_le_one_iff_val φ _ (fun y => ?_) hφ x).symm
  have hi : IsIntegral ℤ (φ (y : D.what₂.LL)) := (RingOfIntegers.isIntegral_coe y).map φ.toIntAlgHom
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl (D.what₂.places.resChar w)))
    ).isIntegral_iff_v_le_one.mp hi.tower_top
  exact_mod_cast (show ‖φ (y : D.what₂.LL)‖₊ ≤ 1 from h2)

end Formalism.BasicNotions.Examples₂
end
end

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

structure Lbl where
  fA : ∀ k, (ZMod (H.g k))[X]
  fB : ∀ k, (ZMod (H.g k))[X]
  ne : ∀ k, fA k ≠ fB k
  okA : ∀ k, (fA k).Monic ∧ (fA k).natDegree = R.r ∧ (fA k).coeff 0 ≠ 0
  okB : ∀ k, (fB k).Monic ∧ (fB k).natDegree = R.r ∧ (fB k).coeff 0 ≠ 0
  good : ∀ k (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (fun v => if t v then fA k else fB k) (fun (_ : PP) (_ : J) => (1 : (ZMod (H.g k))ˣ))

variable {H} (Lb : Lbl H)



variable (H) (what₂ : Rows.Data R) (h : NHyp H what₂)

section Field

variable (K : Type) [Field K] [CharZero K]

end Field


end Formalism.BasicNotions.Examples₂.NZ
end
end

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.PlOver
noncomputable section

namespace Formalism.BasicNotions.Examples₂.PlOver

open NumberField IsDedekindDomain

variable (D : D7)

theorem liesOver_of_mem {L : Type} [Field L] [NumberField L] {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 L)) [hP : P.IsPrime]
    (h : ((p : ℕ) : 𝓞 L) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have := Int.ideal_span_isMaximal_of_prime p
  refine ⟨?_⟩
  refine Ideal.IsMaximal.eq_of_le inferInstance ?_ ?_
  · exact (Ideal.IsPrime.under ℤ P).ne_top
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using h

theorem mem_of_liesOver {L : Type} [Field L] [NumberField L] {p : ℕ} (P : Ideal (𝓞 L))
    [h : P.LiesOver (Ideal.span {(p : ℤ)})] : ((p : ℕ) : 𝓞 L) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [← h.over]; exact Ideal.mem_span_singleton_self _
  rw [Ideal.under_def, Ideal.mem_comap] at h1
  simpa using h1

theorem prime_unique {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (P : Ideal (𝓞 L))
    [hP : P.IsPrime] (hp' : ((p : ℕ) : 𝓞 L) ∈ P) (hq' : ((q : ℕ) : 𝓞 L) ∈ P) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((p : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((q : ℕ) : 𝓞 L) := by
    have := congrArg (Int.cast : ℤ → 𝓞 L) hab.symm
    push_cast at this
    exact this
  rw [h1]
  exact P.add_mem (P.mul_mem_left _ hp') (P.mul_mem_left _ hq')

theorem resChar_mem (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have hq := D.what₂.places.resChar_prime w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have h1 := D.val_eq w _ hne
  rw [D.what₂.places.val_resChar] at h1
  have h2 : ((D.what₂.places.ramIdx w : ℕ) : ℤ) =
      vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by exact_mod_cast h1
  have h3 : 0 < vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [← h2]; exact_mod_cast D.what₂.places.ramIdx_pos w
  unfold vAdd at h3
  have hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
    by_contra h
    push_neg at h
    have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hne
    have h4 := (WithZero.log_le_log one_ne_zero hv0).mpr h
    rw [WithZero.log_one] at h4
    omega
  refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.what₂.LL) _ _).mp ?_
  first
    | exact hlt
    | (simpa using hlt)
    | (convert hlt using 2; exact map_natCast _ _)

theorem resChar_eq_iff (p : ℕ) [hp : Fact p.Prime] (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ ((p : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have := (D.plEq w).isPrime
  constructor
  · rintro rfl; exact resChar_mem D w
  · intro h; exact prime_unique (D.what₂.places.resChar_prime w) hp.out _ (resChar_mem D w) h

theorem span_ne_bot (p : ℕ) [hp : Fact p.Prime] : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simp [hp.out.ne_zero]

theorem exists_over (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 D.what₂.LL))
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 D.what₂.LL)) :
    ∃ w : {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}, (D.plEq w.1).asIdeal = P := by
  obtain ⟨hPp, hPl⟩ := hP
  have hb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (span_ne_bot p) P
  refine ⟨⟨D.plEq.symm ⟨P, hPp, hb⟩, ?_⟩, by simp⟩
  rw [resChar_eq_iff]
  simpa using mem_of_liesOver (p := p) P

theorem plNe (p : ℕ) [Fact p.Prime] : Nonempty {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} := by
  have := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := 𝓞 D.what₂.LL) (Ideal.span {(p : ℤ)})
  exact ⟨(exists_over D p P hP).choose⟩

end Formalism.BasicNotions.Examples₂.PlOver
end
end
