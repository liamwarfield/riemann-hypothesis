module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.MemMirabQuot
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]

private theorem norm_one {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  have := (Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le
  have h2 := (Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge
  exact le_antisymm this h2

private theorem fin_supp (y : (Af F)ˣ) : Function.HasFiniteMulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖ := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (norm_one (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

private theorem absF_mul (y z : (Af F)ˣ) : absF (y * z) = absF y * absF z := by
  unfold absF
  rw [← finprod_mul_distrib (fin_supp y) (fin_supp z)]
  simp

private theorem absF_pos (y : (Af F)ˣ) : 0 < absF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w =>
    norm_pos_iff.2 (y.isUnit.map (pLoc F w)).ne_zero

private theorem ordI_mul (v : Pl F) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : ordI v (I * J) = ordI v I + ordI v J := by
  unfold ordI
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) v.associates_irreducible]

private theorem ordI_self (w : Pl F) : ordI w w.asIdeal = 1 := Associates.count_self w.associates_irreducible

private theorem ordI_ne {v w : Pl F} (h : v ≠ w) : ordI v w.asIdeal = 0 :=
  Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible fun e =>
    h (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))

private theorem ordI_inj {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ v : Pl F, ordI v I = ordI v J) : I = J := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI, ← Ideal.finprod_heightOneSpectrum_factorization hJ]
  exact finprod_congr fun v => congrArg (v.asIdeal ^ ·) (h v)

private theorem genD_uniq {y : Af F} {I J : Ideal (𝓞 F)} (hI : GenD y I) (hJ : GenD y J) : I = J :=
  ordI_inj hI.1 hJ.1 fun v => by
    have := WithZero.exp_inj.1 ((hI.2 v).symm.trans (hJ.2 v))
    omega

private theorem coefAt_eq (c : Ideal (𝓞 F) → ℂ) {y : Af F} {I : Ideal (𝓞 F)} (h : GenD y I) : coefAt c y = c I := by
  have e : ∃ 𝔪, GenD y 𝔪 := ⟨I, h⟩
  rw [coefAt, dite_eq_left e, genD_uniq e.choose_spec h]

private theorem genD_shift {w : Pl F} {u : Af F} (hu : ∀ v, Valued.v (pLoc F v u) = WithZero.exp (ordI v w.asIdeal : ℤ))
    (y : Af F) (I : Ideal (𝓞 F)) : GenD (y * u) I ↔ GenD y (w.asIdeal * I) := by
  by_cases hI : I = ⊥
  · simp [GenD, hI]
  refine and_congr (by simp [hI, w.ne_bot]) (forall_congr' fun v => ?_)
  rw [map_mul, map_mul, hu, ordI_mul v w.ne_bot hI, ← eq_div_iff WithZero.exp_ne_zero, ← WithZero.exp_sub]
  push_cast
  ring_nf

private theorem coefAt_shift {w : Pl F} {u : Af F} (hu : ∀ v, Valued.v (pLoc F v u) = WithZero.exp (ordI v w.asIdeal : ℤ))
    (a : Ideal (𝓞 F) → ℂ) (y : Af F) : coefAt (coefDiv a w.asIdeal) y = coefAt a (y * u) := by
  by_cases h : ∃ I, GenD (y * u) I
  · obtain ⟨I, hI⟩ := h
    have e : ∃ 𝔫, w.asIdeal * I = w.asIdeal * 𝔫 := ⟨I, rfl⟩
    rw [coefAt_eq a hI, coefAt_eq _ ((genD_shift hu y I).1 hI), coefDiv, dite_eq_left e,
      ← mul_left_cancel₀ w.ne_bot e.choose_spec]
  · rw [coefAt.eq_1 a, dite_eq_right h]
    by_cases h' : ∃ J, GenD y J
    · obtain ⟨J, hJ⟩ := h'
      rw [coefAt_eq _ hJ, coefDiv, dite_eq_right]
      rintro ⟨I, rfl⟩
      exact h ⟨I, (genD_shift hu y I).2 hJ⟩
    · rw [coefAt, dite_eq_right h']

private theorem max_eq {w : Pl F} (π : w.adicCompletionIntegers F)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) = Ideal.span {π} := by
  ext y
  rw [Ideal.mem_span_singleton, (HeightOneSpectrum.adicCompletionIntegers.integers F w).dvd_iff_le,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change ¬ Valued.v (y : w.adicCompletion F) = 1 ↔ Valued.v (y : w.adicCompletion F) ≤ Valued.v (π : w.adicCompletion F)
  rw [hπ]
  have hy : Valued.v (y : w.adicCompletion F) ≤ 1 := y.2
  generalize Valued.v (y : w.adicCompletion F) = t at hy
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
    rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_inj]
    omega

private theorem mem_mirab_quot {R : Type} [CommRing R] (I : Ideal R) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g ∈ mirab (R ⧸ I) ↔ g 1 0 ∈ I ∧ g 1 1 - 1 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq]
  change _ = _ ↔ _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct]

private theorem K1_conj (w : Pl F) (c : ℕ) (ϖ : (w.adicCompletion F)ˣ) (hϖ : IsUnifAt w ϖ)
    {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w (c + 1)) :
    ∃ k' ∈ K1 w c, k * aff ϖ⁻¹ 0 = aff ϖ⁻¹ 0 * k' := by
  obtain ⟨g, hg, rfl⟩ := hk
  have hϖ' : Valued.v (ϖ : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  let π : w.adicCompletionIntegers F := ⟨ϖ, by
    change Valued.v (ϖ : w.adicCompletion F) ≤ 1
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega⟩
  have hm := max_eq π hϖ'
  obtain ⟨h0, h1⟩ := (mem_mirab_quot _ g).1 hg
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h0
  obtain ⟨e, he⟩ := h0
  have hd : IsUnit (!![g 0 0, π * g 0 1; π ^ c * e, g 1 1] : Matrix (Fin 2) (Fin 2) _).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    rw [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two_of]
    convert this using 2
    rw [he]; ring
  refine ⟨_, ⟨Matrix.GeneralLinearGroup.mk'' _ hd, (mem_mirab_quot _ _).2 ⟨?_, Ideal.pow_le_pow_right (Nat.le_succ c) h1⟩, rfl⟩, ?_⟩
  · rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨e, rfl⟩
  · have he' : ((g 1 0 : w.adicCompletionIntegers F) : w.adicCompletion F) = ϖ ^ (c + 1) * e := by rw [he]; rfl
    ext i j : 2
    fin_cases i <;> fin_cases j <;>
      simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.mk'', Matrix.nonsingInvUnit, he', π]
    · ring
    · field_simp
      ring

private theorem gl_ext' {g h : GL (Fin 2) (Af F)}
    (e : ∀ w, Matrix.GeneralLinearGroup.map (pLoc F w) g = Matrix.GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) (e w)

private theorem locGL_comm {v w : Pl F} (h : v ≠ w) (g : GL (Fin 2) (v.adicCompletion F)) (k : GL (Fin 2) (w.adicCompletion F)) :
    locGL F 2 v g * locGL F 2 w k = locGL F 2 w k * locGL F 2 v g := by
  refine gl_ext' fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = v
  · subst hx; rw [pLoc_locGL_of_ne h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (aff y 0) = aff (Units.map f.toMonoidHom y) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mul {R : Type} [CommRing R] (y z : Rˣ) : aff y (0 : R) * aff z 0 = aff (y * z) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem aff_one {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem exists_idele (w : Pl F) (x : (w.adicCompletion F)ˣ) : ∃ u : (Af F)ˣ, pLoc F w u = x ∧
    (∀ v, v ≠ w → pLoc F v u = 1) ∧ locGL F 2 w (aff x 0) = aff u 0 := by
  classical
  let u : (Af F)ˣ := Units.map (corner (sLoc F w)) x
  have h1 : pLoc F w u = x := by
    have h : ∀ y, pLoc F w (sLoc F w y) = y := fun y =>
      Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w y
    change pLoc F w (1 - sLoc F w 1 + sLoc F w x) = x
    simp [h]
  have h2 : ∀ v, v ≠ w → pLoc F v u = 1 := fun v hv => by
    have h : ∀ y, pLoc F v (sLoc F w y) = 0 := fun y =>
      Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) hv y
    change pLoc F v (1 - sLoc F w 1 + sLoc F w x) = 1
    simp [h]
  refine ⟨u, h1, h2, gl_ext' fun v => ?_⟩
  rw [map_aff]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL]
    congr 1
    exact Units.ext h1.symm
  · rw [pLoc_locGL_of_ne hv, ← aff_one]
    congr 1
    exact Units.ext (h2 v hv).symm

variable [IsTotallyReal F]

private theorem lie_fin (X : TR.Lie F 2) (t : GL (Fin 2) (Af F)) (φ : TR.Sm F 2) :
    TR.lie F 2 X (TR.finRep F 2 t φ) = TR.finRep F 2 t (TR.lie F 2 X φ) :=
  LinearMap.congr_fun (TR.lie_rt_fin X t) φ

private theorem zalg_comm (t : GL (Fin 2) (Af F)) {z : Module.End ℂ (TR.Sm F 2)} (hz : z ∈ TR.Zalg F 2) :
    TR.finRep F 2 t * z = z * TR.finRep F 2 t := by
  let S : Subalgebra ℂ (Module.End ℂ (TR.Sm F 2)) := Subalgebra.centralizer ℂ {TR.finRep F 2 t}
  have hE : ∀ τ i j, TR.Eop τ i j ∈ S := fun τ i j => (Subalgebra.mem_centralizer_iff ℂ).2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    exact (TR.lie_rt_fin _ t).symm
  refine (Subalgebra.mem_centralizer_iff ℂ).1 ((Algebra.adjoin_le (S := S) ?_) hz) _ rfl
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

private theorem aut_fin {φ : TR.Sm F 2} (h : TR.IsAutForm φ) (t : GL (Fin 2) (Af F)) {s : ℂ} (hs : s ≠ 0) :
    TR.IsAutForm (s • TR.finRep F 2 t φ) := by
  have hv : ∀ g, (s • TR.finRep F 2 t φ).1 g = s * φ.1 (g * finGL F 2 t) := fun _ => rfl
  refine ⟨fun γ g => by rw [hv, hv, mul_assoc, h.left], ?_, ?_, ?_, fun g => ?_⟩
  · have e : {k | TR.finRep F 2 k (s • TR.finRep F 2 t φ) = s • TR.finRep F 2 t φ} =
        (fun k => t⁻¹ * k * t) ⁻¹' {k | TR.finRep F 2 k φ = φ} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_smul, map_mul, Module.End.mul_apply]
      rw [(smul_right_injective _ hs).eq_iff]
      constructor
      · intro hk
        rw [hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro hk
        conv_rhs => rw [← hk]
        rw [← Module.End.mul_apply (TR.finRep F 2 t), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e]
    exact h.level.preimage (by fun_prop)
  · haveI := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => TR.cptRep F 2 k φ)).map
      (s • TR.finRep F 2 t)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, Subtype.ext (funext fun g => ?_)⟩
    change s * φ.1 (g * finGL F 2 t * TR.infGL F 2 _) = s * φ.1 (g * TR.infGL F 2 _ * finGL F 2 t)
    rw [mul_assoc, mul_assoc, TR.infGL_comm]
  · haveI := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F 2) => z φ) '' TR.Zalg F 2)).map
      (s • TR.finRep F 2 t)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (s • ·) (LinearMap.congr_fun (zalg_comm t hz) φ)
  · obtain ⟨C, N, hC⟩ := h.growth (g * finGL F 2 t)
    refine ⟨‖s‖ * C, N, fun y => ?_⟩
    rw [hv, norm_mul, mul_assoc g, TR.infGL_comm, ← mul_assoc, mul_assoc ‖s‖]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)

end UpperTheory.V.Sd

open UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holB :
    UpperTheory.V.Sd.HolB := by
  intro F _ _ _ k c ω φ c₀ a w hφ hE
  classical
  have hϖ := unif_spec w
  set ϖ := atFin w (unif w)
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_idele w ϖ⁻¹
  have hu : ∀ v, Valued.v (pLoc F v (u : Af F)) = WithZero.exp (ordI v w.asIdeal : ℤ) := fun v => by
    by_cases hv : v = w
    · subst hv
      rw [hu1, ordI_self, Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (ϖ : v.adicCompletion F) = _ from hϖ,
        ← WithZero.exp_neg]
      rfl
    · rw [hu2 v hv, ordI_ne hv, map_one]; rfl
  have hp : 0 < absF u ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (absF_pos u) _
  have hp' : ((absF u ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp.ne'
  set s : ℂ := ((absF u ^ ((k : ℝ) / 2) : ℝ) : ℂ)⁻¹ with hs
  have hv : ∀ g, (s • TR.finRep F 2 (aff u 0) φ).1 g = s * φ.1 (g * finGL F 2 (aff u 0)) := fun _ => rfl
  refine ⟨s • TR.finRep F 2 (aff u 0) φ, u, ⟨aut_fin hφ.aut _ (inv_ne_zero hp'), fun v => ?_, fun z g => ?_, fun v => ?_,
    fun v => ?_⟩, fun x y hy yf => ?_⟩
  · refine Submodule.smul_mem _ _ fun g hg => ?_
    change TR.finRep F 2 (locGL F 2 v g) _ = _
    rw [← Module.End.mul_apply, ← map_mul, ← hu3]
    by_cases hvw : v = w
    · subst hvw
      rw [Function.update_self] at hg
      obtain ⟨g', hg', e⟩ := K1_conj v _ ϖ hϖ hg
      rw [← map_mul, e, map_mul, map_mul, Module.End.mul_apply]
      exact congrArg _ (hφ.level v g' hg')
    · rw [Function.update_of_ne hvw] at hg
      rw [locGL_comm hvw, map_mul, Module.End.mul_apply]
      exact congrArg _ (hφ.level v g hg)
  · rw [hv, hv, mul_assoc, hφ.cent]; ring
  · have := hφ.wt v
    simp only [TR.Eop, map_smul, lie_fin] at this ⊢
    rw [← smul_sub, ← map_sub, this, map_smul, smul_comm]
  · have := hφ.low v
    simp only [TR.Eop, map_smul, lie_fin] at this ⊢
    rw [← smul_sub, ← map_sub, this, map_smul, smul_comm, ← smul_add, ← map_add (f := _)]
  · have h := hE x y hy (yf * u)
    have hy' : 0 < ∏ v, y.val v := Finset.prod_pos fun v _ => hy v
    convert h using 2
    · rw [coefAt_shift hu, Units.val_mul, mul_assoc (algebraMap F (Af F) _)]
    · rw [hv, mul_assoc, ← map_mul, aff_mul, absF_mul, ← mul_assoc,
        Real.mul_rpow (mul_pos hy' (absF_pos yf)).le (absF_pos u).le, Complex.ofReal_mul, hs]
      rw [mul_comm _ (φ.1 _), ← div_eq_mul_inv, div_div, mul_comm (_ : ℂ)]
end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]

private theorem div_mul (a : Ideal (𝓞 F) → ℂ) (w : Pl F) (n : Ideal (𝓞 F)) : coefDiv a w.asIdeal (w.asIdeal * n) = a n := by
  have h : ∃ 𝔫, w.asIdeal * n = w.asIdeal * 𝔫 := ⟨n, rfl⟩
  unfold coefDiv
  rw [dite_eq_left h, ← mul_left_cancel₀ w.ne_bot h.choose_spec]

private theorem div_not (a : Ideal (𝓞 F) → ℂ) (w : Pl F) {m : Ideal (𝓞 F)} (h : ¬ w.asIdeal ∣ m) : coefDiv a w.asIdeal m = 0 := by
  unfold coefDiv
  rw [dite_eq_right]
  exact h

private theorem not_dvd_mul {v w : Pl F} (hvw : v ≠ w) {m : Ideal (𝓞 F)} (h : ¬ v.asIdeal ∣ m) : ¬ v.asIdeal ∣ w.asIdeal * m := by
  intro h'
  rcases v.prime.dvd_or_dvd h' with h1 | h1
  · exact hvw (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))
  · exact h h1

private theorem div_comm {v w : Pl F} (hvw : v ≠ w) (a : Ideal (𝓞 F) → ℂ) (m : Ideal (𝓞 F)) :
    coefDiv a v.asIdeal (w.asIdeal * m) = coefDiv (fun n => a (w.asIdeal * n)) v.asIdeal m := by
  by_cases h : v.asIdeal ∣ m
  · obtain ⟨n, rfl⟩ := h
    rw [div_mul, mul_left_comm, div_mul]
  · rw [div_not _ _ h, div_not _ _ (not_dvd_mul hvw h)]

private def Rel (w : Pl F) (e t : ℂ) (a : Ideal (𝓞 F) → ℂ) : Prop :=
  ∀ m, m ≠ ⊥ → a (w.asIdeal * m) + e * coefDiv a w.asIdeal m = t * a m

private theorem rel_div {v w : Pl F} (hvw : v ≠ w) {e t : ℂ} {a : Ideal (𝓞 F) → ℂ} (h : Rel w e t a) :
    Rel w e t (coefDiv a v.asIdeal) := by
  intro m hm
  by_cases h1 : v.asIdeal ∣ m
  · obtain ⟨n, rfl⟩ := h1
    have hn : n ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
    rw [div_comm hvw.symm, mul_left_comm, div_mul, div_mul, ← h n hn]
    simp only [div_mul]
  · rw [div_not _ _ h1, div_not _ _ (not_dvd_mul hvw h1)]
    by_cases h2 : w.asIdeal ∣ m
    · obtain ⟨n, rfl⟩ := h2
      rw [div_mul, div_not _ _ (fun h3 => h1 (h3.mul_left _))]
      simp
    · rw [div_not _ _ h2]
      simp

private theorem div_add (a b : Ideal (𝓞 F) → ℂ) (z : ℂ) (q m : Ideal (𝓞 F)) :
    coefDiv (a + z • b) q m = coefDiv a q m + z * coefDiv b q m := by
  unfold coefDiv
  split_ifs <;> simp

private theorem rel_add {w : Pl F} {e t : ℂ} {a b : Ideal (𝓞 F) → ℂ} (z : ℂ) (h : Rel w e t a) (h' : Rel w e t b) :
    Rel w e t (a + z • b) := by
  intro m hm
  rw [div_add]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h m hm + z * h' m hm

private theorem rel_same {w : Pl F} {x y : ℂ} {a : Ideal (𝓞 F) → ℂ} (h : Rel w (x * y) (x + y) a) :
    Rel w 0 x (a + (-y) • coefDiv a w.asIdeal) := by
  intro m hm
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_mul]
  linear_combination h m hm

private theorem ord_fin {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : {w : Pl F | ordI w I ≠ 0}.Finite := by
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  exact (Associates.count_ne_zero_iff_dvd hI w.irreducible).1 hw

private theorem chi_mul (ω : HChar F) (c : Pl F → ℕ) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    chiI ω c (I * J) = chiI ω c I * chiI ω c J := by
  unfold chiI
  rw [← finprod_mul_distrib]
  · refine finprod_congr fun w => ?_
    rw [← pow_add]
    congr 1
    unfold ordI
    rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) w.associates_irreducible]
  · refine (ord_fin hI).subset fun w hw h0 => hw ?_
    simp only [h0, pow_zero]
  · refine (ord_fin hJ).subset fun w hw h0 => hw ?_
    simp only [h0, pow_zero]

private theorem chi_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  unfold chiI
  rw [finprod_eq_single _ w]
  · have : ordI w w.asIdeal = 1 := Associates.count_self w.associates_irreducible
    rw [this, pow_one]
  · intro v hv
    have : ordI v w.asIdeal = 0 := by
      by_contra h0
      have h1 := (Associates.count_ne_zero_iff_dvd w.ne_bot v.irreducible).1 h0
      exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 ((v.prime.dvd_prime_iff_associated w.prime).1 h1)))
    rw [this, pow_zero]

private theorem chi_top (ω : HChar F) (c : Pl F → ℕ) : chiI ω c ⊤ = 1 := by
  unfold chiI
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  have : ordI v ⊤ = 0 := by
    by_contra h0
    have h1 := (Associates.count_ne_zero_iff_dvd top_ne_bot v.irreducible).1 h0
    exact v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h1))
  rw [this, pow_zero]

private theorem dvd_fin {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) : {r : Ideal (𝓞 F) | r ∣ m}.Finite := by
  have := UniqueFactorizationMonoid.fintypeSubtypeDvd m hm
  exact Set.finite_coe_iff.1 (Finite.of_fintype {r // r ∣ m})

private theorem sum_step (χ : Ideal (𝓞 F) → ℂ) (hχ : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → χ (I * J) = χ I * χ J) (w : Pl F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) :
    ∑ᶠ r ∈ {r | r ∣ w.asIdeal * m}, χ r = χ w.asIdeal * ∑ᶠ r ∈ {r | r ∣ m}, χ r + ∑ᶠ r ∈ {r | r ∣ m ∧ ¬ w.asIdeal ∣ r}, χ r := by
  have hs : {r | r ∣ w.asIdeal * m} = (fun r => w.asIdeal * r) '' {r | r ∣ m} ∪ {r | r ∣ m ∧ ¬ w.asIdeal ∣ r} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro h
      by_cases h1 : w.asIdeal ∣ r
      · obtain ⟨n, rfl⟩ := h1
        exact Or.inl ⟨n, (mul_dvd_mul_iff_left w.ne_bot).1 h, rfl⟩
      · refine Or.inr ⟨?_, h1⟩
        exact ((w.irreducible.isRelPrime_iff_not_dvd.2 h1).symm).dvd_of_dvd_mul_left h
    · rintro (⟨n, hn, rfl⟩ | ⟨h, -⟩)
      · exact mul_dvd_mul_left _ hn
      · exact h.mul_left _
  rw [hs, finsum_mem_union _ ((dvd_fin hm).image _) ((dvd_fin hm).subset fun r (h : r ∈ {r : Ideal (𝓞 F) | r ∣ m ∧ ¬ w.asIdeal ∣ r}) => h.1),
    finsum_mem_image (fun x _ y _ h => mul_left_cancel₀ w.ne_bot h)]
  · congr 1
    rw [finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm), finsum_mem_eq_finite_toFinset_sum _ (dvd_fin hm), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => hχ _ _ w.ne_bot ?_
    rintro rfl
    exact hm (zero_dvd_iff.1 ((dvd_fin hm).mem_toFinset.1 hr))
  · rw [Set.disjoint_left]
    rintro _ ⟨n, -, rfl⟩ h
    exact h.2 (dvd_mul_right _ _)

private theorem rel_sum (χ : Ideal (𝓞 F) → ℂ) (hχ : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → χ (I * J) = χ I * χ J) (w : Pl F) :
    Rel w (χ w.asIdeal) (1 + χ w.asIdeal) fun m => ∑ᶠ r ∈ {r | r ∣ m}, χ r := by
  intro m hm
  simp only
  rw [sum_step χ hχ w hm]
  by_cases h : w.asIdeal ∣ m
  · obtain ⟨n, rfl⟩ := h
    have hn : n ≠ ⊥ := fun h0 => hm (by rw [h0, Ideal.mul_bot])
    have hs : {r | r ∣ w.asIdeal * n ∧ ¬ w.asIdeal ∣ r} = {r | r ∣ n ∧ ¬ w.asIdeal ∣ r} := by
      ext r
      exact ⟨fun h => ⟨((w.irreducible.isRelPrime_iff_not_dvd.2 h.2).symm).dvd_of_dvd_mul_left h.1, h.2⟩,
        fun h => ⟨h.1.mul_left _, h.2⟩⟩
    rw [div_mul, hs]
    linear_combination -sum_step χ hχ w hn
  · have hs : {r | r ∣ m ∧ ¬ w.asIdeal ∣ r} = {r | r ∣ m} := by
      ext r
      exact ⟨fun h => h.1, fun h1 => ⟨h1, fun h2 => h (h2.trans h1)⟩⟩
    rw [div_not _ _ h, hs]
    ring

private def intS {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) : Subring ℂ where
  carrier := {z | ‖ι.symm z‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

private theorem val_mem {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) :
    ((ω.val w : ℂˣ) : ℂ) ∈ intS ι := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  have h1 : ∀ k : ℕ, (ω ^ k).val w = ω.val w ^ k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]
  have h2 : ω.val w ^ n = 1 := by rw [← h1, h]; rfl
  have h3 : ‖ι.symm ((ω.val w : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, h2]
    simp
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3).le

private theorem chi_mem (S : Subring ℂ) {ω : HChar F} (h : ∀ w, ((ω.val w : ℂˣ) : ℂ) ∈ S) (c : Pl F → ℕ) (I : Ideal (𝓞 F)) :
    chiI ω c I ∈ S := by
  unfold chiI
  refine finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) fun w => S.pow_mem ?_ _
  split_ifs
  exacts [h w, S.zero_mem]

private theorem div_mem (S : Subring ℂ) {a : Ideal (𝓞 F) → ℂ} (h : ∀ m, a m ∈ S) (q m : Ideal (𝓞 F)) : coefDiv a q m ∈ S := by
  unfold coefDiv
  split_ifs
  exacts [h _, S.zero_mem]

open Classical in
private theorem step [IsTotallyReal F] (S : Subring ℂ) (ω : HChar F) (hS : ∀ w, ((ω.val w : ℂˣ) : ℂ) ∈ S) (c : Pl F → ℕ)
    (P : Set (Pl F)) (φ₀ : TR.Sm F 2) (L₀ : ℂ) (h1 : IsHol 1 c ω φ₀)
    (h2 : HasExp φ₀.1 1 (fun _ => L₀) fun 𝔪 => ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯) (T : Finset (Pl F)) (hT : ∀ w ∈ T, c w = 0) :
    ∃ (φ : TR.Sm F 2) (L : ℂ) (a : Ideal (𝓞 F) → ℂ), IsHol 1 (fun w => if w ∈ T then 1 else c w) ω φ ∧
      HasExp φ.1 1 (fun _ => L) a ∧ ((∃ w ∈ T, w ∈ P) → L = 0) ∧ a ⊤ = 1 ∧ (∀ m, a m ∈ S) ∧
      (∀ w ∈ T, Rel w 0 (if w ∈ P then ((ω.val w : ℂˣ) : ℂ) else 1) a) ∧
      ∀ w ∉ T, Rel w (chiI ω c w.asIdeal) (1 + chiI ω c w.asIdeal) a := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨φ₀, L₀, _, by simpa using h1, h2, by simp, ?_, fun m => ?_, by simp, fun w _ => rel_sum _ (fun I J => chi_mul ω c) w⟩
    · have : {r : Ideal (𝓞 F) | r ∣ ⊤} = {⊤} := by
        ext r
        simp [Ideal.dvd_iff_le]
      simp only [this, finsum_mem_singleton, chi_top]
    · refine finsum_mem_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem) fun r _ => chi_mem S hS c r
  | insert v T hv ih =>
    obtain ⟨φ, L, a, g1, g2, g3, g4, g5, g6, g7⟩ := ih fun w hw => hT w (Finset.mem_insert_of_mem hw)
    have hc : c v = 0 := hT v (Finset.mem_insert_self _ _)
    obtain ⟨ψ, u, k1, k2⟩ := holB F 1 _ ω φ _ a v g1 g2
    have he : Function.update (fun w => if w ∈ T then 1 else c w) v ((if v ∈ T then 1 else c v) + 1) =
        fun w => if w ∈ insert v T then 1 else c w := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp [hv, hc]
      · simp [hw]
    rw [he] at k1
    obtain ⟨-, -, l1, -, l2⟩ := holLin F 1 (fun w => if w ∈ insert v T then 1 else c w) ω
    obtain ⟨-, -, -, l3, l4⟩ := holLin F 1 (fun w => if w ∈ T then 1 else c w) ω
    have g1' : IsHol 1 (fun w => if w ∈ insert v T then 1 else c w) ω φ := by
      refine l4 φ _ (fun w => ?_) g1
      by_cases hw : w = v
      · subst hw
        simp [hv, hc]
      · simp [hw]
    set y : ℂ := if v ∈ P then 1 else ((ω.val v : ℂˣ) : ℂ) with hy
    have hyS : y ∈ S := by
      rw [hy]
      split_ifs
      exacts [S.one_mem, hS v]
    refine ⟨φ + (-y) • ψ, L + (-y) * L, a + (-y) • coefDiv a v.asIdeal, l1 _ _ _ g1' k1, l3 _ _ (-y) _ _ _ _ g2 k2, ?_, ?_,
      fun m => S.add_mem (g5 m) (S.mul_mem (S.neg_mem hyS) (div_mem S g5 _ _)), fun w hw => ?_, fun w hw => ?_⟩
    · rintro ⟨w, hw, hP⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [hy, if_pos hP]
        ring
      · rw [g3 ⟨w, hw, hP⟩]
        ring
    · have : ¬ v.asIdeal ∣ ⊤ := fun h => v.isPrime.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 h))
      simp [g4, div_not a v this]
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · apply rel_same
        have := g7 w hv
        rw [chi_prime, if_pos hc] at this
        rw [hy]
        split_ifs
        · rwa [mul_one, add_comm]
        · rwa [one_mul]
      · exact rel_add _ (g6 w hw) (rel_div (fun h : v = w => hv (h ▸ hw)) (g6 w hw))
    · rw [Finset.mem_insert, not_or] at hw
      exact rel_add _ (g7 w hw.2) (rel_div (Ne.symm hw.1) (g7 w hw.2))

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.emix :
    UpperTheory.V.Published.HilbertEisOne → UpperTheory.V.Sd.Emix := by
  intro hE F _ _ _ l hl ι ω c hω hodd hcond hne hcl P hP
  classical
  obtain ⟨φ₀, L₀, h1, h2⟩ := hE F ω c hω hodd hcond hne
  have hl0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.out.ne_zero
  have hfin := Ideal.finite_factors hl0
  have hT : ∀ w : Pl F, w ∈ hfin.toFinset ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := fun w => by
    rw [hfin.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  obtain ⟨φ, L, a, g1, g2, g3, g4, g5, g6, g7⟩ := step (intS ι) ω (val_mem ι hω) c P φ₀ L₀ h1 h2 hfin.toFinset
    fun w hw => hcl w ((hT w).1 hw)
  obtain ⟨w₀, hw₀, hw₁⟩ := hP
  obtain rfl := g3 ⟨w₀, (hT _).2 hw₁, hw₀⟩
  have he : (fun w => if w ∈ hfin.toFinset then 1 else c w) = levL l c := by
    funext w
    simp only [levL, hT]
  refine ⟨φ, a, he ▸ g1, g2, g4, fun m _ => g5 m, fun w m hm => ?_⟩
  unfold hkCoef eisT
  rw [chi_prime, Nat.sub_self, pow_zero, mul_one]
  by_cases hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
  · have := g6 w ((hT w).2 hw) m hm
    simp only [levL, hw, if_true, one_ne_zero, if_false]
    convert this
  · have := g7 w (fun h => hw ((hT w).1 h)) m hm
    rw [chi_prime] at this
    simp only [levL, hw, if_false]
    rw [this]
    split_ifs <;> simp
