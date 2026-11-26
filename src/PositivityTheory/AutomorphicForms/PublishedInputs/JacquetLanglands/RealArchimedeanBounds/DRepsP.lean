module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.RtWMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DRepsP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.DeterminantRepresentatives

variable {F : Type} [Field F] [NumberField F]

theorem norm_one' {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  have := (Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le
  have h2 := (Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge
  exact le_antisymm this h2

theorem fin_supp (y : (Af F)ˣ) : Function.HasFiniteMulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖ := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (norm_one' (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

theorem absF_mul (y z : (Af F)ˣ) : absF (y * z) = absF y * absF z := by
  unfold absF
  rw [← finprod_mul_distrib (fin_supp y) (fin_supp z)]
  simp

theorem aff_mul {R : Type} [CommRing R] (y z : Rˣ) (x t : R) : aff y x * aff z t = aff (y * z) (x + y * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

@[simp] theorem aff_one {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, aff, Matrix.det_fin_two_of]

theorem det_centralSection {R : Type} [CommRing R] (y : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) y * (aff y 0)⁻¹) = y := by
  rw [map_mul, map_inv, det_aff]
  ext
  simp [pow_two]

theorem pLoc_det (v : Pl F) (g : GF F) : pLoc F v ((Matrix.GeneralLinearGroup.det g : (Af F)ˣ) : Af F) =
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (pLoc F v) g) : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem absF_loc (w : Pl F) (g : GL (Fin 2) (w.adicCompletion F))
    (hg : Matrix.GeneralLinearGroup.det g = atFin w (unif w)) :
    absF (Matrix.GeneralLinearGroup.det (locGL F 2 w g)) = (normV w : ℝ)⁻¹ := by
  rw [absF, finprod_eq_single _ w fun v hv => by rw [pLoc_det, pLoc_locGL_of_ne hv]; simp, pLoc_det, pLoc_locGL, hg,
    FinitePlace.norm_def, unif_spec, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]

  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem step {c : Pl F → ℕ} {w : Pl F} {W : List (Pl F)} {ι κ : Type} [Fintype ι] [Fintype κ] {b : ι → GF F}
    (hb : IsReps c W b) (r : κ → GL (Fin 2) (w.adicCompletion F))
    (hr1 : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V),
      ∀ x ∈ Hi.fixd ρ (K1 w (c w)), Uop w ρ (c w) x = ∑ j, ρ (r j) x)
    (hr2 : ∀ j, Matrix.GeneralLinearGroup.det (r j) = atFin w (unif w))
    (hr3 : c w ≠ 0 → ∀ j, ∃ u : w.adicCompletionIntegers F, r j = aff (atFin w (unif w)) (u : w.adicCompletion F)) :
    IsReps c (w :: W) (fun p : κ × ι => locGL F 2 w (r p.1) * b p.2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ ρ x hx
    obtain ⟨hy, he⟩ := hb.act V ρ x hx
    have hy' : (∑ i, ρ (b i) x) ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w)) :=
      fun k hk => hy _ ((kcTop F).2.2.2.2.2 c w k hk)
    have hs : ∑ p : κ × ι, ρ (locGL F 2 w (r p.1) * b p.2) x =
        Uop w (ρ.comp (locGL F 2 w)) (c w) (∑ i, ρ (b i) x) := by
      rw [hr1 V (ρ.comp (locGL F 2 w)) _ hy', Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Module.End.mul_apply]
      rfl
    rw [hs]
    refine ⟨(hkComm (hkReps uopSum) kcTop F V ρ c _ hy w).1, ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← he]
  · intro p
    rw [map_mul, absF_mul, absF_loc w _ (hr2 p.1), hb.det, List.map_cons, List.prod_cons]
  · intro p w' hw'
    classical
    obtain ⟨u', hu'⟩ := hb.loc p.2 w' hw'
    rw [map_mul]
    by_cases h : w' = w
    · subst h
      obtain ⟨u, hu⟩ := hr3 hw' p.1
      have hm : ((atFin w' (unif w') : (w'.adicCompletion F)ˣ) : w'.adicCompletion F) ∈ w'.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, unif_spec, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      refine ⟨u + ⟨_, hm⟩ * u', ?_⟩
      rw [pLoc_locGL, hu, hu', aff_mul, List.count_cons_self, pow_succ']
      push_cast
      rfl
    · refine ⟨u', ?_⟩
      rw [pLoc_locGL_of_ne h, one_mul, hu']
      simp [List.count_cons, Ne.symm h]

theorem base (c : Pl F → ℕ) : IsReps c ([] : List (Pl F)) (fun _ : Unit => (1 : GF F)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ ρ x hx
    simpa using hx
  · intro i
    simp [absF]
  · intro i w hw
    exact ⟨0, by simp⟩

theorem reindex {c : Pl F → ℕ} {W : List (Pl F)} {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) {a : ι → GF F}
    (h : IsReps c W a) : IsReps c W (a ∘ e) := by
  refine ⟨?_, fun i => h.det (e i), fun i => h.loc (e i)⟩
  intro V _ _ ρ x hx
  rw [show ∑ i, ρ ((a ∘ e) i) x = ∑ i, ρ (a i) x from Equiv.sum_comp e (fun i => ρ (a i) x)]
  exact h.act V ρ x hx

theorem ex (c : Pl F → ℕ) (W : List (Pl F)) : ∃ (ι : Type) (_ : Fintype ι) (a : ι → GF F), IsReps c W a := by
  induction W with
  | nil => exact ⟨Unit, inferInstance, _, base c⟩
  | cons w W ih =>
    obtain ⟨ι, _, b, hb⟩ := ih
    classical
    haveI := Formalism.UG.P.glint_finite_residueField w
    letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
    choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))
    have hS : Set.BijOn (IsLocalRing.residue (w.adicCompletionIntegers F))
        ((Finset.univ.image s : Finset (w.adicCompletionIntegers F)) : Set (w.adicCompletionIntegers F)) Set.univ := by
      refine ⟨fun _ _ => Set.mem_univ _, ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩
      intro x hx y hy h
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      rw [hs, hs] at h
      rw [h]
    generalize Finset.univ.image s = S at hS
    by_cases hc : c w = 0
    · refine ⟨Option S × ι, inferInstance, _, step hb (fun o => o.elim
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w)) * (aff (atFin w (unif w)) 0)⁻¹)
        (fun u => aff (atFin w (unif w)) ((u : w.adicCompletionIntegers F) : w.adicCompletion F))) ?_ ?_ ?_⟩
      · intro V _ _ ρ x hx
        rw [(uopSum F w V ρ (c w) x hx).2 S hS, if_pos hc, Fintype.sum_option, add_comm, ← Finset.sum_coe_sort S]
        rfl
      · intro j
        cases j with
        | none => exact det_centralSection _
        | some u => exact det_aff _ _
      · exact fun h => absurd hc h
    · refine ⟨S × ι, inferInstance, _, step hb (fun u : S => aff (atFin w (unif w))
        ((u : w.adicCompletionIntegers F) : w.adicCompletion F)) ?_ (fun _ => det_aff _ _) (fun _ u => ⟨u, rfl⟩)⟩
      intro V _ _ ρ x hx
      rw [(uopSum F w V ρ (c w) x hx).2 S hS, if_neg hc, add_zero, ← Finset.sum_coe_sort S]

end UpperTheory.Esk.DeterminantRepresentatives

open UpperTheory.Esk.DeterminantRepresentatives in
theorem UpperTheory.Esk.dReps : UpperTheory.Esk.DReps := by
  intro F _ _ c W
  obtain ⟨ι, _, a, ha⟩ := ex c W
  exact ⟨Fintype.card ι, a ∘ (Fintype.equivFin ι).symm, reindex _ ha⟩
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AAdd
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem aAdd : AMem → AAdd := by
  intro _ F _ _ t u
  have hU : IsOpen {z : Af F | ((t⁻¹ : (Af F)ˣ) : Af F) * (u - z) ∈ Ohat F} :=
    isOpen_Ohat.preimage (by fun_prop)
  obtain ⟨y, hy⟩ := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).exists_mem_open hU
    ⟨u, by simp⟩
  exact ⟨y, hy⟩

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AMonoP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.MonomialSupportLemmas

variable {F : Type} [Field F] [NumberField F]

theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.MonomialSupportLemmas

open UpperTheory.Esk.MonomialSupportLemmas in
theorem UpperTheory.Esk.aMono : UpperTheory.Esk.AMono := by
  intro F _ _ t t' h
  classical
  unfold absF
  set s := ((fin_supp t).union (fin_supp t')).toFinset
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) (by intro w hw; simp [s, hw]),
    finprod_eq_prod_of_mulSupport_subset _ (s := s) (by intro w hw; simp [s, hw])]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    fun w _ => (Valued.toNormedField.norm_le_iff).2 (h w)
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DCountP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

theorem dCount : AMem → ABnfH → AOrb → DCount := by
  intro hM hB hO F _ _ _ c hc χ
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hKH : Kc c ≤ Hc c := le_sup_left
  have hzH : ∀ z, zc F z ∈ Hc c := fun z => Subgroup.mem_sup_right ⟨z, rfl⟩
  obtain ⟨-, -, hKK, hHd, -⟩ := hM F
  show Countable (GF F ⧸ Hc c) ∧ ∀ a : GF F,
    {ω : GF F ⧸ Hc c | ∃ h ∈ Hc c, ω = ((h * a : GF F) : GF F ⧸ Hc c)}.Finite
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨S, hS⟩ := hB F c hc
    have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
    have : Countable (GL (Fin 2) F) :=
      (show Function.Injective (Units.val : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F) from
        fun _ _ h => Units.ext h).countable
    refine Function.Surjective.countable
      (f := fun p : GL (Fin 2) F × S => ((jF F p.1 * p.2.1 : GF F) : GF F ⧸ Hc c)) ?_
    intro ω
    induction ω using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, -, x', hx', h, hh, e⟩ := hS x
      refine ⟨(b⁻¹, ⟨x', hx'⟩), QuotientGroup.eq.2 ?_⟩
      have hx : x = jF F b⁻¹ * x' * h := by rw [map_inv, mul_assoc, ← e, inv_mul_cancel_left]
      show (jF F b⁻¹ * x')⁻¹ * x ∈ Hc c
      rw [hx, inv_mul_cancel_left]
      exact hKH hh
  · obtain ⟨S, hS⟩ := hO F c hc a
    refine (S.finite_toSet.image (fun x : GF F => (x : GF F ⧸ Hc c))).subset ?_
    rintro ω ⟨h, hh, rfl⟩
    obtain ⟨k, hk, z, rfl⟩ := (hHd c h).1 hh
    obtain ⟨x', hx', h', hh', e⟩ := hS k (hKK c hk)
    refine ⟨x', hx', QuotientGroup.eq.2 ?_⟩
    have he : k * zc F z * a = x' * (h' * zc F z) := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.1 (zc_center z) a, ← mul_assoc, e, mul_assoc]
    rw [he, inv_mul_cancel_left]
    exact mul_mem (hKH hh') (hzH z)

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowMul
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.PrimitiveVectorLemmas

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
theorem exists_row (s : Fin 2 → F) (hs : s ≠ 0) : ∃ γ : GL (Fin 2) F, ∀ j, γ.val 1 j = s j := by
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := by
      intro h1; apply hs; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; s 0, s 1] (by simp [Matrix.det_fin_two, h1]), ?_⟩
    intro j; fin_cases j <;> rfl
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; s 0, s 1] (by simp [Matrix.det_fin_two, h0]), ?_⟩
    intro j; fin_cases j <;> rfl

theorem row_mul (s : Fin 2 → F) (γ : GL (Fin 2) F) (hγ : ∀ j, γ.val 1 j = s j) (x : GF F) (i : Fin 2) :
    rowF s x i = (jF F γ * x).val 1 i := by
  simp [rowF, jF, Matrix.mul_apply, Matrix.vecMul, dotProduct, hγ]

theorem row_zak (d a : (Af F)ˣ) (u : Af F) (k : GF F) (i : Fin 2) :
    (zc F d * aff a u * k).val 1 i = (d : Af F) * k.val 1 i := by
  simp [zc, aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply]

end UpperTheory.Esk.PrimitiveVectorLemmas

theorem UpperTheory.Esk.aRow : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ARow := by
  intro hM hI F _ _ s x
  refine ⟨fun hs => ?_, fun t k hk hrow => ?_⟩
  · obtain ⟨γ, hγ⟩ := UpperTheory.Esk.PrimitiveVectorLemmas.exists_row s hs
    obtain ⟨d, a, u, k, hk, he⟩ := hI F (UpperTheory.Esk.jF F γ * x)
    refine ⟨d, k, hk, fun i => ?_⟩
    rw [UpperTheory.Esk.PrimitiveVectorLemmas.row_mul s γ hγ x i, he, UpperTheory.Esk.PrimitiveVectorLemmas.row_zak]
  · obtain ⟨-, -, -, -, h5, -⟩ := hM F
    have key : ∀ w : Pl F, max ‖pLoc F w (k.val 1 0)‖ ‖pLoc F w (k.val 1 1)‖ = 1 := by
      intro w
      have h := (h5 k hk w).2
      refine le_antisymm (max_le (Valued.toNormedField.norm_le_one_iff.2 ((le_max_left _ _).trans h.le))
        (Valued.toNormedField.norm_le_one_iff.2 ((le_max_right _ _).trans h.le))) ?_
      rcases max_choice (Valued.v (pLoc F w (k.val 1 0))) (Valued.v (pLoc F w (k.val 1 1))) with hh | hh <;> rw [hh] at h
      · exact le_max_of_le_left (Valued.toNormedField.one_le_norm_iff.2 h.ge)
      · exact le_max_of_le_right (Valued.toNormedField.one_le_norm_iff.2 h.ge)
    have hw : ∀ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ =
        ‖pLoc F w (t : Af F)‖ := by
      intro w
      rw [hrow 0, hrow 1, map_mul, map_mul, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ (norm_nonneg _), key w, mul_one]
    show ∏ᶠ w : Pl F, max ‖pLoc F w (UpperTheory.Esk.rowF s x 0)‖ ‖pLoc F w (UpperTheory.Esk.rowF s x 1)‖ = ∏ᶠ w : Pl F, ‖pLoc F w (t : Af F)‖
    exact finprod_congr hw
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.JFSa
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.AdelicNormalFormLemmas

theorem key {R : Type} [CommRing R] (c α r e r' e' : Rˣ) (u y0 : R) (k : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u * k) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0 * k)) := by
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) r * aff r' 0 *
      (aff 1 (((r'⁻¹ : Rˣ) : R) * (((α⁻¹ : Rˣ) : R) * u - y0)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) e * aff e' 0)) := by
    have hc := Units.inv_mul c
    have ha := Units.inv_mul α
    have hr := Units.mul_inv r'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [aff, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply] <;>
      first
      | linear_combination (((α⁻¹ : Rˣ) : R) * α * r * e * r' * e') * hc + ((r : R) * e * r' * e') * ha
      | linear_combination ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hc - ((r : R) * e * (((α⁻¹ : Rˣ) : R) * u - y0)) * hr
      | linear_combination ((r : R) * e) * hc
  calc _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹ * aff α⁻¹ (-y0) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (c * r * e) * aff (α * r' * e') u)) * k := by group
    _ = _ := by rw [h1]; group

theorem jF_sa {F : Type} [Field F] [NumberField F] (c α : Fˣ) (β : F) :
    UpperTheory.Esk.jF F (Matrix.GeneralLinearGroup.scalar (Fin 2) c * aff α β) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ratU F c) * aff (ratU F α) (algebraMap F (Af F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperTheory.Esk.jF, ratU, aff, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply]

end UpperTheory.Esk.AdelicNormalFormLemmas

open UpperTheory.Esk.AdelicNormalFormLemmas in
theorem UpperTheory.Esk.aBnf : UpperTheory.Esk.AMem → UpperTheory.Esk.AIw → UpperTheory.Esk.ACls → UpperTheory.Esk.AAdd → UpperTheory.Esk.ABnf := by
  intro hM hI hC hA F _ _
  classical
  obtain ⟨T, hT⟩ := hC F
  refine ⟨(T ×ˢ T).image (fun p => zc F p.1 * aff p.2 0), fun x => ?_⟩
  obtain ⟨d, a, u, k, hk, rfl⟩ := hI F x
  obtain ⟨y, e, r, hr, he, hd⟩ := hT d
  obtain ⟨y', e', r', hr', he', ha⟩ := hT a
  obtain ⟨y0, hy0⟩ := hA F r' ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u)
  have hK := (hM F).2.2.2.2.2.2.2
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) y⁻¹ * aff y'⁻¹ (-y0), ?_, zc F r * aff r' 0,
    Finset.mem_image.2 ⟨(r, r'), Finset.mem_product.2 ⟨hr, hr'⟩, rfl⟩,
    aff 1 (((r'⁻¹ : (Af F)ˣ) : Af F) * ((((ratU F y')⁻¹ : (Af F)ˣ) : Af F) * u - algebraMap F (Af F) y0)) *
      (zc F e * aff e' 0 * k), ?_, ?_⟩
  · simp [aff, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  · exact Subgroup.mul_mem _ ((hK 1 (by simp)).2 _ hy0)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK e he).1 ((hK e' he').2 0 (zero_mem _))) hk)
  · rw [jF_sa, map_inv, map_inv, map_neg, hd, ha]
    exact key (ratU F y) (ratU F y') r e r' e' u (algebraMap F (Af F) y0) k
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.MapScalarCenter
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalarMap

theorem central_of_map {K L : Type} [Field K] [Field L] (f : K →+* L) {g : GL (Fin 2) K}
    (h : Matrix.GeneralLinearGroup.map f g ∈ Subgroup.center (GL (Fin 2) L)) :
    g ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [Subgroup.mem_center_iff] at h ⊢
  intro δ
  have e := h (Matrix.GeneralLinearGroup.map f δ)
  rw [← map_mul, ← map_mul] at e
  apply Units.ext
  exact Matrix.map_injective f.injective (congrArg Units.val e)

theorem map_scalar_center {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) z) ∈ Subgroup.center (GL (Fin 2) S) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end UpperTheory.Esk.CentralScalarMap

namespace UpperTheory.Esk

open CentralScalarMap in
theorem dTwo : AMem → DTwo := by
  intro hA F _ _ _ c χ ⟨u, hu, hu2⟩ ω S hS hfin
  obtain ⟨-, -, -, hH, -⟩ := hA F
  have hc0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hc0 (p := 2) ?_⟩
  intro p hp hd
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨γ, hγ⟩ := exists_prime_orderOf_dvd_card' (G := S) p hd
  set g : GL (Fin 2) F := (γ : PG F).out with hg
  have hmk : ((g : PG F)) = (γ : PG F) := QuotientGroup.out_eq' _
  have hgp : g ^ p ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, ← Subgroup.coe_pow, ← hγ, pow_orderOf_eq_one,
      Subgroup.coe_one]
  have hst : (γ : PG F) • ω = ω := hS γ.2
  obtain ⟨x, hx⟩ : ∃ x : GF F, ((x : GF F ⧸ Hc c) : (mkDat c χ).Om) = ω := QuotientGroup.mk_surjective ω
  have h1 : ((jF F g * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := by
    rw [← hmk, ← hx] at hst
    exact hst
  have h2 : x⁻¹ * (jF F g * x) ∈ Hc c := QuotientGroup.eq.1 h1.symm
  obtain ⟨k, hk, z, hkz⟩ := (hH c _).1 h2
  obtain ⟨z0, hz0⟩ := jF_center hgp
  have hzc : ∀ z, zc F z ∈ Subgroup.center (GF F) := zc_center
  have hyp : (x⁻¹ * (jF F g * x)) ^ p = zc F z0 := by
    have := conj_pow (a := x⁻¹) (b := jF F g) (i := p)
    rw [inv_inv] at this
    rw [← mul_assoc, this, ← map_pow, hz0, Subgroup.mem_center_iff.1 (hzc _) x⁻¹, inv_mul_cancel_right]
  have hkp : k ^ p = zc F (z0 * (z ^ p)⁻¹) := by
    have e1 : (k * zc F z) ^ p = k ^ p * zc F z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.1 (hzc z) k) p
    rw [map_mul, map_inv, map_pow, ← hyp, hkz, e1, mul_inv_cancel_right]
  set P := Matrix.GeneralLinearGroup.map (n := Fin 2) (pLoc F u) with hP
  have hPz : ∀ z, P (zc F z) ∈ Subgroup.center _ := fun z => map_scalar_center _ z
  have hku : P k ∈ K1 u (c u) := Subgroup.mem_iInf.1 hk u
  have hkc := locTwo F u (c u) hu hu2 _ hku p (hp.odd_of_ne_two hne) (by rw [← map_pow, hkp]; exact hPz _)
  have hc2 : P (x⁻¹ * (jF F g * x)) ∈ Subgroup.center _ := by
    rw [hkz, map_mul]; exact mul_mem hkc (hPz z)
  have hc3 : P (jF F g) ∈ Subgroup.center _ := by
    have := (Subgroup.normal_of_characteristic _).conj_mem _ hc2 (P x)
    simpa [mul_assoc] using this
  have hcen : g ∈ Subgroup.center (GL (Fin 2) F) :=
    central_of_map ((pLoc F u).comp (algebraMap F (Af F))) hc3
  have h1' : (γ : PG F) = 1 := by
    rw [← hmk]; exact (QuotientGroup.eq_one_iff _).2 hcen
  have : γ = 1 := Subtype.ext h1'
  rw [this, orderOf_one] at hγ
  exact hp.one_lt.ne hγ

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DProdP
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightProductFormula

theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = sg v x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

theorem rowF_apply {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x : GF F) (i : Fin 2) :
    rowF s x i = algebraMap F (Af F) (s 0) * x.val 0 i + algebraMap F (Af F) (s 1) * x.val 1 i := by
  simp [rowF, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem det_id {F : Type} [Field F] [NumberField F] (s s' : Fin 2 → F) (x : GF F) :
    algebraMap F (Af F) (s 0 * s' 1 - s 1 * s' 0) * (Matrix.GeneralLinearGroup.det x : Af F) =
      rowF s x 0 * rowF s' x 1 - rowF s x 1 * rowF s' x 0 := by
  rw [rowF_apply, rowF_apply, rowF_apply, rowF_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [map_sub, map_mul]
  ring

end UpperTheory.Esk.HeightProductFormula

namespace UpperTheory.Esk

open HeightProductFormula in
theorem dProd : AMem → AMono → ARow → DProd := by
  intro hM hMo hR F _ _ _ c _ χ s s' hΔ x
  obtain ⟨hpos, hmul, -, hprod⟩ := UpperTheory.V.Sd.Hm.absf F
  have hs : s ≠ 0 := fun h => hΔ (by simp [h])
  have hs' : s' ≠ 0 := fun h => hΔ (by simp [h])
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s' x).1 hs'
  have hn : nF s x = absF t := (hR F s x).2 t k hk ht
  have hn' : nF s' x = absF t' := (hR F s' x).2 t' k' hk' ht'
  obtain ⟨hK, hO, -⟩ := hM F
  have hle : ∀ (g : GF F), g ∈ K0 F → ∀ i j (w : Pl F), Valued.v (pLoc F w (g.val i j)) ≤ 1 :=
    fun g hg i j w => (hO _).1 (((hK g).1 hg).1 i j) w
  set Δ := s 0 * s' 1 - s 1 * s' 0 with hΔd
  set U1 : (Af F)ˣ := ratU F (Units.mk0 Δ hΔ) * Matrix.GeneralLinearGroup.det x
  have key : absF U1 ≤ absF (t * t') := by
    refine hMo F _ _ fun w => ?_
    have e : (U1 : Af F) = (t * t' : (Af F)ˣ) * (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0) := by
      change algebraMap F (Af F) Δ * (Matrix.GeneralLinearGroup.det x : Af F) = _
      rw [det_id, ht, ht, ht', ht', Units.val_mul]
      ring
    rw [e, map_mul, map_mul]
    have h1 : Valued.v (pLoc F w (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0)) ≤ 1 := by
      rw [map_sub, map_mul, map_mul]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 0 w) (hle k' hk' 1 1 w)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 1 w) (hle k' hk' 1 0 w)
    calc _ ≤ Valued.v (pLoc F w ((t * t' : (Af F)ˣ) : Af F)) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _
  have hU1 : absF U1 = absF (ratU F (Units.mk0 Δ hΔ)) * absF (Matrix.GeneralLinearGroup.det x) := hmul _ _
  have hP := hprod (Units.mk0 Δ hΔ)
  change (∏ v, |reAt v Δ|) * absF (ratU F (Units.mk0 Δ hΔ)) = 1 at hP
  simp only [reAt_eq] at hP
  change absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * (absF (Matrix.GeneralLinearGroup.det x) / nF s' x ^ 2) ≤
    ∏ v, sg v Δ ^ 2
  rw [hn, hn']
  have hsq : ∏ v, sg v Δ ^ 2 = (∏ v, |sg v Δ|) ^ 2 := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun v _ => (sq_abs _).symm
  rw [hsq]
  set P := ∏ v, |sg v Δ|
  set R := absF (ratU F (Units.mk0 Δ hΔ))
  set A := absF (Matrix.GeneralLinearGroup.det x)
  have hA := hpos (Matrix.GeneralLinearGroup.det x)
  have hT := hpos t
  have hT' := hpos t'
  have hRp := hpos (ratU F (Units.mk0 Δ hΔ))
  have hPp : 0 ≤ P := Finset.prod_nonneg fun v _ => abs_nonneg _
  rw [hU1, hmul t t'] at key
  have hA2 : A ≤ absF t * absF t' * P := by
    have : A = P * (R * A) := by rw [← mul_assoc, hP, one_mul]
    rw [this, mul_comm (absF t * absF t') P]
    exact mul_le_mul_of_nonneg_left key hPp
  rw [div_mul_div_comm, div_le_iff₀ (by positivity), ← sq, ← mul_pow, ← mul_pow]
  exact pow_le_pow_left₀ hA.le (by linarith) 2

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowFSmul
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightFunctionLemmas

variable {F : Type} [Field F] [NumberField F]

theorem nF_eq (s : Fin 2 → F) (x : GF F) :
    nF s x = ∏ᶠ w : Pl F, max ‖pLoc F w (rowF s x 0)‖ ‖pLoc F w (rowF s x 1)‖ := rfl

theorem rowF_jF (s : Fin 2 → F) (γ : GL (Fin 2) F) (x : GF F) :
    rowF s (jF F γ * x) = rowF (s ᵥ* γ.val) x := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((s ᵥ* γ.val) i)) =
      (fun i => algebraMap F (Af F) (s i)) ᵥ* (jF F γ).val := by
    funext i
    exact RingHom.map_vecMul (algebraMap F (Af F)) γ.val s i
  rw [h, Units.val_mul, Matrix.vecMul_vecMul]

theorem rowF_smul (s : Fin 2 → F) (a : F) (x : GF F) (i : Fin 2) :
    rowF (a • s) x i = algebraMap F (Af F) a * rowF s x i := by
  unfold rowF
  have h : (fun i => algebraMap F (Af F) ((a • s) i)) = algebraMap F (Af F) a • (fun i => algebraMap F (Af F) (s i)) := by
    funext i
    simp [map_mul]
  rw [h, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]

theorem det_jF (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F γ) = ratU F (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  change (γ.val.map (algebraMap F (Af F))).det = algebraMap F (Af F) γ.val.det
  exact (RingHom.map_det (algebraMap F (Af F)) γ.val).symm

variable [IsTotallyReal F]

theorem nF_pos (hR : ARow) {s : Fin 2 → F} (hs : s ≠ 0) (x : GF F) : 0 < nF s x := by
  obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
  rw [(hR F s x).2 t k hk h]
  exact (Hm.absf F).1 t

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem prod_rat (a : Fˣ) : (∏ v, |sg v (a : F)|) * absF (ratU F a) = 1 := by
  have := (Hm.absf F).2.2.2 a
  simp only [reAt_eq] at this
  exact this

end UpperTheory.Esk.HeightFunctionLemmas

open UpperTheory.Esk.HeightFunctionLemmas in
theorem UpperTheory.Esk.dHt : UpperTheory.Esk.ARow → UpperTheory.Esk.DHt := by
  intro hR F _ _ _ c _ χ
  refine ⟨fun s hs x => ?_, fun s hs γ x => ?_, fun s hs a ha x => ?_⟩
  · change 0 < absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2
    exact div_pos ((Hm.absf F).1 _) (pow_pos (nF_pos hR hs x) 2)
  · change absF (Matrix.GeneralLinearGroup.det (jF F γ * x)) / nF s (jF F γ * x) ^ 2 * ∏ v, |sg v γ.val.det| =
      absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2
    have hP := prod_rat (Matrix.GeneralLinearGroup.det γ)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hP
    rw [map_mul, det_jF, (Hm.absf F).2.1, nF_eq s, rowF_jF, ← nF_eq]
    calc absF (ratU F (Matrix.GeneralLinearGroup.det γ)) * absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2 *
          ∏ v, |sg v γ.val.det|
        = ((∏ v, |sg v γ.val.det|) * absF (ratU F (Matrix.GeneralLinearGroup.det γ))) *
          (absF (Matrix.GeneralLinearGroup.det x) / nF (s ᵥ* γ.val) x ^ 2) := by ring
      _ = _ := by rw [hP, one_mul]
  · change absF (Matrix.GeneralLinearGroup.det x) / nF (a • s) x ^ 2 =
      absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * ∏ v, sg v a ^ 2
    obtain ⟨t, k, hk, h⟩ := (hR F s x).1 hs
    have h1 := (hR F s x).2 t k hk h
    have h2 : nF (a • s) x = absF (ratU F (Units.mk0 a ha)) * nF s x := by
      rw [(hR F (a • s) x).2 (ratU F (Units.mk0 a ha) * t) k hk (fun i => by
        rw [rowF_smul, h i, Units.val_mul, mul_assoc]; rfl), (Hm.absf F).2.1, h1]
    have hP := prod_rat (Units.mk0 a ha)
    simp only [Units.val_mk0] at hP
    have hA := (Hm.absf F).1 (ratU F (Units.mk0 a ha))
    have hN := nF_pos hR hs x
    have hsq : ∏ v, sg v a ^ 2 = (∏ v, |sg v a|) ^ 2 := by
      rw [← Finset.prod_pow]; simp [sq_abs]
    rw [h2, hsq, eq_inv_of_mul_eq_one_left hP]
    field_simp
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.PlaceEq
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.BoxMapsToLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

lemma place_eq (v : InfinitePlace F) (t : F) : v t = |sg v t| := by
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.norm_embedding_of_isReal _ t).symm

lemma injOn (R : ℝ) : Set.InjOn (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R} := by
  intro t ht t' ht' h
  by_contra hne
  let a : 𝓞 F := ⟨t - t', ht.1.sub ht'.1⟩
  have ha : a ≠ 0 := by
    intro h0
    apply hne
    have h1 : ((a : 𝓞 F) : F) = 0 := by rw [h0]; rfl
    exact sub_eq_zero.1 h1
  have hlt : ∀ v : InfinitePlace F, v (a : F) < 1 := by
    intro v
    have hv := congrFun h v
    simp only at hv
    rw [place_eq]
    show |sg v (t - t')| < 1
    rw [map_sub]
    exact Int.abs_sub_lt_one_of_floor_eq_floor hv
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

open Classical in
lemma mapsTo (R : ℝ) : Set.MapsTo (fun t : F => fun v : InfinitePlace F => ⌊sg v t⌋)
    {t : F | IsIntegral ℤ t ∧ ∀ v : InfinitePlace F, v t ≤ R}
    ((Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊ : Finset _) : Set _) := by
  intro t ht
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro v
  have h1 := ht.2 v
  rw [place_eq, abs_le] at h1
  have hc : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  constructor
  · rw [Int.le_floor]
    push_cast
    linarith [h1.1]
  · have h2 : ((⌊sg v t⌋ : ℤ) : ℝ) ≤ ((⌈R⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.floor_le (sg v t), h1.2]
    exact_mod_cast h2

end UpperTheory.Esk.BoxMapsToLemmas

open Classical in
theorem UpperTheory.Esk.dBox : UpperTheory.Esk.DBox := by
  intro F _ _ _
  refine ⟨5 ^ Fintype.card (InfinitePlace F), fun R hR => ?_⟩
  set d := Fintype.card (InfinitePlace F)
  set T := (Fintype.piFinset fun _ : InfinitePlace F => Finset.Icc (-(⌈R⌉₊ : ℤ)) ⌈R⌉₊)
  refine ⟨Set.Finite.of_injOn (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn _ (BoxMapsToLemmas.mapsTo R) (BoxMapsToLemmas.injOn R) T.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  have h2 : T.card = (2 * ⌈R⌉₊ + 1) ^ d := by
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  have h3 : ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ≤ 5 * max 1 R := by
    have := Nat.ceil_lt_add_one hR
    have hm1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
    have hmR : R ≤ max 1 R := le_max_right _ _
    push_cast
    linarith
  have h4 : (max 1 R) ^ d ≤ 1 + R ^ d := by
    rcases le_total R 1 with h | h
    · rw [max_eq_left h, one_pow]
      linarith [pow_nonneg hR d]
    · rw [max_eq_right h]
      linarith [zero_le_one' ℝ]
  calc (_ : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h1
    _ = ((2 * ⌈R⌉₊ + 1 : ℕ) : ℝ) ^ d := by rw [h2]; push_cast; ring
    _ ≤ (5 * max 1 R) ^ d := pow_le_pow_left₀ (by positivity) h3 _
    _ = 5 ^ d * (max 1 R) ^ d := mul_pow _ _ _
    _ ≤ 5 ^ d * (1 + R ^ d) := mul_le_mul_of_nonneg_left h4 (by positivity)
end
end
