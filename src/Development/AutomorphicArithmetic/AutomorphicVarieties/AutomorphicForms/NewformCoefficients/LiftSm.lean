module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftSm
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftSm :
    UpperTheory.V.Af.Nf.LiftSm := by
  intro k M hM f φ hφ
  refine ⟨fun γ g => ?_, fun u hu g => ?_, fun hf g => ?_⟩
  · obtain ⟨γ', h, u, hu, rfl⟩ := decomp M hM g
    rw [← mul_assoc, ← map_mul, hφ _ _ _ hu, hφ _ _ _ hu]
  · obtain ⟨γ', h, u', hu', rfl⟩ := decomp M hM g
    rw [mul_assoc, mul_assoc, ← map_mul, hφ _ _ _ hu', hφ _ _ _ (mul_mem hu' hu)]
  · obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
    let L : TR.Lie ℚ 2 → (Fin 2 → Fin 2 → ℝ) := fun x i j => ∑ l, h.val i l * x l j Rat.infinitePlace
    have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L := by
      refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ContDiff.sum fun l _ => contDiff_const.mul ?_
      exact (contDiff_apply ℝ _ Rat.infinitePlace).comp ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ l))
    have hLy : ∀ y : GL (Fin 2) (TR.Rinf ℚ),
        Matrix.of (L (TR.toL y.val)) = (h * Matrix.GeneralLinearGroup.map ev y).val := fun y => rfl
    refine ((archSm k f hf).comp hL.contDiffOn fun x hx => ?_).congr fun x hx => ?_
    · obtain ⟨y, hy⟩ := id hx
      have e : x = TR.toL y.val := hy.symm
      subst e
      change (Matrix.of (L (TR.toL y.val))).det ≠ 0
      rw [hLy]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
    · obtain ⟨y, hy⟩ := id hx
      have e : x = TR.toL y.val := hy.symm
      subst e
      rw [TR.chart_val, ← upR_ev, mul_assoc, mul_assoc, ← upR_comm, ← mul_assoc (upR h), ← map_mul, hφ _ _ _ hu,
        Function.comp_apply, arch, hLy]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftEx
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private noncomputable def dnR : GA ℚ 2 →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map ev).comp (Matrix.GeneralLinearGroup.map (TR.pInf ℚ))

private theorem dnR_upR (h : GL (Fin 2) ℝ) : dnR (upR h) = h := by
  show Matrix.GeneralLinearGroup.map ev (Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (TR.infGL ℚ 2 _)) = h
  rw [TR.pInf_infGL]
  exact Units.ext (Matrix.ext fun i j => rfl)

private theorem dnR_finGL (u : GL (Fin 2) (Af ℚ)) : dnR (finGL ℚ 2 u) = 1 := by
  show Matrix.GeneralLinearGroup.map ev (Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (finGL ℚ 2 u)) = 1
  rw [TR.pInf_finGL, map_one]

private theorem pFin_upR (h : GL (Fin 2) ℝ) : Matrix.GeneralLinearGroup.map (pFin ℚ) (upR h) = 1 :=
  TR.pFin_infGL _

private theorem comp_eq {γ γ' : GL (Fin 2) ℚ} {h h' : GL (Fin 2) ℝ} {u u' : GL (Fin 2) (Af ℚ)}
    (e : ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u) = ratGL ℚ 2 γ' * (upR h' * finGL ℚ 2 u')) :
    h' = toR (γ'⁻¹ * γ) * h ∧ toF (γ'⁻¹ * γ) = u' * u⁻¹ := by
  rw [ratGL_eq, ratGL_eq] at e
  have e1 := congrArg dnR e
  have e2 := congrArg (Matrix.GeneralLinearGroup.map (pFin ℚ)) e
  simp only [map_mul, dnR_upR, dnR_finGL, mul_one] at e1
  simp only [map_mul, pFin_upR, pFin_finGL, one_mul] at e2
  constructor
  · rw [map_mul, map_inv, mul_assoc, e1, inv_mul_cancel_left]
  · rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, e2, inv_mul_cancel_left]

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.liftEx :
    UpperTheory.V.Af.Nf.LiftEx := by
  intro k M hM f hf
  choose γ h u hu e using decomp M hM
  refine ⟨fun g => nsl k f (h g) UpperHalfPlane.I, fun γ' h' u' hu' => ?_⟩
  obtain ⟨e1, e2⟩ := comp_eq (e (ratGL ℚ 2 γ' * (upR h' * finGL ℚ 2 u')))
  have hK := (K1G M).mul_mem (hu (ratGL ℚ 2 γ' * (upR h' * finGL ℚ 2 u'))) ((K1G M).inv_mem hu')
  rw [← e2] at hK
  obtain ⟨δ, hδ, hc⟩ := (ratK M hM).1 _ hK
  have hd : h'.val.det ≠ 0 := (Matrix.isUnits_det_units h').ne_zero
  have hi := (nslInv k M f h'.val hd).1 hf δ hδ
  show nsl k f (h _).val UpperHalfPlane.I = _
  rw [e1, Units.val_mul]
  rcases hc with hc | hc
  · rw [hc, hi]
  · rw [hc, mul_assoc, (nslMul k f).2.1, hi]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem rot_nsl (k : ℕ) (x : Matrix (Fin 2) (Fin 2) ℝ) (h1 : x 0 0 ^ 2 + x 0 1 ^ 2 = 1) (hc : x 1 0 = -x 0 1)
    (hd : x 1 1 = x 0 0) : x.det = 1 ∧ ∃ c : ℂ, ∀ F : UpperHalfPlane → ℂ, nsl k F x UpperHalfPlane.I = c * F UpperHalfPlane.I := by
  have hdet : x.det = 1 := by rw [Matrix.det_fin_two, hc, hd]; linear_combination h1
  refine ⟨hdet, ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)), fun F => ?_⟩
  have h1' : (x 0 0 : ℂ) ^ 2 + (x 0 1 : ℂ) ^ 2 = 1 := by exact_mod_cast h1
  have hne : (x 1 0 : ℂ) * Complex.I + x 1 1 ≠ 0 := by
    intro h
    rw [hc, hd] at h
    push_cast at h
    have : (1 : ℂ) = 0 := by
      linear_combination ((x 0 1 : ℂ) * Complex.I + x 0 0) * h - h1' + (x 0 1 : ℂ) ^ 2 * Complex.I_sq
    exact one_ne_zero this
  have hq : ((x 0 0 : ℂ) * Complex.I + x 0 1) / ((x 1 0 : ℂ) * Complex.I + x 1 1) = (UpperHalfPlane.I : UpperHalfPlane) := by
    rw [div_eq_iff hne, hc, hd, UpperHalfPlane.coe_I]
    push_cast
    linear_combination (x 0 1 : ℂ) * Complex.I_sq
  unfold nsl
  rw [hdet, UpperHalfPlane.coe_I, hq]
  rw [sign_one, SignType.coe_one, Complex.ofReal_one, one_mul, UpperHalfPlane.ofComplex_apply]
  simp

private theorem rot_rt (k M : ℕ) (hM : 1 ≤ M) (f : UpperHalfPlane → ℂ) (φ : TR.Sm ℚ 2) (hφ : IsLift k M f φ.1)
    (x : GL (Fin 2) ℝ) (h1 : x.val 0 0 ^ 2 + x.val 0 1 ^ 2 = 1) (hc : x.val 1 0 = -x.val 0 1) (hd : x.val 1 1 = x.val 0 0) :
    ∃ c : ℂ, TR.rt ℚ 2 (upR x) φ = c • φ := by
  obtain ⟨hdet, c, hF⟩ := rot_nsl k x.val h1 hc hd
  refine ⟨c, Subtype.ext (funext fun g => ?_)⟩
  obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
  have e : ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u) * upR x = ratGL ℚ 2 γ * (upR (h * x) * finGL ℚ 2 u) := by
    rw [map_mul, mul_assoc, mul_assoc, ← upR_comm, mul_assoc]
  rw [TR.rt_apply, e, hφ γ _ u hu]
  change _ = c * φ.1 _
  rw [hφ γ h u hu, ← hF, (nslMul k f).1 h.val x.val h.det_ne_zero (by rw [hdet]; exact one_pos)]
  rfl

private theorem orth_cases {a b c d : ℝ} (h1 : a ^ 2 + b ^ 2 = 1) (h2 : c ^ 2 + d ^ 2 = 1)
    (h3 : a * c + b * d = 0) : (c = -b ∧ d = a) ∨ (c = b ∧ d = -a) := by
  have hD : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by
    linear_combination (c ^ 2 + d ^ 2) * h1 + h2 - (a * c + b * d) * h3
  rcases mul_eq_zero.1 hD with h | h
  · exact Or.inl ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩
  · exact Or.inr ⟨by linear_combination (-c) * h1 + a * h3 - b * h, by linear_combination (-d) * h1 + b * h3 + a * h⟩

private def epsG : GL (Fin 2) ℝ :=
  ⟨eps, eps, by simp [eps, Matrix.one_fin_two], by simp [eps, Matrix.one_fin_two]⟩

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftK :
    UpperTheory.V.Af.Nf.LiftK := by
  intro k M hM f φ hφ
  have : FiniteDimensional ℂ (Submodule.span ℂ ({φ, TR.rt ℚ 2 (upR epsG) φ} : Set (TR.Sm ℚ 2))) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ ({φ, TR.rt ℚ 2 (upR epsG) φ} : Set (TR.Sm ℚ 2)))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨r, rfl⟩
  set x : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.map ev (Unitary.toUnits r) with hx
  have e : TR.cptRep ℚ 2 r φ = TR.rt ℚ 2 (upR x) φ := by rw [hx, upR_ev]; rfl
  have hr : ∀ i j, x.val i 0 * x.val j 0 + x.val i 1 * x.val j 1 = if i = j then 1 else 0 := by
    intro i j
    have h := congrArg (fun m => ev (m i j)) r.2.2
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, map_add (f := _), map_mul, Matrix.one_apply] at h
    rw [apply_ite ev, map_one, map_zero] at h
    exact h
  have h1 : x.val 0 0 ^ 2 + x.val 0 1 ^ 2 = 1 := by have := hr 0 0; simp only [if_true] at this; linear_combination this
  have h2 : x.val 1 0 ^ 2 + x.val 1 1 ^ 2 = 1 := by have := hr 1 1; simp only [if_true] at this; linear_combination this
  have h3 : x.val 0 0 * x.val 1 0 + x.val 0 1 * x.val 1 1 = 0 := by simpa using hr 0 1
  change TR.cptRep ℚ 2 r φ ∈ _
  rw [e]
  clear_value x
  rcases orth_cases h1 h2 h3 with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · obtain ⟨c, hc⟩ := rot_rt k M hM f φ hφ x h1 hc hd
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · have hv : (epsG * x).val = !![-x.val 0 0, -x.val 0 1; x.val 1 0, x.val 1 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [epsG, eps, Matrix.mul_apply, Fin.sum_univ_two]
    obtain ⟨c, hc⟩ := rot_rt k M hM f φ hφ (epsG * x) (by rw [hv]; simpa using h1) (by rw [hv]; simpa using hc)
      (by rw [hv]; simpa using hd)
    have e2 : x = epsG * (epsG * x) := by
      rw [← mul_assoc, show epsG * epsG = 1 from Units.ext epsG.val_inv, one_mul]
    rw [e2, map_mul, map_mul, Module.End.mul_apply, hc, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCent
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af.Nf Matrix
open scoped MatrixGroups

private theorem idele_split (x : Ideles ℚ) :
    TR.infId ℚ (Units.map (TR.pInf ℚ).toMonoidHom x) * finId ℚ (Units.map (pFin ℚ).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  have h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  have h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin ℚ (sFin ℚ x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h, h2]
  · change pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h3, h4]

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem idele_dec (z : Ideles ℚ) : ∃ (r : ℚˣ) (t : (TR.Rinf ℚ)ˣ) (u : (Af ℚ)ˣ), (∀ v, 0 < t.val v) ∧ IsZU u ∧
    z = Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * (TR.infId ℚ t * finId ℚ u) := by
  obtain ⟨r, u, -, hu, e⟩ := ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)
  set w : Ideles ℚ := (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r)⁻¹ * z with hw
  have hz : z = Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * w := by rw [hw, mul_inv_cancel_left]
  have e1 : Units.map (pFin ℚ).toMonoidHom w = u := by
    rw [hw, map_mul, map_inv, e]
    exact inv_mul_cancel_left _ _
  have h0 := TR.unit_ne_zero (Units.map (TR.pInf ℚ).toMonoidHom w) Rat.infinitePlace
  rcases lt_or_gt_of_ne h0 with h | h
  · refine ⟨-r, Units.map (TR.pInf ℚ).toMonoidHom (-w), Units.map (pFin ℚ).toMonoidHom (-w), fun v => ?_, ?_, ?_⟩
    · rw [Subsingleton.elim v Rat.infinitePlace]
      change 0 < TR.pInf ℚ (-w.val) Rat.infinitePlace
      rw [map_neg]
      exact neg_pos.2 h
    · have : Units.map (pFin ℚ).toMonoidHom (-w) = -u := by
        rw [← e1]
        exact Units.ext (map_neg (pFin ℚ) w.val)
      rw [this]
      exact ⟨neg_mem hu.1, neg_mem hu.2⟩
    · rw [idele_split]
      refine hz.trans (Units.ext ?_)
      simp
  · refine ⟨r, Units.map (TR.pInf ℚ).toMonoidHom w, Units.map (pFin ℚ).toMonoidHom w, fun v => ?_, e1 ▸ hu, ?_⟩
    · rw [Subsingleton.elim v Rat.infinitePlace]
      exact h
    · rw [idele_split]
      exact hz

theorem UpperTheory.V.Af.Nf.liftCent :
    UpperTheory.V.Af.Nf.LiftCent := by
  intro k M hM χ ω hω f hf φ hφ z g
  obtain ⟨r, t, u, ht, hu, rfl⟩ := idele_dec z
  obtain ⟨γ, h, κ, hκ, rfl⟩ := decomp M hM g
  obtain ⟨δ, β, hδ, hβ, hK, hd⟩ := (ratK M hM).2 u hu
  have h1 : ω.1 (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) = 1 := ω.2.2 r
  have h2 := hω.unit u hu _ hd
  have s1 : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r) =
      ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r) := by
    ext i j
    by_cases e : i = j <;> simp [ratGL, Matrix.diagonal_apply, e, Matrix.algebraMap_matrix_apply]
  set T : GL (Fin 2) ℝ := GeneralLinearGroup.map ev (GeneralLinearGroup.scalar (Fin 2) t) with hT
  have s2 : GeneralLinearGroup.scalar (Fin 2) (TR.infId ℚ t) = upR T := by
    rw [hT, upR_ev]
    exact (corner_sc _ t).symm
  have s3 : GeneralLinearGroup.scalar (Fin 2) (finId ℚ u) = finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) u) :=
    (corner_sc _ u).symm
  have e : GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom r * (TR.infId ℚ t * finId ℚ u)) *
      (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 κ)) = ratGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) r * γ * β) *
        (upR ((toR β)⁻¹ * (T * h)) * finGL ℚ 2 ((toF β)⁻¹ * GeneralLinearGroup.scalar (Fin 2) u * κ)) := by
    have c : ∀ (x : GL (Fin 2) ℝ) (y : GL (Fin 2) (Af ℚ)) (w : GA ℚ 2), finGL ℚ 2 y * (upR x * w) = upR x * (finGL ℚ 2 y * w) :=
      fun x y w => by rw [← mul_assoc, ← upR_comm, mul_assoc]
    rw [map_mul, mul_assoc, ← mul_assoc _ (ratGL ℚ 2 γ),
      GeneralLinearGroup.scalar_commute (TR.infId ℚ t * finId ℚ u) (ratGL ℚ 2 γ), map_mul, s1, s2, s3,
      map_mul (ratGL ℚ 2), map_mul (ratGL ℚ 2), ratGL_eq β]
    simp only [mul_assoc, c]
    simp only [mul_assoc, map_mul, map_inv, mul_inv_cancel_left]
  have hβ' : (toR β).val = δ.1.map (Int.cast : ℤ → ℝ) := by
    ext i j
    have := congrFun (congrFun hβ i) j
    change (Rat.castHom ℝ) (β.val i j) = _
    rw [this]
    simp
  have e2 : ((toR β)⁻¹ * (T * h)).val = t.val Rat.infinitePlace • ((toR β)⁻¹ * h).val := by
    have : T.val = t.val Rat.infinitePlace • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      by_cases e : i = j <;> simp [hT, ev, Matrix.diagonal_apply, e]
    simp only [Units.val_mul, this, Matrix.smul_mul, Matrix.mul_smul, one_mul]
  have e3 := ((nslInv k M f ((toR β)⁻¹ * h).val ((toR β)⁻¹ * h).det_ne_zero).2 χ hf δ hδ)
  rw [← hβ', ← Units.val_mul, mul_inv_cancel_left] at e3
  rw [e, hφ _ _ _ (mul_mem hK hκ), hφ _ _ _ hκ, e2, (nslMul k f).2.2.1 _ _ (ht _), e3, map_mul, map_mul, h1, hω.pos t ht,
    one_mul, one_mul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, h2, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftLie
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchDer
open UpperHalfPlane hiding I
open scoped Manifold

namespace UpperTheory.V.Af.Nf

private noncomputable def cR (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i)

private noncomputable def cC (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cR i j)

private theorem cR_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cR i j x = x i j := rfl
private theorem cC_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cC i j x = (x i j : ℂ) := rfl

private theorem key (k : ℕ) (F : ℂ → ℂ) (F' : ℂ) (hF : HasDerivAt F F' Complex.I) (x0 : Fin 2 → Fin 2 → ℝ)
    (h00 : x0 0 0 = 1) (h01 : x0 0 1 = 0) (h10 : x0 1 0 = 0) (h11 : x0 1 1 = 1) :
    ∃ L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ,
      HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          F (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) L x0 ∧
      ∀ v : Fin 2 → Fin 2 → ℝ, L v = (k : ℂ) / 2 * (v 0 0 + v 1 1) * F Complex.I - k * (v 1 0 * Complex.I + v 1 1) * F Complex.I +
        (v 0 0 * Complex.I + v 0 1 + v 1 0 - v 1 1 * Complex.I) * F' := by
  have r : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => x i j) (cR i j) x0 := fun i j => (cR i j).hasFDerivAt
  have c : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => (x i j : ℂ)) (cC i j) x0 := fun i j => (cC i j).hasFDerivAt
  have hd := ((r 0 0).fun_mul (r 1 1)).fun_sub ((r 0 1).fun_mul (r 1 0))
  have hd2 := hd.rpow_const (p := (k : ℝ) / 2) (Or.inl (by simp [h00, h01, h10, h11]))
  have hd3 := Complex.ofRealCLM.hasFDerivAt.comp x0 hd2
  have hden := ((c 1 0).mul_const Complex.I).fun_add (c 1 1)
  have hnum := ((c 0 0).mul_const Complex.I).fun_add (c 0 1)
  have hne : (x0 1 0 : ℂ) * Complex.I + x0 1 1 ≠ 0 := by simp [h10, h11]
  have hz := (hasDerivAt_zpow (-(k : ℤ)) _ (Or.inl hne)).comp_hasFDerivAt x0 hden
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x0 hden
  have hq := hnum.fun_mul hi
  have hF2 : HasDerivAt F F' (((x0 0 0 : ℂ) * Complex.I + x0 0 1) * ((x0 1 0 : ℂ) * Complex.I + x0 1 1)⁻¹) := by
    simpa [h00, h01, h10, h11] using hF
  have hc := hF2.comp_hasFDerivAt x0 hq
  refine ⟨_, (hd3.fun_mul hz).fun_mul hc, fun v => ?_⟩
  simp [h00, h01, h10, h11, cR_apply, cC_apply]
  linear_combination (-(v 1 0 : ℂ) * F') * Complex.I_mul_I

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.archDer :
    UpperTheory.V.Af.Nf.ArchDer := by
  intro k f hf D hD
  have hF : DifferentiableAt ℂ (f ∘ ofComplex) Complex.I :=
    (UpperHalfPlane.mdifferentiable_iff.1 hf).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simp))
  obtain ⟨L, hL, hv⟩ := key k (f ∘ ofComplex) _ hF.hasDerivAt (Matrix.of.symm 1) (by simp) (by simp) (by simp) (by simp)
  have hpos : ∀ᶠ x : Fin 2 → Fin 2 → ℝ in nhds (Matrix.of.symm 1), 0 < x 0 0 * x 1 1 - x 0 1 * x 1 0 := by
    have hc : Continuous fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0 := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by simp)
  have hA : HasFDerivAt (arch k f) L (Matrix.of.symm 1) := by
    refine hL.congr_of_eventuallyEq (hpos.mono fun x hx => ?_)
    simp only [arch, nsl, Matrix.det_fin_two, Matrix.of_apply, abs_of_pos hx, sign_pos hx, Function.comp, coe_I,
      div_eq_mul_inv]
    simp
  have hI : (f ∘ ofComplex) Complex.I = f UpperHalfPlane.I := by
    rw [← coe_I, Function.comp, ofComplex_apply]
  simp only [hD, hA.fderiv, hv, hI]
  simp [Matrix.single]
  refine ⟨Or.inl (mul_comm _ _), ?_⟩
  linear_combination (k * f UpperHalfPlane.I) * Complex.I_mul_I
end

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd Topology
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private def incl : (Fin 2 → Fin 2 → ℝ) →L[ℝ] TR.Lie ℚ 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j _ => x i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem incl_one : incl (Matrix.of.symm 1) = TR.oneL ℚ 2 := by
  funext i j v
  change (1 : Matrix (Fin 2) (Fin 2) ℝ) i j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j v
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

open Classical in
private theorem incl_single (v : InfinitePlace ℚ) (i j : Fin 2) :
    incl (Matrix.of.symm (Matrix.single i j 1)) = TR.toL (Matrix.single i j (Pi.single v 1)) := by
  funext a b w
  obtain rfl : v = w := Subsingleton.elim _ _
  change Matrix.single i j (1 : ℝ) a b = Matrix.single i j (Pi.single v (1 : ℝ) : TR.Rinf ℚ) a b v
  by_cases h : i = a ∧ j = b <;> simp [Matrix.single, h]

private theorem chart_near {k M : ℕ} {f : ℍ → ℂ} {φ : GA ℚ 2 → ℂ} (hφ : IsLift k M f φ)
    (γ : GL (Fin 2) ℚ) (h : GL (Fin 2) ℝ) {u : GL (Fin 2) (Af ℚ)} (hu : u ∈ K1G M) :
    arch k (nsl k f h) =ᶠ[𝓝 (Matrix.of.symm 1)]
      TR.chart φ (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u)) ∘ incl := by
  have hc : Continuous fun x : Fin 2 → Fin 2 → ℝ => (Matrix.of x).det :=
    Continuous.matrix_det continuous_id
  have ho : {x : Fin 2 → Fin 2 → ℝ | 0 < (Matrix.of x).det} ∈ 𝓝 (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (isOpen_lt continuous_const hc).mem_nhds (by
      change 0 < (1 : Matrix (Fin 2) (Fin 2) ℝ).det
      simp)
  refine Filter.eventually_of_mem ho fun x hx => ?_
  have hx' : 0 < (Matrix.of x).det := hx
  let y : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of x) hx'.ne'
  have e : incl x = TR.toL (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) y).val := rfl
  rw [Function.comp_apply, e, TR.chart_val]
  change _ = φ (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u) * upR y)
  rw [mul_assoc, mul_assoc, ← upR_comm, ← mul_assoc (upR h), ← map_mul, hφ γ _ u hu, arch,
    (nslMul k f).1 _ _ h.det_ne_zero hx']
  rfl

end UpperTheory.V.Af.Nf

open UpperTheory.V UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftLie :
    UpperTheory.V.Af.Nf.LiftLie := by
  intro k M hM f hf φ hφ v
  have key : ∀ g, (TR.Eop v 0 1 φ).1 g - (TR.Eop v 1 0 φ).1 g = Complex.I * k * φ.1 g ∧
      (TR.Eop v 0 0 φ).1 g - (TR.Eop v 1 1 φ).1 g =
        Complex.I * ((TR.Eop v 0 1 φ).1 g + (TR.Eop v 1 0 φ).1 g) := by
    intro g
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
    rw [hφ γ h u hu]
    refine archDer k (nsl k f h) ((nslSl k f).2.2 hf _ h.det_ne_zero)
      (fun i j => (TR.Eop v i j φ).1 (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u))) fun i j => ?_
    rw [(chart_near hφ γ h hu).fderiv_eq,
      fderiv_comp _ (by rw [incl_one]; exact TR.differentiableAt_chart φ.2 _) incl.differentiableAt,
      incl_one, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, incl_single v]
    rfl
  exact ⟨Subtype.ext (funext fun g => (key g).1), Subtype.ext (funext fun g => (key g).2)⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCT
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ClassCT
open CongruenceSubgroup UpperTheory.V.Af.Nf
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm Pointwise

private lemma aux {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} (F : CuspForm Γ k) (z : ℍ) :
    ∃ N : ℕ, 0 < N ∧ Function.Periodic (fun t : ℝ => F (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, F (t +ᵥ z) = 0 := by
  have h1 : Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [← Subgroup.mem_strictPeriods_iff, Subgroup.strictPeriods_SL2Z]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨N, hN, -, hm⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    (Subgroup.IsArithmetic.is_commensurable (𝒢 := Γ)).1.relIndex_ne_zero h1
  have hP : (N : ℝ) ∈ Γ.strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    have := (Subgroup.mem_inf.mp hm).1
    rw [← AddChar.map_nsmul_eq_pow] at this
    simpa only [nsmul_eq_mul, mul_one] using this
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hper : ∀ w : ℍ, Function.Periodic (fun t : ℝ => F (t +ᵥ w)) N := fun w t => by
    have := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods F (t +ᵥ w) hP
    simp only
    rw [add_comm, add_vadd]
    exact this
  refine ⟨N, hN, hper z, ?_⟩
  have h0 := CuspFormClass.qExpansion_coeff_zero F hN' hP
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral F hN' hP 0 z.im_pos] at h0
  have hne : (1 / ((N : ℝ) : ℂ)) ≠ 0 := by
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simpa using this
  have h2 := (mul_eq_zero.mp h0).resolve_left hne
  set w : ℍ := (-z.re) +ᵥ z with hw
  have h3 : ∫ t in (0 : ℝ)..N, F (t +ᵥ w) = 0 := by
    rw [← h2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [pow_zero, div_one, one_mul]
    congr 1
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [hw]
  have h4 := (hper w).intervalIntegral_add_eq z.re 0
  rw [zero_add, h3] at h4
  rw [← h4]
  have h5 := intervalIntegral.integral_comp_add_right (fun t : ℝ => F (t +ᵥ w)) z.re (a := 0) (b := N)
  rw [zero_add, add_comm (N : ℝ)] at h5
  rw [← h5]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hw, vadd_vadd]
  congr 2
  ring

private lemma aux2 (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (hγ : 0 < (toR γ).val.det) (z : ℍ) : ∃ N : ℕ, 0 < N ∧
    Function.Periodic (fun t : ℝ => nsl k f (toR γ) (t +ᵥ z)) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f (toR γ) (t +ᵥ z) = 0 := by
  haveI : NeZero M := ⟨by omega⟩
  haveI : (ConjAct.toConjAct (toR γ)⁻¹ • (Gamma1 M : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    have := Subgroup.IsArithmetic.conj (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) γ⁻¹
    rw [← map_inv]
    exact this
  obtain ⟨N, hN, hp, hi⟩ := aux (CuspForm.translate f (toR γ)) z
  refine ⟨N, hN, ?_, ?_⟩
  · intro t
    have := hp t
    simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply]
    congr 1
  · simp only [(nslSl k f).2.1 _ hγ, Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    exact mul_eq_zero_of_right _ hi

theorem UpperTheory.V.Af.Nf.classCT :
    UpperTheory.V.Af.Nf.ClassCT := by
  intro k M hM f γ z
  have hne : (toR γ).val.det ≠ 0 := (toR γ).det_ne_zero
  rcases hne.lt_or_gt with h | h
  · let e : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by simp)
    have he : (toR (e * γ)).val = eps * (toR γ).val := by
      rw [map_mul, Units.val_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [toR, e, eps]
    have hd : 0 < (toR (e * γ)).val.det := by
      rw [he, Matrix.det_mul]
      simpa [eps] using h
    have := aux2 k M hM f (e * γ) hd z
    rwa [he, (nslMul k f).2.1] at this
  · exact aux2 k M hM f γ h z
end

noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem mobius_upper_half_plane_im_pos (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) :
    ((y 1 0 : ℂ) * Complex.I + y 1 1) ≠ 0 ∧
    0 < (((y 0 0 : ℂ) * Complex.I + y 0 1) / ((y 1 0 : ℂ) * Complex.I + y 1 1)).im := by
  rw [Matrix.det_fin_two] at hy
  have h0 : ((y 1 0 : ℂ) * Complex.I + y 1 1) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    rw [h1, h2] at hy
    simp at hy
  refine ⟨h0, ?_⟩
  have hn := Complex.normSq_pos.mpr h0
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ hn
  simp
  linarith

private theorem nsl_shift (k : ℕ) (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) :
    ∃ (c : ℂ) (z : ℍ), ∀ (F : ℍ → ℂ) (t : ℝ),
      nsl k F (!![1, t; 0, 1] * y) UpperHalfPlane.I = c * F (t +ᵥ z) := by
  obtain ⟨h0, h1⟩ := mobius_upper_half_plane_im_pos y hy
  refine ⟨((|y.det| ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((y 1 0 : ℂ) * Complex.I + y 1 1) ^ (-(k : ℤ)), ⟨_, h1⟩, fun F t => ?_⟩
  have hd : (!![1, t; 0, 1] * y).det = y.det := by rw [Matrix.det_mul]; simp
  have e10 : (!![1, t; 0, 1] * y) 1 0 = y 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (!![1, t; 0, 1] * y) 1 1 = y 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 : (!![1, t; 0, 1] * y) 0 0 = y 0 0 + t * y 1 0 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (!![1, t; 0, 1] * y) 0 1 = y 0 1 + t * y 1 1 := by simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold nsl
  rw [hd, e10, e11, e00, e01, sign_pos hy, UpperHalfPlane.coe_I]
  congr 2
  rw [← ofComplex_apply (t +ᵥ _)]
  congr 1
  rw [coe_vadd]
  show _ = (t : ℂ) + ((y 0 0 : ℂ) * Complex.I + y 0 1) / ((y 1 0 : ℂ) * Complex.I + y 1 1)
  simp only [SignType.coe_one]
  push_cast
  field_simp
  ring

private theorem pos_case (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : 0 < y.det) :
    ∃ N : ℕ, 0 < N ∧
      Function.Periodic (fun t : ℝ => nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = 0 := by
  obtain ⟨c, z, hc⟩ := nsl_shift k y hy
  obtain ⟨N, hN, hp, hi⟩ := classCT k M hM f γ z
  have key : ∀ t : ℝ, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = c * nsl k f (toR γ) (t +ᵥ z) := by
    intro t
    rw [← (nslMul k f).1 _ _ (toR γ).det_ne_zero (by rw [Matrix.det_mul]; simpa using hy), hc]
  simp only [key]
  refine ⟨N, hN, fun t => ?_, ?_⟩
  · exact congrArg (c * ·) (hp t)
  · rw [intervalIntegral.integral_const_mul, hi, mul_zero]

private def epsQ : GL (Fin 2) ℚ := aff (-1) 0

private theorem toR_epsQ : (toR epsQ).val = eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toR, epsQ, eps, aff]

private theorem all_case (k M : ℕ) (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (γ : GL (Fin 2) ℚ)
    (y : Matrix (Fin 2) (Fin 2) ℝ) (hy : y.det ≠ 0) :
    ∃ N : ℕ, 0 < N ∧
      Function.Periodic (fun t : ℝ => nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I) N ∧
      ∫ t in (0 : ℝ)..N, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = 0 := by
  rcases hy.lt_or_gt with hy | hy
  · have hy' : 0 < (eps * y).det := by
      rw [Matrix.det_mul]
      simp [eps, hy]
    obtain ⟨N, hN, hp, hi⟩ := pos_case k M hM f (γ * epsQ) (eps * y) hy'
    set G : ℝ → ℂ := fun t : ℝ => nsl k f ((toR (γ * epsQ)).val * (!![1, t; 0, 1] * (eps * y))) UpperHalfPlane.I with hG
    have key : ∀ t : ℝ, nsl k f ((toR γ).val * (!![1, t; 0, 1] * y)) UpperHalfPlane.I = G (-t) := by
      intro t
      have : eps * (!![1, -t; 0, 1] * eps) = !![1, t; 0, 1] := by
        simp [eps]
      simp only [hG, map_mul, Units.val_mul, toR_epsQ]
      rw [← this]
      simp only [Matrix.mul_assoc]
    simp only [key]
    refine ⟨N, hN, fun t => ?_, ?_⟩
    · show G (-(t + N)) = G (-t)
      rw [neg_add, ← sub_eq_add_neg]
      exact hp.sub_eq _
    · rw [intervalIntegral.integral_comp_neg G]
      have := hp.intervalIntegral_add_eq (-(N : ℝ)) 0
      simp only [neg_add_cancel, zero_add] at this
      rw [neg_zero, this]
      exact hi
  · exact pos_case k M hM f γ y hy

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftCT :
    UpperTheory.V.Af.Nf.LiftCT := by
  intro k M hM f φ hφ g
  obtain ⟨γ, h, u, hu, rfl⟩ := decomp M hM g
  have key : ∀ t : ℝ, φ (upR (aff 1 t) * (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u))) =
      nsl k f ((toR γ⁻¹).val * (!![1, t; 0, 1] * (toR γ * h).val)) UpperHalfPlane.I := by
    intro t
    have e : upR (aff 1 t) * (ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u)) =
        ratGL ℚ 2 γ * (upR (toR γ⁻¹ * (aff 1 t * (toR γ * h))) * finGL ℚ 2 u) := by
      rw [ratGL_eq, ← mul_assoc (upR (toR γ) * finGL ℚ 2 (toF γ)) (upR (toR γ⁻¹ * _)), mul_assoc (upR (toR γ)) _ (upR (toR γ⁻¹ * _)),
        ← upR_comm, ← mul_assoc (upR (toR γ)), ← map_mul, map_inv, mul_inv_cancel_left,
        ← mul_assoc _ (upR h), mul_assoc (upR (toR γ)) _ (upR h), ← upR_comm]
      simp only [map_mul, mul_assoc]
    rw [e, hφ γ _ u hu]
    rfl
  simp only [key]
  exact all_case k M hM f γ⁻¹ _ (toR γ * h).det_ne_zero
end
end
