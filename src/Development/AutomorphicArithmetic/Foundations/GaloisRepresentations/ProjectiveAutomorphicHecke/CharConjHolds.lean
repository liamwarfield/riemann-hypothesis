module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PThLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemiHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
noncomputable section

open NumberField Matrix Polynomial GlobalTheory.DefU GlobalTheory.UnitaryBC Formalism.BasicNotions
open UpperTheory.Gal.Schur (sch)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

def lamOf {E : Type} [Field E] {n : ℕ} (W : InfinitePlace E → DomWeight n) (m : InfinitePlace E → ℕ) (τ : E →+* ℂ) (i : Fin n) : ℕ :=
  if τ = (InfinitePlace.mk τ).embedding then m (InfinitePlace.mk τ) else ((W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ)).toNat

def TrRho : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (g : InfinitePlace E → GL (Fin n) ℂ),
  LinearMap.trace ℂ _ (Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W g) = ∏ v, LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (W v) (g v))

def TrSch : Prop := ∀ (n : ℕ) (lam : DomWeight n) (m : ℕ), (∀ i, 0 ≤ lam.w i + m) → ∀ (g : GL (Fin n) ℂ) (t : Fin n → ℂ),
  Function.Injective t → g.val.charpoly = ∏ i, (X - C (t i)) →
  LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) * (∏ i, t i) ^ m = sch (fun i => (lam.w i + m).toNat) t

def SchHom : Prop := ∀ (n : ℕ) (t : Fin n → ℂ), Function.Injective t →
  (∀ (lam : Fin n → ℕ) (c : ℂ), c ≠ 0 → sch lam (fun i => c * t i) = c ^ (∑ i, lam i) * sch lam t) ∧
    ∀ m : ℕ, sch (fun _ => m) t = (∏ i, t i) ^ m

def CharConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y P : GL (Fin n) E) (s : ℚˣ),
  (y.val.map (IsCMField.complexConj E))ᵀ * P.val * y.val = ((s : ℚ) : E) • P.val → ∀ (φ : E →+* ℂ) (t : Fin n → ℂ),
  y.val.charpoly.map φ = ∏ i, (X - C (t i)) →
  (∀ i, t i ≠ 0) ∧ y.val.charpoly.map (ComplexEmbedding.conjugate φ) = ∏ i, (X - C (((s : ℚ) : ℂ) / t i))

def WtCore : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (m : InfinitePlace E → ℕ),
  (∀ v i, 0 ≤ (W v).w i + m v) → ∀ (y P y' : GL (Fin n) E) (s : ℚˣ),
  (y.val.map (IsCMField.complexConj E))ᵀ * P.val * y.val = ((s : ℚ) : E) • P.val → y.val.charpoly.Separable → y'.val = (y⁻¹).valᵀ →
  LinearMap.trace ℂ _ (xi W (∑ v, ((∑ i, (W v).w i) + n * m v)) (y', s⁻¹)) = LocalSmoothExtension.schW (lamOf W m) (LocalSmoothExtension.invPol y.val.charpoly)

def AutEx : Prop := ∀ (E : Type) [Field E] [NumberField E] (τ τ₀ : E →+* ℂ), ∃ σ : ℂ ≃+* ℂ, ∀ y, σ (τ y) = τ₀ y

def WtAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ π : AutSub E n, (∃ W : Wt E n, π.finPart W ≠ ⊥) ∧
  ∀ W : Wt E n, π.finPart W ≠ ⊥ → ∀ τ lam, HasWeightAt π.V τ lam → lam = W.at τ

def EpsIff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (x ω : E), 0 < d → x ^ 2 = -(d : E) →
  ω ∈ IntermediateField.adjoin ℚ {x} → x ∈ IntermediateField.adjoin ℚ {ω} → ∀ τ φ : E →+* ℂ,
  (φ ω = (starRingEnd ℂ) (τ ω) ↔ φ x = -τ x)

def ExpSum : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (W : Wt E n) (m : InfinitePlace E → ℕ), (∀ v i, 0 ≤ (W v).w i + m v) → ∀ τ : E →+* ℂ,
  ((∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), (if φ x = -τ x then 1 else 0) * ∑ j, lamOf W m φ j : ℕ) : ℤ) +
      (n * m (InfinitePlace.mk τ) + if τ = (InfinitePlace.mk τ).embedding then ∑ i, (W (InfinitePlace.mk τ)).w i else 0) =
    mOf x W (∑ v, ((∑ i, (W v).w i) + n * m v)) τ

def ExpCore : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
  ∀ (W : Wt E n) (m : InfinitePlace E → ℕ), (∀ v i, 0 ≤ (W v).w i + m v) → (∀ τ, Antitone (lamOf W m τ)) ∧
  ∀ (τ τ₀ : E →+* ℂ) (σ : ℂ ≃+* ℂ), (∀ y, σ (τ y) = τ₀ y) → ∀ ε : (E →+* ℂ) → ℕ,
    (∀ φ : E →+* ℂ, ε ((σ : ℂ →+* ℂ).comp φ) = if φ x = -τ x then 1 else 0) → ∀ k : Fin n, ∃ (h : Fin n → ℕ) (i : Fin n),
      LocalSmoothExtension.IsHExp τ₀ ε (LocalSmoothExtension.conjWt σ (lamOf W m)) h ∧
        (h i : ℤ) = (((k : ℕ) : ℤ) - (W.at τ).w k) + mOf x W (∑ v, ((∑ i, (W v).w i) + n * m v)) τ

end UpperTheory.Gal.CertificateRingHomMap

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PVecWt
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.LKTrip GlobalTheory.LKDef GlobalTheory.LKMid Formalism.BasicNotions
open UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.Int.Geo.Pl

theorem vecEx_of (h0 : SeedGU) (h1 : WtAt) : VecEx := by
  intro E _ _ _ n l d hn hd x hx U hU w₀ hw₀ hT Up hUp hu
  obtain ⟨e, J, θ, χ, hJo, hJc, htf, -, -, hcusp, hφ⟩ := hT
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨W, hW⟩ := (h1 E n hn π).1
  let m : InfinitePlace E → ℕ := fun v => ∑ i, ((W v).w i).natAbs
  have hm : ∀ v i, 0 ≤ (W v).w i + m v := fun v i => by
    have : ((W v).w i).natAbs ≤ m v := Finset.single_le_sum (f := fun i => ((W v).w i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨S, Kw, Φ, κ, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h0 E n hn d x hd hx π W hW (∑ v, ((∑ i, (W v).w i) + n * m v)) Up hUp w₀ hw₀ hu
    J (χ.comp θ) hJo hJc hφ
  exact ⟨⟨π, rfl, W, hW, m, hm, _, rfl, J, χ.comp θ, hcusp, htf, S, Kw, Φ, κ, hw₀, a1, a2, a3, a4, a5, a6, a7, a8⟩⟩

theorem wtOf_of (h0 : WtCore) : WtOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V thQ hth B y hdeg hsep
  let y₀ : GL (Fin n) E × ℚˣ := y.1
  let β : GL (Fin n) E := B.β
  have hc : ∀ z : E, S.L.e.symm z = z := fun z => S.L.e.symm_apply_eq.2 (S.L_e z).symm
  have hmin : minpoly E y₀.1.val = y₀.1.val.charpoly := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (Matrix.isIntegral _)) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) ?_ |>.symm
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact hdeg.ge
  let Hc : Matrix (Fin n) (Fin n) E := (A.H n).map (IsCMField.complexConj E : E →+* E)
  have hu : IsUnit Hc.det := by
    rw [show Hc.det = _ from ((IsCMField.complexConj E : E →+* E).map_det _).symm]
    exact ((map_ne_zero _).2 (A.det_ne n)).isUnit
  have hy : y₀.1.val * β.val * (Hc⁻¹ * (y₀.1.val.map (IsCMField.complexConj E : E →+* E))ᵀ * Hc) = algebraMap ℚ _ (y₀.2 : ℚ) * β.val := y.2.1
  have hrel : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * ((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val * y₀.1.val =
      ((y₀.2 : ℚ) : E) • (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit.val * β⁻¹.val) := by
    rw [IsUnit.unit_spec]
    have e1 : (y₀.1.val.map (IsCMField.complexConj E))ᵀ * Hc = ((y₀.2 : ℚ) : E) • (Hc * β⁻¹.val * y₀.1⁻¹.val * β.val) := by
      have h2 := congrArg (fun M => Hc * β⁻¹.val * y₀.1⁻¹.val * M) hy
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h2
      rw [← Algebra.smul_def, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul] at h2
      simp only [Matrix.mul_assoc]
      rw [Rat.cast_smul_eq_qsmul]
      exact h2
    rw [e1]
    simp only [smul_mul_assoc, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul, Matrix.mul_one]
  have hsep' : y₀.1.val.charpoly.Separable := hmin ▸ hsep
  have key := h0 E n V.W V.m V.pos y₀.1 (((Matrix.isUnit_iff_isUnit_det _).2 hu).unit * β⁻¹) (thQ y₀).1 y₀.2
    (by rw [Units.val_mul, ← Matrix.mul_assoc]; exact hrel) hsep' (hth y₀).1
  have e2 : thQ y₀ = ((thQ y₀).1, y₀.2⁻¹) := Prod.ext rfl (hth y₀).2
  have e3 : LocalSmoothExtension.endPol S.L (minpoly E y₀.1.val) = LocalSmoothExtension.invPol y₀.1.val.charpoly := by
    unfold LocalSmoothExtension.endPol
    rw [hmin]
    refine congrArg LocalSmoothExtension.invPol (Polynomial.ext fun i => ?_)
    exact (Polynomial.coeff_map _ _).trans (hc _)
  rw [← V.jz_eq, ← e2, ← e3] at key
  exact key

theorem expOf_of (h0 : ExpCore) (h1 : AutEx) (h2 : WtAt) (h3 : EpsIff) : ExpOf := by
  intro E _ _ _ A n p _ S x U w₀ Up V d hd hx hG
  obtain ⟨a1, a2⟩ := h0 E n d x hd hx V.W V.m V.pos
  refine ⟨a1, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h1 E τ A.τ₀
  refine ⟨σ, hσ, fun lam hl j hj => ?_⟩
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hj
  have e : lam = V.W.at τ := (h2 E n S.facts.pos V.π).2 V.W V.hW τ lam (by rw [V.hV]; exact hl)
  subst e
  rw [V.jz_eq]
  refine a2 τ A.τ₀ σ hσ _ (fun φ => ?_) k
  have e1 : (starRingEnd ℂ) (A.τ₀ (A.ω : E)) = σ ((starRingEnd ℂ) (τ (A.ω : E))) := by
    rw [← IsCMField.complexEmbedding_complexConj, ← IsCMField.complexEmbedding_complexConj, hσ]
  have e2 : (σ (φ (A.ω : E)) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) ↔ φ x = -τ x := by
    rw [e1, σ.injective.eq_iff]
    exact h3 E d x A.ω hd hx hG.1 hG.2 τ φ
  exact if_congr e2 rfl rfl

end UpperTheory.Gal.Int.Geo.Pl

end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AgreeOfAdjoin
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.Qk58.agree_of_adjoin :
    ∀ {E : Type} [inst : Field E]
    [inst_1 : NumberField E] (φ ψ : E →+* ℂ) {a b : E},
    (φ : E → ℂ) a = (ψ : E → ℂ) a → b ∈ ℚ⟮a⟯ → (φ : E → ℂ) b = (ψ : E → ℂ) b := by
  intro E _ _ φ ψ a b ha hb
  induction hb using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact ha
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImagOfSq
theorem UpperTheory.Reformulated.B.Qh67.imag_of_sq :
    ∀ {c : ℂ} {d : ℕ},
    (0 : ℕ) < d → c ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) c = -c ∧ c ≠ (0 : ℂ) := by
  intro c d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : c.re * c.re - c.im * c.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : c.re * c.im + c.im * c.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : c.re * c.im = 0 := by linarith [mul_comm c.re c.im]
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg c.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext
    · simp [hre]
    · simp
  · rintro rfl
    simp at h1
    omega
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEqNegOfSq
theorem UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq :
    ∀ {z : ℂ} {d : ℕ},
    (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro z d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    simpa [pow_two] using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im h
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtCore
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem prod_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (f : (E →+* ℂ) → ℂ) :
    ∏ τ, f τ = ∏ v : InfinitePlace E, f v.embedding * f (ComplexEmbedding.conjugate v.embedding) := by
  rw [← Finset.prod_fiberwise Finset.univ (fun τ : E →+* ℂ => InfinitePlace.mk τ) f]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hs : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; exact (star_star τ).symm)
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hs, Finset.prod_pair (conjugate_ne v.embedding).symm]

private theorem exists_list {n : ℕ} (p : ℂ[X]) (hm : p.Monic) (hd : p.natDegree = n) (hs : p.Separable) :
    ∃ t : Fin n → ℂ, Function.Injective t ∧ p = ∏ i, (X - C (t i)) := by
  have hsp := IsAlgClosed.splits p
  have hnd := nodup_roots hs
  have hc : p.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.1 hsp, hd]
  let e := p.roots.toFinset.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : ℂ), fun a b h => e.symm.injective (Subtype.ext h), ?_⟩
  have h1 : ∏ i, (X - C ((e.symm i : ℂ))) = ∏ x ∈ p.roots.toFinset, (X - C x) := by
    rw [← Finset.prod_coe_sort p.roots.toFinset (fun x => (X - C x : ℂ[X]))]
    exact Fintype.prod_equiv e.symm _ _ fun _ => rfl
  rw [h1, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
  exact hsp.eq_prod_roots_of_monic hm

private theorem roots_list {n : ℕ} (t : Fin n → ℂ) :
    (∏ i, (X - C (t i)) : ℂ[X]).roots = Finset.univ.val.map t := by
  have : (∏ i, (X - C (t i)) : ℂ[X]) = ((Finset.univ.val.map t).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [this, roots_multiset_prod_X_sub_C]

theorem UpperTheory.Gal.CertificateRingHomMap.pWtCore_of :
    UpperTheory.Gal.CertificateRingHomMap.TrRho → UpperTheory.Gal.CertificateRingHomMap.TrSch → UpperTheory.Gal.CertificateRingHomMap.SchHom → UpperTheory.Gal.CertificateRingHomMap.CharConj → UpperTheory.Gal.CertificateRingHomMap.WtCore := by
  intro hTr hSch hHom hCC E _ _ _ n W m hm y P y' s hy hsep hy'
  have hex : ∀ v : InfinitePlace E, ∃ t : Fin n → ℂ, Function.Injective t ∧
      y.val.charpoly.map v.embedding = ∏ i, (X - C (t i)) := fun v =>
    exists_list _ ((charpoly_monic _).map _)
      (by rw [(charpoly_monic _).natDegree_map, charpoly_natDegree_eq_dim, Fintype.card_fin]) (hsep.map)
  choose t ht hχ using hex
  have hc := fun v => hCC E n y P s hy v.embedding (t v) (hχ v)
  have hinv : ((y'⁻¹ : GL (Fin n) E)).val = y.valᵀ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy', ← transpose_mul, Units.mul_inv, transpose_one]
  have hgp : ∀ v, (embAll E n y'⁻¹ v).val.charpoly = ∏ i, (X - C (t v i)) := fun v => by
    show (((y'⁻¹ : GL (Fin n) E)).val.map v.embedding).charpoly = _
    rw [hinv, charpoly_map, charpoly_transpose, hχ]
  have h0 : y.val.charpoly.coeff 0 ≠ 0 := by
    intro h
    have h2 := det_eq_sign_charpoly_coeff y.val
    rw [h, mul_zero] at h2
    exact (Matrix.isUnits_det_units y).ne_zero h2
  let g : (E →+* ℂ) → Fin n → ℂ := fun τ i =>
    if τ = (InfinitePlace.mk τ).embedding then (t (InfinitePlace.mk τ) i)⁻¹ else t (InfinitePlace.mk τ) i / ((s : ℚ) : ℂ)
  have gE : ∀ v : InfinitePlace E, g v.embedding = fun i => (t v i)⁻¹ := fun v => by
    funext i
    simp only [g, InfinitePlace.mk_embedding, if_true]
  have gC : ∀ v : InfinitePlace E, g (ComplexEmbedding.conjugate v.embedding) = fun i => t v i / ((s : ℚ) : ℂ) := fun v => by
    funext i
    simp only [g, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (conjugate_ne v.embedding)]
  have hL : LocalSmoothExtension.Lists (LocalSmoothExtension.invPol y.val.charpoly) g := by
    intro τ
    rw [LocalSmoothExtension.InvRoots_holds E _ h0 τ]
    obtain ⟨v, hv⟩ : ∃ v : InfinitePlace E, τ = v.embedding ∨ τ = ComplexEmbedding.conjugate v.embedding := by
      refine ⟨InfinitePlace.mk τ, ?_⟩
      rcases InfinitePlace.embedding_mk_eq τ with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; exact (star_star τ).symm)
    rcases hv with rfl | rfl
    · rw [gE, UpperTheory.Gal.W2.rts, hχ, roots_list, Multiset.map_map]
      rfl
    · rw [gC, UpperTheory.Gal.W2.rts, (hc v).2, roots_list, Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      simp only [Function.comp, inv_div]
  have lE : ∀ v : InfinitePlace E, lamOf W m v.embedding = fun _ => m v := fun v => by
    funext i
    simp only [lamOf, InfinitePlace.mk_embedding, if_true]
  have lC : ∀ v : InfinitePlace E, lamOf W m (ComplexEmbedding.conjugate v.embedding) =
      fun i => ((W v).w i + m v).toNat := fun v => by
    funext i
    simp only [lamOf, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (conjugate_ne v.embedding)]
  have hs0 : ((s : ℚ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have hpair : ∀ v : InfinitePlace E,
      UpperTheory.Gal.Schur.sch (lamOf W m v.embedding) (g v.embedding) *
        UpperTheory.Gal.Schur.sch (lamOf W m (ComplexEmbedding.conjugate v.embedding)) (g (ComplexEmbedding.conjugate v.embedding)) =
      (((s : ℚ) : ℂ)⁻¹) ^ (∑ i, ((W v).w i + m v).toNat) *
        LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (W v) (embAll E n y'⁻¹ v)) := fun v => by
    have hp0 : (∏ i, t v i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hc v).1 i
    have e1 := (hHom n (fun i => (t v i)⁻¹) (inv_injective.comp (ht v))).2 (m v)
    have e2 := (hHom n (t v) (ht v)).1 (fun i => ((W v).w i + m v).toNat) (((s : ℚ) : ℂ)⁻¹) (inv_ne_zero hs0)
    have e3 := hSch n (W v) (m v) (hm v) (embAll E n y'⁻¹ v) (t v) (ht v) (hgp v)
    have e4 : (fun i => t v i / ((s : ℚ) : ℂ)) = fun i => ((s : ℚ) : ℂ)⁻¹ * t v i := by
      funext i
      rw [div_eq_inv_mul]
    rw [lE, lC, gE, gC, e4, e1, e2, ← e3, Finset.prod_inv_distrib, inv_pow]
    field_simp
  have hJ : ∀ v : InfinitePlace E, ((∑ i, ((W v).w i + m v).toNat : ℕ) : ℤ) = (∑ i, (W v).w i) + n * m v := fun v => by
    push_cast
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hm v i), Finset.sum_add_distrib]
    simp
  rw [LocalSmoothExtension.schWEq_of E n (lamOf W m) _ g hL, prod_emb, Finset.prod_congr rfl fun v _ => hpair v, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hJ2 : (∑ v, ((∑ i, (W v).w i) + n * m v)) = ((∑ v, ∑ i, ((W v).w i + m v).toNat : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hJ v]
    push_cast
    rfl
  show LinearMap.trace ℂ _ (((((s⁻¹ : ℚˣ) : ℚ) : ℂ) ^ (∑ v, ((∑ i, (W v).w i) + n * m v))) •
    Representation.dual ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) y') = _
  rw [map_smul, Representation.dual_apply, LinearMap.trace_transpose', hJ2, zpow_natCast]
  have e5 := hTr E n W (embAll E n y'⁻¹)
  have e6 : ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) y'⁻¹ =
      Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (embAll E n y'⁻¹) := rfl
  have e7 : (((s⁻¹ : ℚˣ) : ℚ) : ℂ) = ((s : ℚ) : ℂ)⁻¹ := by push_cast; rfl
  rw [e6, e7, smul_eq_mul, e5]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrSch
noncomputable section

open Matrix Polynomial

namespace UpperTheory.Gal.CertificateRingHomMap

open UpperTheory.Gal.Schur in
private theorem den_eq {n : ℕ} (t : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))).det = vdm t := by
  have hm : (Matrix.of fun i j : Fin n => t i ^ (n - 1 - (j : ℕ))) =
      Matrix.projVandermonde (fun _ => (1 : ℂ)) t := by
    ext i j
    simp only [Matrix.projVandermonde_apply, one_pow, one_mul, Matrix.of_apply, Fin.val_rev]
    congr 1
    omega
  rw [hm, Matrix.det_projVandermonde]
  simp only [one_mul, vdm]

open UpperTheory.Gal.Schur in
private theorem num_eq' {n : ℕ} (l : Fin n → ℤ) (t : Fin n → ℂ) :
    (Matrix.of fun i j : Fin n => t i ^ (l j + (n - 1 - (j : ℕ) : ℕ))).det =
      altnZ (fun i => l i + n - 1 - (i : ℕ)) t := by
  rw [← Matrix.det_transpose]
  unfold altnZ
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  have := i.isLt
  omega

theorem pTrSch_of : TrSch := by
  intro n lam m hpos g t ht hchar
  obtain ⟨d, hd0, hdchar, htr⟩ := GlobalTheory.ContraChar.exists_eig lam g
  have key : ∀ e : Fin n → ℂ, (∏ i, (X - C (e i))).roots = Multiset.map e Finset.univ.val := by
    intro e
    have he : (∏ i, (X - C (e i))) = ((Finset.univ.val.map e).map fun a => X - C a).prod := by
      rw [Multiset.map_map]
      rfl
    rw [he, Polynomial.roots_multiset_prod_X_sub_C]
  have hroots : Multiset.map d Finset.univ.val = Multiset.map t Finset.univ.val := by
    rw [← key d, ← key t, ← hdchar, ← hchar]
  obtain ⟨π, hπ⟩ := GlobalTheory.ContraChar.exists_perm_of_map_eq d t hroots
  have ht0 : ∀ i, t i ≠ 0 := fun i => by rw [← hπ i]; exact hd0 _
  have hgt : ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n lam.w t = ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n lam.w d := by
    rw [← GlobalTheory.ContraChar.gtChar_perm lam d hd0 π]
    congr 1
    funext i
    exact (hπ i).symm
  have hw := GlobalTheory.CompanionTheory.RmCharacter.weylChar_eq_gtChar lam.w lam.anti t ht0 ht
  rw [htr, ← hgt, ← hw]
  unfold PositivityTheory.RgBcC.weylChar
  rw [num_eq' lam.w t, den_eq t]
  rw [UpperTheory.Gal.Schur.WeylTie_holds ℂ n lam.w m (fun i => (lam.w i + m).toNat) t
    (fun i => (Int.toNat_of_nonneg (hpos i)).symm) ht ht0]
  have hp : (∏ k, t k) ^ m ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => ht0 i)
  exact div_mul_cancel₀ _ hp

end UpperTheory.Gal.CertificateRingHomMap

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSchHom
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSchHom_of :
    UpperTheory.Gal.CertificateRingHomMap.SchHom := by
  intro n t _
  refine ⟨fun lam c _ => UpperTheory.Gal.Schur.SchurHomog_holds ℂ n lam t c, fun m => ?_⟩
  obtain ⟨h0, h1⟩ := UpperTheory.Gal.Schur.SchurDet_holds ℂ n t
  have h := h1 (fun _ => 0) m
  simp only [zero_add] at h
  rw [h, h0, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCharConj
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pCharConj_of :
    UpperTheory.Gal.CertificateRingHomMap.CharConj := by
  intro E _ _ _ n y P s h φ t ht
  set A : Matrix (Fin n) (Fin n) ℂ := (y : Matrix (Fin n) (Fin n) E).map φ with hAdef
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) E).map φ with hQdef
  set B : Matrix (Fin n) (Fin n) ℂ :=
    (y : Matrix (Fin n) (Fin n) E).map (NumberField.ComplexEmbedding.conjugate φ) with hBdef
  have hB : B = ((y : Matrix (Fin n) (Fin n) E).map (IsCMField.complexConj E)).map φ := by
    ext i j
    simp only [B, Matrix.map_apply]
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq,
      NumberField.IsCMField.complexEmbedding_complexConj]
  have hrel : Bᵀ * Q * A = ((s : ℚ) : ℂ) • Q := by
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map φ) h
    simp only [Matrix.map_mul] at h2
    rw [Matrix.transpose_map] at h2
    rw [hB, hQdef, hAdef, h2]
    ext i j
    simp [Matrix.map_apply]
  have hA : ((y : Matrix (Fin n) (Fin n) E).map φ).charpoly = ∏ i, (X - C (t i)) := by
    rw [Matrix.charpoly_map]; exact ht
  have hdetA : A.det ≠ 0 := by
    have hu : IsUnit (y : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
    rw [hAdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hdetQ : Q.det ≠ 0 := by
    have hu : IsUnit (P : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
    rw [hQdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero φ).mpr hu.ne_zero
  have hprodt : A.det = ∏ i, t i := by
    have e := congrArg (Polynomial.eval 0) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at e
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub] at e
    rw [map_zero, zero_sub, Matrix.det_neg, Fintype.card_fin] at e
    have e2 : ∏ i, -t i = (-1) ^ n * ∏ i, t i := by
      calc ∏ i, -t i = ∏ i, ((-1) * t i) := by simp
        _ = (-1) ^ n * ∏ i, t i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [e2] at e
    exact mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) e
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i hi
    apply hdetA
    rw [hprodt]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hpt : ∏ i, t i ≠ 0 := hprodt ▸ hdetA
  refine ⟨ht0, ?_⟩
  rw [← Matrix.charpoly_map]
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := {z : ℂ | z ≠ 0})
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    have key : (Matrix.scalar (Fin n) z - B).det * A.det =
        z ^ n * (-1) ^ n * (Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A).det := by
      have e1 : (Matrix.scalar (Fin n) z - Bᵀ) * Q * A = Q * (z • A - ((s : ℚ) : ℂ) • 1) := by
        rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_mul, sub_mul, hrel, mul_sub]
        simp [smul_mul_assoc, mul_smul_comm]
      have e2 : (Matrix.scalar (Fin n) z - B).det = (Matrix.scalar (Fin n) z - Bᵀ).det := by
        rw [← Matrix.eval_charpoly, ← Matrix.eval_charpoly, Matrix.charpoly_transpose]
      have e3 : z • A - ((s : ℚ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
          z • (-(Matrix.scalar (Fin n) (((s : ℚ) : ℂ) / z) - A)) := by
        rw [neg_sub, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, smul_sub, smul_smul,
          mul_div_cancel₀ _ hz]
      have e4 := congrArg Matrix.det e1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, e3, Matrix.det_smul, Matrix.det_neg,
        Fintype.card_fin, ← e2] at e4
      apply mul_left_cancel₀ hdetQ
      linear_combination e4
    have hAev := congrArg (Polynomial.eval (((s : ℚ) : ℂ) / z)) hA
    rw [Matrix.eval_charpoly, Polynomial.eval_prod] at hAev
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hAev
    rw [hAev, hprodt] at key
    rw [Matrix.eval_charpoly, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hfac : ∀ i, (z - ((s : ℚ) : ℂ) / t i) * t i = (z * -1) * (((s : ℚ) : ℂ) / z - t i) := by
      intro i
      field_simp [ht0 i, hz]
      ring
    have hq : (∏ i, (z - ((s : ℚ) : ℂ) / t i)) * ∏ i, t i =
        z ^ n * (-1) ^ n * ∏ i, (((s : ℚ) : ℂ) / z - t i) := by
      rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => hfac i),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    exact mul_right_cancel₀ hpt (key.trans hq.symm)
  · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PAutEx
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pAutEx_of :
    UpperTheory.Gal.CertificateRingHomMap.AutEx := by
  intro E _ _ τ τ₀
  obtain ⟨σ, hσ⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegreeAlt.exists_ringEquiv_comp τ τ₀
  exact ⟨σ, fun y => RingHom.congr_fun hσ y⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PEpsIff
noncomputable section

open NumberField

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem agree_of_adjoin {E : Type} [Field E] [NumberField E] (φ ψ : E →+* ℂ) {a b : E}
    (h : φ a = ψ a) (hb : b ∈ IntermediateField.adjoin ℚ {a}) : φ b = ψ b :=
  _root_.UpperTheory.Reformulated.B.Qk58.agree_of_adjoin φ ψ h hb

private theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z :=
  _root_.UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq hd hz

theorem pEpsIff_of : EpsIff := by
  intro E _ _ _ d x ω hd hx hω hx' τ φ
  have hτ : (τ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hc : ComplexEmbedding.conjugate τ x = -τ x := by
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg_of_sq hd hτ
  constructor
  · intro h
    have h' : φ ω = ComplexEmbedding.conjugate τ ω := by
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact h
    rw [agree_of_adjoin φ _ h' hx', hc]
  · intro h
    have h' : φ x = ComplexEmbedding.conjugate τ x := by rw [h, hc]
    rw [agree_of_adjoin φ _ h' hω, ComplexEmbedding.conjugate_coe_eq]

end UpperTheory.Gal.CertificateRingHomMap

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrRho
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pTrRho_of :
    UpperTheory.Gal.CertificateRingHomMap.TrRho := by
  intro E _ _ _ n W g
  set e := GlobalTheory.BCT.TrKer.wspEquivVV W
  set F : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] GlobalTheory.BCT.TrKer.Wsp W :=
    PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v)) with hF
  have hcomp : Formalism.L2.DIV.rhoK W g ∘ₗ (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) =
      (e : GlobalTheory.BCT.TrKer.Wsp W →ₗ[ℂ] _) ∘ₗ F := by
    apply PiTensorProduct.ext
    refine MultilinearMap.ext (fun u => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hF, PiTensorProduct.map_tprod]
    dsimp only [e, GlobalTheory.BCT.TrKer.wspEquivVV, LinearEquiv.ofLinear_apply]
    show Formalism.L2.DIV.rhoK W g (GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ u)) =
      GlobalTheory.BCT.TrKer.wspToVV W (PiTensorProduct.tprod ℂ _)
    rw [GlobalTheory.BCT.TrKer.wspToVV_tprod, GlobalTheory.BCT.TrKer.wspToVV_tprod, rhoK_tenMul]
  have hconj : Formalism.L2.DIV.rhoK W g = e.conj F := by
    rw [LinearEquiv.conj_apply, ← hcomp]
    refine LinearMap.ext (fun x => ?_)
    simp
  rw [hconj, LinearMap.trace_conj', hF, GlobalTheory.BCT.TrKer.trace_piMap]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtAtOf
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pWtAt_of :
    UpperTheory.Gal.CertificateRingHomMap.WtAt := by
  intro E _ _ _ n _ π
  refine ⟨⟨(AU.mk π).wt, AutSub.finPart_wt_ne_bot E n π⟩, fun W hW τ lam hlam => ?_⟩
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hT :=
    GlobalTheory.Cong.ofType_of_finPart_fixed E n π W ⊥ f hf hf0 (by
      intro k hk v g
      rw [Subgroup.mem_bot.1 hk, mul_one])
  exact hasWeightAt_unique π τ hlam (hT.wt τ)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpCore
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem symm_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {σ : ℂ ≃+* ℂ} {τ τ₀ : E →+* ℂ}
    (hσ : ∀ y, σ (τ y) = τ₀ y) :
    (σ.symm : ℂ →+* ℂ).comp τ₀ = τ ∧
      (σ.symm : ℂ →+* ℂ).comp (ComplexEmbedding.conjugate τ₀) = ComplexEmbedding.conjugate τ := by
  constructor
  · refine RingHom.ext fun y => ?_
    simp [← hσ y]
  · refine RingHom.ext fun y => ?_
    have h1 : ComplexEmbedding.conjugate τ₀ y = τ₀ (IsCMField.complexConj E y) := by
      rw [ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
    have h2 : ComplexEmbedding.conjugate τ y = τ (IsCMField.complexConj E y) := by
      rw [ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
    rw [h2]
    simp [h1, ← hσ]

private theorem sum_reindex {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {σ : ℂ ≃+* ℂ} {τ τ₀ : E →+* ℂ} {x : E}
    (lam : (E →+* ℂ) → Fin n → ℕ) (hσ : ∀ y, σ (τ y) = τ₀ y) {ε : (E →+* ℂ) → ℕ}
    (hε : ∀ φ : E →+* ℂ, ε ((σ : ℂ →+* ℂ).comp φ) = if φ x = -τ x then 1 else 0) :
    ∑ φ ∈ (Finset.univ.erase τ₀).erase (ComplexEmbedding.conjugate τ₀), ε φ * ∑ j, UpperTheory.Gal.LocalSmoothExtension.conjWt σ lam φ j =
      ∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), (if φ x = -τ x then 1 else 0) * ∑ j, lam φ j := by
  obtain ⟨e1, e2⟩ := symm_comp hσ
  have hA : ∀ φ : E →+* ℂ, (σ : ℂ →+* ℂ).comp ((σ.symm : ℂ →+* ℂ).comp φ) = φ := fun φ =>
    RingHom.ext fun y => by simp
  have hB : ∀ φ : E →+* ℂ, (σ.symm : ℂ →+* ℂ).comp ((σ : ℂ →+* ℂ).comp φ) = φ := fun φ =>
    RingHom.ext fun y => by simp
  refine Finset.sum_nbij' (fun φ => (σ.symm : ℂ →+* ℂ).comp φ) (fun φ => (σ : ℂ →+* ℂ).comp φ) ?_ ?_
    (fun φ _ => hA φ) (fun φ _ => hB φ) ?_
  · intro φ hφ
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hφ ⊢
    exact ⟨fun h => hφ.1 ((hA φ).symm.trans (by rw [h, ← e2, hA])),
      fun h => hφ.2 ((hA φ).symm.trans (by rw [h, ← e1, hA]))⟩
  · intro φ hφ
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hφ ⊢
    exact ⟨fun h => hφ.1 ((hB φ).symm.trans (by rw [h, e2])),
      fun h => hφ.2 ((hB φ).symm.trans (by rw [h, e1]))⟩
  · intro φ _
    have h := hε ((σ.symm : ℂ →+* ℂ).comp φ)
    rw [hA] at h
    rw [h]
    rfl

theorem UpperTheory.Gal.CertificateRingHomMap.pExpCore_of :
    UpperTheory.Gal.CertificateRingHomMap.ExpSum → UpperTheory.Gal.CertificateRingHomMap.ExpCore := by
  intro hS E _ _ _ n d x hd hx W m hm
  refine ⟨fun τ a b hab => ?_, fun τ τ₀ σ hσ ε hε k => ?_⟩
  · unfold lamOf
    split_ifs
    · exact le_rfl
    · exact Int.toNat_le_toNat (add_le_add_left ((W _).anti hab) _)
  · obtain ⟨e1, e2⟩ := symm_comp hσ
    have hs := hS E n d x hd hx W m hm τ
    rw [← sum_reindex (lamOf W m) hσ hε] at hs
    have c1 : ∀ i, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) τ₀ i = lamOf W m τ i := fun i => by
      show lamOf W m ((σ.symm : ℂ →+* ℂ).comp τ₀) i = _
      rw [e1]
    have c2 : ∀ i, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) (ComplexEmbedding.conjugate τ₀) i =
        lamOf W m (ComplexEmbedding.conjugate τ) i := fun i => by
      show lamOf W m ((σ.symm : ℂ →+* ℂ).comp (ComplexEmbedding.conjugate τ₀)) i = _
      rw [e2]
    generalize hR : (∑ φ ∈ (Finset.univ.erase τ₀).erase (ComplexEmbedding.conjugate τ₀),
      ε φ * ∑ j, UpperTheory.Gal.LocalSmoothExtension.conjWt σ (lamOf W m) φ j) = R at hs
    have hk : 0 < n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    rcases InfinitePlace.embedding_mk_eq τ with hv | hv
    · have hc : ComplexEmbedding.conjugate τ ≠ (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding := by
        rw [InfinitePlace.mk_conjugate_eq, hv]; exact conjugate_ne τ
      have l1 : ∀ i, lamOf W m τ i = m (InfinitePlace.mk τ) := fun i => if_pos hv.symm
      have l2 : ∀ i, ((lamOf W m (ComplexEmbedding.conjugate τ) i : ℕ) : ℤ) =
          (W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m (ComplexEmbedding.conjugate τ) i =
          ((W (InfinitePlace.mk (ComplexEmbedding.conjugate τ))).w i +
            m (InfinitePlace.mk (ComplexEmbedding.conjugate τ))).toNat := if_neg hc
        rw [h, InfinitePlace.mk_conjugate_eq]
        exact Int.toNat_of_nonneg (hm _ _)
      have hw : W.at τ = W (InfinitePlace.mk τ) := by
        have h := W.at_embedding (InfinitePlace.mk τ)
        rwa [hv] at h
      refine ⟨fun i => (m (InfinitePlace.mk τ) + R) +
        (∑ j ∈ Finset.univ.erase i, lamOf W m (ComplexEmbedding.conjugate τ) j + (i : ℕ)), k,
        Or.inr ⟨m (InfinitePlace.mk τ), fun i => by rw [c1, l1], fun i => ?_⟩, ?_⟩
      · simp only [c2, hR]
      · have hsum : ((∑ j ∈ Finset.univ.erase k, lamOf W m (ComplexEmbedding.conjugate τ) j : ℕ) : ℤ) =
            ∑ j ∈ Finset.univ.erase k, ((W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) := by
          push_cast
          exact Finset.sum_congr rfl fun j _ => l2 j
        have h3 := Finset.add_sum_erase Finset.univ
          (fun j => (W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) (Finset.mem_univ k)
        have h4 : ∑ j, ((W (InfinitePlace.mk τ)).w j + (m (InfinitePlace.mk τ) : ℤ)) =
            ∑ j, (W (InfinitePlace.mk τ)).w j + (n : ℤ) * m (InfinitePlace.mk τ) := by
          rw [Finset.sum_add_distrib]
          simp
        rw [if_pos hv.symm] at hs
        rw [hw, ← hs]
        push_cast at hsum ⊢
        rw [hsum]
        linarith
    · have hn : τ ≠ (InfinitePlace.mk τ).embedding := by
        rw [hv]; exact (conjugate_ne τ).symm
      have l1 : ∀ i, ((lamOf W m τ i : ℕ) : ℤ) = (W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m τ i = ((W (InfinitePlace.mk τ)).w i + m (InfinitePlace.mk τ)).toNat := if_neg hn
        rw [h]
        exact Int.toNat_of_nonneg (hm _ _)
      have l2 : ∀ i, lamOf W m (ComplexEmbedding.conjugate τ) i = m (InfinitePlace.mk τ) := fun i => by
        have h : lamOf W m (ComplexEmbedding.conjugate τ) i = m (InfinitePlace.mk (ComplexEmbedding.conjugate τ)) :=
          if_pos (by rw [InfinitePlace.mk_conjugate_eq, hv])
        rw [h, InfinitePlace.mk_conjugate_eq]
      have hw : W.at τ = (W (InfinitePlace.mk τ)).dual := if_neg fun h => hn h.symm
      refine ⟨fun i => ((n - 1) * m (InfinitePlace.mk τ) + R) + (lamOf W m τ i + (n - 1 - (i : ℕ))), Fin.rev k,
        Or.inl ⟨m (InfinitePlace.mk τ), fun i => by rw [c2, l2], fun i => ?_⟩, ?_⟩
      · simp only [c1, hR]
      · have e3 : n - 1 - ((Fin.rev k : Fin n) : ℕ) = k := by
          have := k.isLt
          rw [Fin.val_rev]
          omega
        have e4 : (((n - 1 : ℕ) : ℤ)) = (n : ℤ) - 1 := by
          rw [Nat.cast_sub hk]; simp
        rw [if_neg hn] at hs
        rw [hw, ← hs]
        simp only [e3, DomWeight.dual]
        push_cast
        rw [l1, e4]
        ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpSum
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem imag_of_sq {c : ℂ} {d : ℕ} (hd : 0 < d) (h : c ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) c = -c ∧ c ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qh67.imag_of_sq hd h

private theorem sum_emb {E : Type} [Field E] [NumberField E]
    (hc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ) (f : (E →+* ℂ) → ℤ) :
    ∑ φ, f φ = ∑ v : InfinitePlace E, (f v.embedding + f (ComplexEmbedding.conjugate v.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun φ => InfinitePlace.mk φ) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib : Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq φ with h | h
      · left; exact h.symm
      · right; rw [h]; exact (ComplexEmbedding.involutive_conjugate E φ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hfib, Finset.sum_pair (hc _).symm]

theorem UpperTheory.Gal.CertificateRingHomMap.pExpSum_of :
    UpperTheory.Gal.CertificateRingHomMap.ExpSum := by
  intro E _ _ _ n d x hd hx W m hm τ
  have hsq : ∀ φ : E →+* ℂ, (φ x) ^ 2 = -(d : ℂ) := fun φ => by
    rw [← map_pow, hx]; simp
  have hτ0 : τ x ≠ 0 := (imag_of_sq hd (hsq τ)).2
  have hcj : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ x = -φ x := fun φ => by
    rw [ComplexEmbedding.conjugate_coe_eq]; exact (imag_of_sq hd (hsq φ)).1
  have hne : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ h => by
    have h1 := hcj φ
    rw [h] at h1
    have h2 : φ x ≠ 0 := (imag_of_sq hd (hsq φ)).2
    exact h2 (self_eq_neg.1 h1)
  have hpm : ∀ φ : E →+* ℂ, φ x = τ x ∨ φ x = -τ x := fun φ =>
    sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq φ).trans (hsq τ).symm)
  have hnn : τ x ≠ -τ x := fun h => hτ0 (self_eq_neg.1 h)
  have hl0 : ∀ v : InfinitePlace E, ∑ j, lamOf W m v.embedding j = n * m v := fun v => by
    simp [lamOf, InfinitePlace.mk_embedding]
  have hl1 : ∀ v : InfinitePlace E, ((∑ j, lamOf W m (ComplexEmbedding.conjugate v.embedding) j : ℕ) : ℤ) =
      ∑ i, (W v).w i + n * m v := fun v => by
    have hv : InfinitePlace.mk (ComplexEmbedding.conjugate v.embedding) = v := by
      rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    have h1 : ∀ j, lamOf W m (ComplexEmbedding.conjugate v.embedding) j = ((W v).w j + m v).toNat := fun j => by
      unfold lamOf
      rw [hv, if_neg (hne _)]
    simp only [h1]
    push_cast
    rw [Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hm v i), Finset.sum_add_distrib]
    simp
  set F : (E →+* ℂ) → ℤ := fun φ => (((if φ x = -τ x then 1 else 0) * ∑ j, lamOf W m φ j : ℕ) : ℤ) with hF
  have hFv : ∀ v : InfinitePlace E, F v.embedding + F (ComplexEmbedding.conjugate v.embedding) =
      n * m v + if v.embedding x = -τ x then 0 else ∑ i, (W v).w i := fun v => by
    simp only [hF, hcj]
    rcases hpm v.embedding with h | h
    · have h1 : v.embedding x ≠ -τ x := by rw [h]; exact hnn
      have h2 : -v.embedding x = -τ x := by rw [h]
      rw [if_neg h1, if_pos h2, if_neg h1, zero_mul, one_mul, hl1]
      push_cast; ring
    · have h2 : -v.embedding x ≠ -τ x := by rw [h, neg_neg]; exact hnn
      rw [if_pos h, if_neg h2, if_pos h, zero_mul, one_mul, hl0]
      push_cast; ring
  have hF1 : ∑ φ, F φ = mOf x W (∑ v, ((∑ i, (W v).w i) + n * m v)) τ := by
    rw [sum_emb hne, Finset.sum_congr rfl fun v _ => hFv v]
    unfold mOf
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> ring
  have hmem : ComplexEmbedding.conjugate τ ∈ Finset.univ.erase τ :=
    Finset.mem_erase.2 ⟨hne τ, Finset.mem_univ _⟩
  have hF2 : ∑ φ, F φ = F τ + (F (ComplexEmbedding.conjugate τ) +
      ∑ φ ∈ (Finset.univ.erase τ).erase (ComplexEmbedding.conjugate τ), F φ) := by
    rw [Finset.add_sum_erase _ F hmem, Finset.add_sum_erase _ F (Finset.mem_univ τ)]
  have hFτ : F τ = 0 := by simp only [hF]; rw [if_neg hnn]; simp
  have hFc : F (ComplexEmbedding.conjugate τ) = n * m (InfinitePlace.mk τ) +
      if τ = (InfinitePlace.mk τ).embedding then ∑ i, (W (InfinitePlace.mk τ)).w i else 0 := by
    simp only [hF]
    rw [if_pos (hcj τ), one_mul]
    split_ifs with h
    · conv_lhs => rw [h]
      rw [hl1]
      ring
    · have h' : ComplexEmbedding.conjugate τ = (InfinitePlace.mk τ).embedding := by
        rcases InfinitePlace.embedding_mk_eq τ with h1 | h1
        · exact absurd h1.symm h
        · exact h1.symm
      rw [h', hl0]
      push_cast; ring
  rw [← hF1, hF2, hFτ, hFc, zero_add]
  simp only [hF]
  push_cast
  ring
end

namespace UpperTheory.Gal.CertificateRingHomMap

theorem trRho_holds : TrRho := pTrRho_of
theorem trSch_holds : TrSch := pTrSch_of
theorem schHom_holds : SchHom := pSchHom_of
theorem charConj_holds : CharConj := pCharConj_of
theorem wtCore_holds : WtCore := pWtCore_of trRho_holds trSch_holds schHom_holds charConj_holds
theorem autEx_holds : AutEx := pAutEx_of
theorem wtAt_holds : WtAt := pWtAt_of
theorem epsIff_holds : EpsIff := pEpsIff_of
theorem expSum_holds : ExpSum := pExpSum_of
theorem expCore_holds : ExpCore := pExpCore_of expSum_holds

end UpperTheory.Gal.CertificateRingHomMap

namespace UpperTheory.Gal.Int.Geo.Pl

theorem vecEx_holds : VecEx := vecEx_of CertificateRingHomMap.seedGU_holds CertificateRingHomMap.wtAt_holds

theorem wtOf_holds : WtOf := wtOf_of CertificateRingHomMap.wtCore_holds

theorem expOf_holds : ExpOf := expOf_of CertificateRingHomMap.expCore_holds CertificateRingHomMap.autEx_holds CertificateRingHomMap.wtAt_holds CertificateRingHomMap.epsIff_holds

end UpperTheory.Gal.Int.Geo.Pl
