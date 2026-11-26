module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.GoodOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.RedOne

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutOf4Of
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Cu.AutomorphyOfRankFourLift

theorem irr_cover {H H' K : Type} [Group H] [Group H'] [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (r : H →* Matrix n n K) (r' : H' →* Matrix n n K) (h : ∀ x, ∃ y, ∃ u : K, r x = u • r' y) (hr : Irr r) :
    Irr r' := by
  unfold Irr at hr ⊢
  rw [eq_top_iff, ← hr, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, u, e⟩ := h x
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem q_apply (d : Dat Ω l) (T : Tower d.D) (g : G T.F Ω) :
    ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r g =
      ((toB d.δ (resQ T.F g) : (Qbar l)ˣ) : Qbar l) •
        mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ) (resQ T.F g) := by
  ext i j
  simp only [PD.map_r, Matrix.map_apply, Dat.Q, MonoidHom.comp_apply, mapRep_apply, Matrix.smul_apply, smul_eq_mul,
    rep4, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, Units.val_one, one_smul, map_mul]
  rfl

end UpperTheory.V.Cu.AutomorphyOfRankFourLift

open UpperTheory.V.Cu.AutomorphyOfRankFourLift in
theorem UpperTheory.V.Cu.autOf4_of (hne : AlNe) : AutOf4 := by
  intro Ω _ _ _ l _ d T hT hok hirr
  have h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L)) := by
    refine irr_cover _ _ (fun x => ?_) hirr
    have hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z := by
      intro z hz
      have hz' : z ∈ T.F ⊔ T.K := T.hL ▸ hz
      have hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x)) := by
        rw [sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le,
          Subgroup.zpowers_le]
        refine ⟨?_, x.2.1⟩
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun y hy => x.1.commutes ⟨y, hy⟩
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)
    let y : G T.L Ω := { (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }
    refine ⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply,
      show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]
    rfl
  have hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L)) := by
    have := ((irrIff (Qbar l)).1 _).1 h1
    convert this using 1
    ext g : 2
    rfl
  have hkL : ¬ d.K' ≤ T.L := fun hle => by
    obtain ⟨g, hg, hn⟩ := hne Ω l d T hT hok
    refine hn (IntermediateField.fixingSubgroup_le hle ?_)
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  have hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  have hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  obtain ⟨π, hreg, hatt⟩ := d.aut T.L hLa hkL
    (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL
  refine ⟨π, hreg, ?_⟩
  have key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits
      ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L) := by
    ext g : 2
    rw [tw_val]
    change _ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _
    rw [q_apply, smul_smul]
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
    rw [show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]
    rfl
  rw [key]
  exact hatt
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ContOf4
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section
variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_map {S : Type} [CommRing S] {J : Ideal S} (φ : R →+* S) (h : I ≤ J.comap φ) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun g => φ (f g) := fun N =>
  (hf N).comp (Ideal.quotientMap (J ^ N) φ ((Ideal.pow_right_mono h N).trans (Ideal.le_comap_pow φ N)))

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x :=
  fun N => (hf N).mul (hg N)

private theorem ac_neg {f : Γ → R} (hf : AdicCont I f) : AdicCont I fun x => -f x :=
  fun N => (hf N).neg

private theorem ac_tn {f t : Γ → M2 R} (hf : ∀ i j, AdicCont I fun g => f g i j)
    (ht : ∀ i j, AdicCont I fun g => t g i j) (i j : Fin 4) : AdicCont I fun g => tn (f g) (t g) i j := by
  fin_cases i <;> fin_cases j <;> simp [tn] <;>
    first
    | exact ac_mul (hf _ _) (ht _ _)
    | exact ac_neg (ac_mul (hf _ _) (ht _ _))

end

theorem contOf4 : ContOf4 := by
  intro Ω _ _ _ l _ d T
  have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
  have hm : maximalIdeal d.c.O ≤ (maximalIdeal d.c₁.O).comap (inc d.h) := fun x hx =>
    (UpperTheory.V.Fr.sc_norm l d.c₁ (inc d.h x)).2.2 ((UpperTheory.V.Fr.sc_norm l d.c x).2.1 hx)
  have h1 : (d.Q T).Cont (maximalIdeal d.c₁.O) := fun i j N =>
    (ac_mul (ac_map (inc d.h) hm d.tw.cont) (ac_tn d.mod.cont d.tau.cont i j) N).comp_continuous hc
  exact ⟨h1, fun R _ f hf i j => ac_map (J := ⊥) f (fun y hy => Ideal.mem_comap.2 (Ideal.mem_bot.2 (hf y hy))) (h1 i j)⟩

end UpperTheory.V.Cu

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ConjRes
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

private theorem low_ne {Γ R : Type} [Group Γ] [Field R] (y a : Γ → R) (hy : ∀ g h, y (g * h) = y g * a h + y h)
    (g0 g : Γ) (h0 : y g0 = 0) (ha : a g0 ≠ 1) (hg : y g ≠ 0) : y (g * g0 * g⁻¹) ≠ 0 := by
  intro h
  have e1 := hy (g * g0 * g⁻¹) g
  rw [inv_mul_cancel_right, hy, h, h0] at e1
  have e2 : y g * (a g0 - 1) = 0 := by linear_combination e1
  rcases mul_eq_zero.1 e2 with e | e
  · exact hg e
  · exact ha (sub_eq_zero.1 e)

private theorem conj_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [hF : IsGalois ℚ F]
    (g : G ℚ Ω) (s : G F Ω) : ∃ t : G F Ω, resQ F t = g * resQ F s * g⁻¹ := by
  haveI : IsGalois ℚ Ω := {}
  have hN : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).2 (by convert hF <;> exact Subsingleton.elim _ _)
  have hs : resQ F s ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact s.commutes ⟨x, hx⟩
  exact ⟨F.fixingSubgroupEquiv ⟨_, hN.conj_mem _ hs g⟩, rfl⟩

private theorem tn_21 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 2 1 = -(a 1 0 * b 1 1) := by
  rfl

private theorem tn_30 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 3 0 = a 1 0 * b 0 0 := by
  rfl

theorem UpperTheory.V.Cu.entOf4 : EntOf4 := by
  intro Ω _ _ _ l _ d T hT hO R _ f hf
  have hU : ∀ y : d.c₁.O, IsUnit y → f y ≠ 0 := fun y hy => (hy.map f).ne_zero
  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k g)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t11 : ∀ g, f (d.τ g 1 1) ≠ 0 := fun g => by
    by_cases hg : g ∈ d.K'.fixingSubgroup
    · rw [(d.tau.on g hg).1, t00]
      exact one_ne_zero
    · rw [(d.tau.off g hg).1, map_neg, t00]
      exact neg_ne_zero.2 one_ne_zero
  have hPhi : Raw.bar (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k) (resQ T.F T.g0) ≠ 1 := by
    intro e
    apply hO.dist 0 3 (by decide)
    rw [hT.pr, d.tw.red0, d.tw.red3, e, mul_one]
  have ha : f (d.ρ₁ (resQ T.F T.g0) 0 0) ≠ 1 := by
    rw [h00]
    intro e
    have hu : IsUnit ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) := by
      by_contra hn
      apply hPhi
      have : residue d.c.O ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) = 0 :=
        (residue_eq_zero_iff _).2 hn
      rwa [map_sub, map_one, sub_eq_zero] at this
    apply hU _ (hu.map (inc d.h))
    rw [map_sub, map_sub, e, map_one, map_one, sub_self]
  obtain ⟨g, hg⟩ := d.mod.ne
  have hg' : f (d.ρ₁ g 1 0) ≠ 0 := hU _ (by by_contra hn; exact hg hn)
  have key : ∃ t : G T.F Ω, f (d.ρ₁ (resQ T.F t) 1 0) ≠ 0 := by
    by_cases h0 : f (d.ρ₁ (resQ T.F T.g0) 1 0) = 0
    · obtain ⟨t, ht⟩ := conj_res T.F g T.g0
      refine ⟨t, ?_⟩
      rw [ht]
      refine low_ne (fun g => f (d.ρ₁ g 1 0)) (fun g => f (d.ρ₁ g 0 0)) (fun g h => ?_) _ g h0 ha hg'
      simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), h11, one_mul]
    · exact ⟨T.g0, h0⟩
  obtain ⟨t, ht⟩ := key
  have hδ : f (toC d.h d.δ (resQ T.F t) : d.c₁.O) ≠ 0 := hU _ (Units.isUnit _)
  have ent : ∀ i j, ((d.Q T).map f).r t i j =
      f (toC d.h d.δ (resQ T.F t) : d.c₁.O) * f (UpperTheory.V.Cu.tn (d.ρ₁ (resQ T.F t)) (d.τ (resQ T.F t)) i j) := fun i j => by
    rw [← map_mul]
    rfl
  refine ⟨⟨t, 2, 1, by decide, ?_⟩, ⟨t, 3, 0, by decide, ?_⟩⟩
  · rw [ent, tn_21, map_neg, map_mul]
    exact mul_ne_zero hδ (neg_ne_zero.2 (mul_ne_zero ht (t11 _)))
  · rw [ent, tn_30, map_mul, t00, mul_one]
    exact mul_ne_zero hδ ht

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ConjDec
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section Alg

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem tn_map (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

private theorem flg_map (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem adj_flg (x s : R) : adj (flg x s) = nA (-s) * tn (low (-x)) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev] <;> ring

private theorem conj_flg (a x y s s' : R) (g t : M2 R) :
    adj (flg y s') * (a • tn g t) * flg x s = a • (nA (-s') * tn (low (-y) * g * low x) t * nA s) := by
  have e : tn (low (-y) * g * low x) t = tn (low (-y)) 1 * tn g t * tn (low x) 1 := by
    rw [← tn_mul, ← tn_mul, one_mul, mul_one]
  rw [adj_flg, e, flg]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

private theorem isUp_mid (a : R) {m t : M2 R} {s s' : R} (hm01 : m 0 1 = 0) (hm10 : m 1 0 = 0) (ht01 : t 0 1 = 0)
    (ht10 : t 1 0 = 0) (hs1 : t 1 1 * s = t 0 0 * s') (hs2 : t 1 1 * s' = t 0 0 * s) :
    IsUp (a • (nA (-s') * tn m t * nA s)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [nA, tn, Matrix.mul_apply, Fin.sum_univ_succ, hm01, hm10, ht01, ht10] at hij ⊢ <;>
    first
    | linear_combination (a * m 0 0) * hs1
    | linear_combination (-(a * m 0 0)) * hs1
    | linear_combination (a * m 1 1) * hs2

end Alg

private theorem conj_dec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {A A' : ValuationSubring Ω} {g s : G ℚ Ω}
    (hA : ∀ x, g x ∈ A' ↔ x ∈ A) (hs : s ∈ Dec (F := ℚ) A') : g⁻¹ * s * g ∈ Dec (F := ℚ) A :=
  UpperTheory.V.conjGal_mem_Dec (τ := RingEquiv.refl ℚ) (σ := g.toRingEquiv) (fun x => g.commutes x) hA hs

private theorem key {R : Type} [Field R] {g s t : M2 R} {x y : R} (h : g * t = s * g) (hg0 : g 0 0 ≠ 0)
    (hg : g 1 1 = 1 ∧ g 0 1 = 0) (hs : s 1 1 = 1 ∧ s 0 1 = 0) (ht : t 1 1 = 1 ∧ t 0 1 = 0) (hne : s 0 0 ≠ 1)
    (hx : t 1 0 + t 1 1 * x = (t 0 0 + t 0 1 * x) * x) (hy : s 1 0 + s 1 1 * y = (s 0 0 + s 0 1 * y) * y) :
    g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y = 0 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hs.1, hs.2, ht.1, ht.2] at h0 h1 hx hy ⊢
  have e : t 0 0 = s 0 0 := mul_left_cancel₀ hg0 (by linear_combination h0)
  rw [e] at h1 hx
  refine mul_left_cancel₀ (sub_ne_zero.2 hne) ?_
  linear_combination h1 - hx + g 0 0 * hy

private theorem phi_ne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (h : D.Good) (pr : Bool) (k : ℕ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Dec (F := ℚ) A, Raw.bar (Phi D pr k) s ≠ 1 := by
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  obtain ⟨u, hu, -⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l _ A hl.out (h.pl_over l hl.out) hA
  have hc : chiO ℚ Ω l c.O (D.sg l) = 1 := by simp [chiO, h.sg_cyc]
  have e : Phi D pr k (u⁻¹ * D.sg l * u) = (D.ξ * D.Psi ^ (if pr then (-1 : ℤ) else 1)) (D.sg l) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    cases pr <;> simp [Phi, phi, Raw.Psi, Chr.Psi, hc]
  exact ⟨_, hu _ (h.sg_frob l hT).1, fun h' => h.condD l hT _
    ((congrArg (fun z : c.Oˣ => residue c.O (z : c.O)) e).symm.trans h')⟩

theorem overOf4 : OverOf4 := by
  intro Ω _ _ _ l _ d T hT R _ f hf
  refine ⟨rfl, fun v' => ?_⟩
  obtain ⟨v, g, hg⟩ := (d.T₀.cover (T.pl v') (T.ovl v')).exists
  refine ⟨v, g, hg, ?_⟩
  obtain ⟨s, hs, hne⟩ := phi_ne d.D d.ctx.1 d.T₀.pr d.k (T.pl v') (T.ovl v')
  have ht : (resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g ∈ Dec (F := ℚ) (d.T₀.pl v) := conj_dec hg hs
  have h1 : ∀ t, ((d.ρ₁ t).map f) 1 1 = 1 ∧ ((d.ρ₁ t).map f) 0 1 = 0 := fun t =>
    ⟨by simpa [sub_eq_zero] using hf _ (d.mod.red t).2.1, hf _ (d.mod.red t).2.2⟩
  have h0 : ∀ t, ((d.ρ₁ t).map f) 0 0 = f (inc d.h (Phi d.D d.T₀.pr d.k t)) := fun t => by
    simpa [sub_eq_zero] using hf _ (d.mod.red t).1
  have hk := key (g := (d.ρ₁ (resQ d.T₀.F g)).map f) (s := (d.ρ₁ s).map f)
    (t := (d.ρ₁ ((resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g)).map f) (x := f (d.x (d.T₀.pl v))) (y := f (d.x (T.pl v')))
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul]; congr 2; group)
    (by rw [h0]; exact (((Phi d.D d.T₀.pr d.k _).isUnit.map (inc d.h)).map f).ne_zero) (h1 _) (h1 _) (h1 _)
    (fun h => by
      rw [h0] at h
      have hn : ¬ IsUnit ((Phi d.D d.T₀.pr d.k s : d.c.O) - 1) := fun hu => by
        have := ((hu.map (inc d.h)).map f).ne_zero
        rw [map_sub, map_sub, map_one, map_one, h, sub_self] at this
        exact this rfl
      refine hne ?_
      show residue d.c.O (Phi d.D d.T₀.pr d.k s : d.c.O) = 1
      rw [← map_one (residue d.c.O)]
      exact Ideal.Quotient.eq.2 hn)
    (by simpa using congrArg f (d.mod.flag _ (d.T₀.ovl v) _ ht))
    (by simpa using congrArg f (d.mod.flag _ (T.ovl v') _ hs))
  have z01 : f (d.τ (resQ d.T₀.F g) 0 1) = 0 := hf _ (d.tau.red _).2
  have hsg := d.tau.mov (d.T₀.pl v) (T.pl v') (resQ d.T₀.F g) (d.T₀.ovl v) hg
  have hτ : ((d.τ (resQ d.T₀.F g)).map f) 1 0 = 0 ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (d.T₀.pl v)) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (T.pl v')) ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (T.pl v')) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (d.T₀.pl v)) := by
    simp only [Matrix.map_apply]
    by_cases hK : resQ d.T₀.F g ∈ d.K'.fixingSubgroup
    · obtain ⟨e1, e2⟩ := d.tau.on _ hK
      rw [e1, e2, hsg.1 hK, z01]
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨e1, e2⟩ := d.tau.off _ hK
      rw [e1, e2, hsg.2 hK, map_neg, map_neg, map_neg, z01]
      exact ⟨neg_zero, by ring, by ring⟩
  have e : ((d.Q d.T₀).map f).r g =
      f (toC d.h d.δ (resQ d.T₀.F g)) • tn ((d.ρ₁ (resQ d.T₀.F g)).map f) ((d.τ (resQ d.T₀.F g)).map f) := by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have e1 : ((d.Q d.T₀).map f).n v = flg (f (d.x (d.T₀.pl v))) (f (d.s (d.T₀.pl v))) := by
    rw [← flg_map]; rfl
  have e2 : ((d.Q T).map f).n v' = flg (f (d.x (T.pl v'))) (f (d.s (T.pl v'))) := by
    rw [← flg_map]; rfl
  rw [e, e1, e2, conj_flg]
  refine isUp_mid _ ?_ ?_ (by simpa using z01) hτ.1 hτ.2.1 hτ.2.2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (h1 (resQ d.T₀.F g)).2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination hk

end UpperTheory.V.Cu

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.HyperbolicOrthogonalEntrySqSubSqEqOne
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu.RankFourHodgeWeights

section Alg

variable {R : Type} [CommRing R]

theorem flg_eq (x σ : R) : flg x σ = !![1, 0, 0, 0; σ, 1, 0, 0; -(x * σ), -x, 1, 0; x, 0, -σ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

theorem adj_flg (x σ : R) : adj (flg x σ) = !![1, 0, 0, 0; -σ, 1, 0, 0; 0, x, 1, 0; -x, x * σ, σ, 1] := by
  rw [flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem diag (c x σ y : R) (g t : M2 R)
    (h1 : g 0 0 + g 0 1 * x = y) (h2 : g 1 1 - x * g 0 1 = 1)
    (ht1 : t 1 1 = t 0 0) (ht2 : t 1 0 = t 0 1) (i : Fin 4) :
    (adj (flg x σ) * (c • tn g t) * flg x σ) i i =
      c * ![y * (t 0 0 + t 0 1 * σ), y * (t 0 0 - t 0 1 * σ), t 0 0 + t 0 1 * σ, t 0 0 - t 0 1 * σ] i := by
  rw [adj_flg, flg_eq]
  fin_cases i
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 + t 0 1 * σ)) * h1
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 - t 0 1 * σ)) * h1
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 + t 0 1 * σ)) * h2
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 - t 0 1 * σ)) * h2

theorem hyperbolicOrthogonal_entry_sq_sub_sq_eq_one (t : M2 R) (h : tᵀ * !![1, 0; 0, -1] * t = !![1, 0; 0, -1]) (ht2 : t 1 0 = t 0 1) :
    t 0 0 * t 0 0 - t 0 1 * t 0 1 = 1 := by
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at this
  rw [ht2] at this
  linear_combination this

theorem fin_cg {α : Type} [CommGroup α] (E D : α) (j : ℤ) (n m : ℕ) (hD : D ^ 2 = E ^ j) (i : Fin 4) :
    (D * ![E ^ n * E ^ m, E ^ n * (E ^ m)⁻¹, E ^ m, (E ^ m)⁻¹] i) ^ 2 =
      E ^ (j + 2 * ![(n : ℤ) + m, (n : ℤ) - m, (m : ℤ), -(m : ℤ)] i) := by
  rw [mul_pow, hD, zpow_add]
  congr 1
  fin_cases i <;> simp <;> group

end Alg

private theorem psi_map {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4) (s : Γ) :
    (P.map f).ψ v i s = f (P.ψ v i s) := by
  have a : adj ((P.n v).map f) = (adj (P.n v)).map f := by
    ext i j
    simp [adj_apply]
  have b : (P.map f).r s = (P.r s).map f := rfl
  have c : (P.map f).n v = (P.n v).map f := rfl
  rw [PD.ψ, b, c, a, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous

private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F

private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

theorem psi_eq (d : Dat Ω l) (T : Tower d.D) (v : T.ι) (s : G T.F Ω) (hs : resQ T.F s ∈ Ine (F := ℚ) (T.pl v)) (i : Fin 4) :
    (d.Q T).ψ v i s = ((toC d.h d.δ (resQ T.F s) * ![chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m,
      chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹,
      chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m, (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹] i : d.c₁.Oˣ) : d.c₁.O) := by
  have hA := T.ovl v
  have hD := Ine_le_Dec _ hs
  have hK := d.quad.split _ hA hD
  obtain ⟨h1, h2⟩ := d.mod.ine _ hA _ hs
  obtain ⟨ht1, ht2⟩ := d.tau.on _ hK
  have hp := d.tau.ine _ hA _ hs
  have hσ : d.s (T.pl v) * d.s (T.pl v) = 1 := by
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> ring
  have hf : d.τ (resQ T.F s) 0 0 * d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.τ (resQ T.F s) 0 1 = 1 :=
    hyperbolicOrthogonal_entry_sq_sub_sq_eq_one _ (d.tau.form (resQ T.F s)) ht2
  have hm : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) =
      (((chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹ : d.c₁.Oˣ) : d.c₁.O) := by
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [← hp]
    linear_combination hf - d.τ (resQ T.F s) 0 1 * d.τ (resQ T.F s) 0 1 * hσ
  have e : (d.Q T).ψ v i s = (adj (flg (d.x (T.pl v)) (d.s (T.pl v))) *
      (((toC d.h d.δ (resQ T.F s) : d.c₁.Oˣ) : d.c₁.O) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))) *
      flg (d.x (T.pl v)) (d.s (T.pl v))) i i := rfl
  rw [e, diag _ _ _ _ _ _ h1 h2 ht1 ht2 i, hp, hm, Units.val_mul]
  congr 1
  fin_cases i <;> simp [Units.val_mul]

end UpperTheory.V.Cu.RankFourHodgeWeights

open UpperTheory.V.Cu

theorem UpperTheory.V.Cu.wtsOf4 : WtsOf4 := by
  intro Ω _ _ _ l _ d T U j hU hj
  refine ⟨U.comap (resQ T.F), hU.preimage (RankFourHodgeWeights.cont_res T.F), fun v i s hs => ?_⟩
  have hI : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := ⟨hs.2.1, hs.2.2⟩
  have e3 : toB d.δ (resQ T.F s) ^ 2 = cycBar T.F Ω l s ^ j := by
    have := congrArg (Units.map (algebraMap d.c.O (PadicAlgCl l)).toMonoidHom) (hj _ hs.1)
    rw [map_pow, map_zpow] at this
    exact this.trans (congrArg (· ^ j) (RankFourHodgeWeights.toB_chi d.c (resQ T.F s)))
  have hk : (d.k : ℤ) - 1 = ((d.k - 1 : ℕ) : ℤ) := by
    have := d.big
    omega
  dsimp only
  rw [RankFourHodgeWeights.psi_map, RankFourHodgeWeights.psi_eq d T v s hI i, hk]
  have key := RankFourHodgeWeights.fin_cg (cycBar T.F Ω l s) (toB d.δ (resQ T.F s)) j (d.k - 1) d.m e3 i
  have hδ : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom) (toC d.h d.δ (resQ T.F s)) = toB d.δ (resQ T.F s) :=
    Units.ext rfl
  have hE : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom) (chiO ℚ Ω l d.c₁.O (resQ T.F s)) = cycBar T.F Ω l s :=
    Units.ext rfl
  have hU : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom)
      (toC d.h d.δ (resQ T.F s) * ![chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m,
        chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹,
        chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m, (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹] i) =
      toB d.δ (resQ T.F s) * ![cycBar T.F Ω l s ^ (d.k - 1) * cycBar T.F Ω l s ^ d.m,
        cycBar T.F Ω l s ^ (d.k - 1) * (cycBar T.F Ω l s ^ d.m)⁻¹, cycBar T.F Ω l s ^ d.m, (cycBar T.F Ω l s ^ d.m)⁻¹] i := by
    rw [← hδ, ← hE]
    fin_cases i <;> simp [map_mul, map_pow, map_inv]
  rw [← key, ← hU, Units.val_pow_eq_pow_val, Units.coe_map]
  rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.EqOfRd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws

namespace UpperTheory.V.Cu.RankFourTwistExistence

section SlopeTestRemainingChoices

variable {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O] {I : Ideal O} {γ δ : Γ →* Oˣ}

theorem ac_mul (h : AdicCont I fun g => (γ g : O)) (h' : AdicCont I fun g => (δ g : O)) :
    AdicCont I fun g => ((γ * δ) g : O) := fun N => by
  simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
  exact (h N).mul (h' N)

theorem ac_zpow (h : AdicCont I fun g => (γ g : O)) (n : ℤ) : AdicCont I fun g => ((γ ^ n) g : O) := fun N => by
  have h1 : IsLocallyConstant fun g => Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (γ g) :=
    IsLocallyConstant.desc _ Units.val (h N) Units.val_injective
  have h2 := h1.comp fun u => ((u ^ n : (O ⧸ I ^ N)ˣ) : O ⧸ I ^ N)
  refine (congrArg IsLocallyConstant (funext fun g => ?_)).mp h2
  simp only [Function.comp_apply, MonoidHom.zpow_apply]
  rw [← map_zpow]
  rfl

theorem ac_ker [IsTopologicalGroup Γ] (h : IsOpen (γ.ker : Set Γ)) : AdicCont I fun g => (γ g : O) := fun N => by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' γ.ker, h.preimage (continuous_const_mul _), by simp, fun y hy => ?_⟩
  have h1 : γ (x⁻¹ * y) = 1 := hy
  beta_reduce
  rw [← mul_inv_cancel_left x y, map_mul γ, h1, mul_one]

end SlopeTestRemainingChoices

noncomputable def rd {l : ℕ} [Fact l.Prime] (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ :=
  Units.map (residue c.O).toMonoidHom

theorem eq_of_rd {l : ℕ} [Fact l.Prime] {c : Coef l} {x y : c.Oˣ} {m : ℕ} (hm : l.Coprime m) (hx : x ^ m = 1)
    (hy : y ^ m = 1) (h : rd c x = rd c y) : x = y :=
  (congrFacts (AlgebraicClosure ℚ) l c).2.2.2.1 x y m ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hm) hx hy
    (Ideal.Quotient.eq.1 (congrArg Units.val h))

theorem grpF {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem grpT {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (ω ^ e * ψ * η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ⁻¹)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) * (ω ^ e) ^ 2 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem cancel3 {M : Type} [CommGroup M] {a b d p : M} (h : a * b = d ^ 2 * p) (hb : b = d) : a = d * p := by
  subst hb
  apply mul_right_cancel (b := b)
  rw [h, sq, mul_right_comm]

end UpperTheory.V.Cu.RankFourTwistExistence

open UpperTheory.V.Cu.RankFourTwistExistence in
theorem UpperTheory.V.Cu.twEx4 : UpperTheory.V.Cu.TwEx4 := by
  intro Ω _ _ _ l hl c D T h3 k hk1 hk
  have h : D.Good := h3.1
  obtain ⟨-, he2, -, ⟨mψ, -, hmψ, hψ⟩, -⟩ := UpperTheory.V.Ws.large₂.host3 D h3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcont, -, homo, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D h
  obtain ⟨mξ, hmξ, hξ⟩ := h.xi_ord
  have hl1 : l.Coprime (l - 1) := (Nat.coprime_self_sub_right hl.out.one_le).2 (Nat.coprime_one_right l)
  set ε := chiO ℚ Ω l c.O with hε
  set μ : G ℚ Ω →* c.Oˣ := D.al * D.ξ ^ (-1 : ℤ) with hμ
  set P : G ℚ Ω →* c.Oˣ := D.om ^ (D.e : ℤ) * D.ψ with hP
  have al_eq : ∀ g, D.al g = ε g * (D.om g)⁻¹ * D.ξ g := fun _ => rfl
  have mu_eq : ∀ g, μ g = ε g * (D.om g)⁻¹ := fun g => by
    rw [hμ, MonoidHom.mul_apply, MonoidHom.zpow_apply, al_eq, zpow_neg_one, mul_inv_cancel_right]
  have charpoly_eq_of_isIso : ∀ g, P g = D.om g ^ D.e * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply, zpow_natCast]
  have P_eqz : ∀ g, P g = D.om g ^ (D.e : ℤ) * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply]
  have Psi_z : ∀ g, D.Psi g = ε g ^ (D.e : ℤ) * D.ψ g := fun _ => rfl
  have Psi_eq : ∀ g, D.Psi g = μ g ^ D.e * P g := fun g => by
    have : D.Psi g = ε g ^ D.e * D.ψ g := by rw [← zpow_natCast]; rfl
    rw [this, mu_eq, charpoly_eq_of_isIso, mul_pow, inv_pow, mul_assoc, inv_mul_cancel_left]
  have al_eq' : ∀ g, D.al g = μ g * D.ξ g := fun g => by rw [al_eq, mu_eq]
  have th_eq : ∀ g, D.th g = D.al g * D.Psi g := fun _ => rfl
  have rmu : ∀ g, rd c (μ g) = 1 := fun g => by
    have : rd c (D.om g) = rd c (ε g) := Units.ext (h.om_bar g)
    rw [mu_eq, map_mul, map_inv, this, mul_inv_cancel]
  have ral : ∀ g, rd c (D.al g) = rd c (D.ξ g) := fun g => by rw [al_eq', map_mul, rmu, one_mul]
  have rPsi : ∀ g, rd c (D.Psi g) = rd c (P g) := fun g => by rw [Psi_eq, map_mul, map_pow, rmu, one_pow, one_mul]
  have omp : ∀ g, D.om g ^ (l - 1) = 1 := fun g => DFunLike.congr_fun h.om_pow g
  have hM : l.Coprime ((l - 1) * mψ * mξ) := (hl1.mul_right hmψ).mul_right hmξ
  have PM : ∀ g, P g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ψ g ^ mψ = 1 := DFunLike.congr_fun hψ g
    rw [charpoly_eq_of_isIso, mul_pow, ← pow_mul, mul_comm D.e, mul_assoc, mul_assoc, pow_mul, omp, one_pow, one_mul, mul_assoc, mul_left_comm,
      pow_mul, h1, one_pow]
  have xM : ∀ g, D.ξ g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ξ g ^ mξ = 1 := DFunLike.congr_fun hξ g
    rw [mul_comm, pow_mul, h1, one_pow]
  have h2 : IsUnit (2 : c.O) := by
    have : IsUnit ((2 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes hl.out Nat.prime_two).2 h.l_odd
    simpa [map_ofNat] using this.map (algebraMap ℤ_[l] c.O)
  obtain ⟨η, η2, ηr, ηc, η1⟩ := UpperTheory.exists_square_root_character c.O h2 (G ℚ Ω) μ (fun g => congrArg Units.val (rmu g))
    (ac_mul (hcont 2) (ac_zpow (ac_ker h.xi_open) _))
  have rη : ∀ g, rd c (η g) = 1 := fun g => Units.ext (ηr g)
  have eps_eq : ∀ g, ε g = η g ^ 2 * D.om g := fun g => by rw [η2, mu_eq, inv_mul_cancel_right]
  have epz : ∀ g, ε g ^ (k - 1) = ε g ^ ((k : ℤ) - 1) := fun g => by
    rw [← zpow_natCast, Nat.cast_sub hk1, Nat.cast_one]
  have hkz : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  have omz : ∀ g, D.om g ^ ((k : ℤ) - 1) = D.om g ^ (D.e : ℤ) := fun g => by
    rw [hkz, zpow_natCast, zpow_natCast]
    exact pow_eq_pow_iff_modEq.2 (hk.of_dvd (orderOf_dvd_of_pow_eq_one (omp g)))
  have om2 : ∀ g, (D.om g ^ (D.e : ℤ)) ^ 2 = 1 := fun g => by
    obtain ⟨n, hn⟩ := he2
    rw [zpow_natCast, ← pow_mul, mul_comm, hn, pow_mul, omp, one_pow]
  set j : ℤ := (D.e : ℤ) + 2 - k with hj
  have hc03 : ∀ g, chi D T.pr 0 g * chi D T.pr 3 g = D.th g := fun g => by
    cases T.pr
    · change D.th g * 1 = D.th g
      rw [mul_one]
    · rfl
  obtain ⟨t, tc, tmul, tred, t1⟩ : ∃ t : G ℚ Ω →* c.Oˣ, AdicCont (maximalIdeal c.O) (fun g => (t g : c.O)) ∧
      (∀ g, (t g * η g ^ j) ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g = D.th g) ∧
      (∀ g, rd c (chi D T.pr 3 g) = rd c (t g)) ∧ ∀ g, P g = 1 → t g = 1 := by
    cases hpr : T.pr
    · refine ⟨1, ac_ker (by rw [MonoidHom.ker_one]; exact isOpen_univ), fun g => ?_, fun g => ?_, fun _ _ => rfl⟩
      · change (1 * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * D.ψ g)) = ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [one_mul, epz, eps_eq, hj, grpF, omz, mul_inv_cancel, mul_one]
      · rfl
    · refine ⟨P, ac_mul (ac_zpow (ac_ker homo) _) (ac_ker h.psi_open), fun g => ?_, fun g => rPsi g, fun _ h => h⟩
      · change (P g * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * (D.ψ g)⁻¹)) =
          ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [P_eqz, epz, eps_eq, hj, grpT, omz, mul_inv_cancel, mul_one, om2, mul_one]
  have δ_eq : ∀ g, (t * η ^ j) g = t g * η g ^ j := fun _ => rfl
  have rδ : ∀ g, rd c ((t * η ^ j) g) = rd c (t g) := fun g => by rw [δ_eq, map_mul, map_zpow, rη, one_zpow, mul_one]
  refine ⟨t * η ^ j, ⟨ac_mul tc (ac_zpow ηc j), fun g => ?_, fun g => ?_, fun g => ?_, fun g hg hr => ?_,
    D.om.ker ⊓ D.ψ.ker, j, homo.inter h.psi_open, fun g hg => ?_⟩⟩
  · rw [δ_eq]
    exact tmul g
  · have e0 : chi D T.pr 0 g * chi D T.pr 3 g = (t * η ^ j) g ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g := (hc03 g).trans (tmul g).symm
    have e1 := congrArg (rd c) e0
    rw [map_mul, map_mul, map_pow] at e1
    exact congrArg Units.val (cancel3 e1 ((tred g).trans (rδ g).symm))
  · exact congrArg Units.val ((tred g).trans (rδ g).symm)
  · have hr' : ∀ i, rd c (D.ps i g) = 1 := fun i => Units.ext (by
      have := congrFun (congrFun hr i) i
      change residue c.O (D.ps i g : c.O) = 1
      simpa [Raw.rbar, Raw.r0, diagRep] using this)
    have e1 : ε g = 1 := by rw [hε, chiO, MonoidHom.comp_apply, hg, map_one]
    have o1 : D.om g = 1 := eq_of_rd hl1 (omp g) (one_pow _) (e1 ▸ Units.ext (h.om_bar g))
    have p1 : P g = 1 := eq_of_rd hM (PM g) (one_pow _) (by rw [← rPsi, map_one]; exact hr' 1)
    have x1 : D.ξ g = 1 := eq_of_rd hM (xM g) (one_pow _) (by rw [← ral, map_one]; exact hr' 2)
    have s1 : D.ψ g = 1 := by rw [charpoly_eq_of_isIso, o1, one_pow, one_mul] at p1; exact p1
    refine ⟨?_, ?_⟩
    · rw [δ_eq, t1 g p1, η1 g (by rw [mu_eq, e1, o1, inv_one, mul_one]), one_zpow, mul_one]
    · cases T.pr
      · change D.ξ g * D.ψ g = 1
        rw [x1, s1, mul_one]
      · change D.ξ g * (D.ψ g)⁻¹ = 1
        rw [x1, s1, inv_one, mul_one]
  · have o1 : D.om g = 1 := hg.1
    have o2 : D.ψ g = 1 := hg.2
    rw [← hε, δ_eq, t1 g (by rw [charpoly_eq_of_isIso, o1, o2, one_pow, mul_one]), one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, η2, mu_eq, o1, inv_one, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PAlNe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Cu

private theorem closed_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F E : IntermediateField ℚ Ω) :
    IsClosed ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) := by
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) =
      ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rfl
  rw [e]
  exact isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)

private theorem lim_pt {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (S : Set Γ) (hS : IsClosed S) (g : Γ)
    (hg : (l : ℤ_[l]) ∣ (ε g : ℤ_[l]) - 1) (hm : ∀ n : ℕ, g ^ l ^ n ∈ S) : ∃ h ∈ S, ε h = 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have h2 := dvd_sub_pow_of_dvd_sub hg n
    rw [one_pow] at h2
    have h3 := (pow_dvd_pow _ n.le_succ).trans h2
    rw [map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h3
  obtain ⟨h, hh, hc⟩ := hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))
  refine ⟨h, hh, Units.ext ?_⟩
  have hc' := hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt
  exact eq_of_nhds_neBot (hc'.clusterPt.mono ht)

private theorem dvd_of_om {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.om g = 1) : (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - 1 := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  have h := hD.om_bar g
  simp only [Raw.bar, hg, Units.val_one] at h
  have h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0 := by
    rw [map_sub, map_sub, map_one, h, sub_eq_zero]
    rfl
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := fun hu => h1 (hu.map _)
  rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  (T : Tower D)

private theorem rb_al (g : G T.F Ω) :
    T.rb wAl g = residue c.O ((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ : c.Oˣ) : c.O) := by
  show residue c.O (((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
    (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = _
  rw [zpow_one, zpow_zero, mul_one]

private theorem rb_le {T₀ : Tower D} (h : T₀.Le T) (g : G T.F Ω) : T.rb wAl g = T₀.rb wAl (resLe h.le g) := by
  rw [rb_al, rb_al, h.pr]
  try rfl

private noncomputable def eta : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt wAl)

private theorem eta_val (g : G T.F Ω) : (eta T g : ResidueField c.O) = T.rb wAl g := rfl

private theorem eta_iff {K' : IntermediateField ℚ Ω}
    (hon : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup → T.rb wAl g = 1)
    (hoff : ∀ g : G T.F Ω, resQ T.F g ∉ K'.fixingSubgroup → T.rb wAl g = -1) (hn : (-1 : ResidueField c.O) ≠ 1)
    (g : G T.F Ω) : eta T g = 1 ↔ resQ T.F g ∈ K'.fixingSubgroup := by
  rw [← Units.val_eq_one, eta_val]
  by_cases h : resQ T.F g ∈ K'.fixingSubgroup
  · exact ⟨fun _ => h, fun _ => hon g h⟩
  · rw [hoff g h]
    exact ⟨fun e => absurd e hn, fun e => absurd e h⟩

private theorem eta_sq {K' : IntermediateField ℚ Ω}
    (hon : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup → T.rb wAl g = 1)
    (hoff : ∀ g : G T.F Ω, resQ T.F g ∉ K'.fixingSubgroup → T.rb wAl g = -1) (g : G T.F Ω) : eta T g ^ 2 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, eta_val, Units.val_one]
  by_cases h : resQ T.F g ∈ K'.fixingSubgroup
  · rw [hon g h, one_pow]
  · rw [hoff g h, neg_one_sq]

private theorem eta_om (hD : D.Good) (K' : IntermediateField ℚ Ω)
    (hk' : ∀ g, eta T g = 1 ↔ resQ T.F g ∈ K'.fixingSubgroup) (hsq : ∀ g, eta T g ^ 2 = 1)
    (hne : ∀ g ∈ T.G', resQ T.F g ∈ K'.fixingSubgroup) (g : G T.F Ω) (hg' : g ∈ T.GalL)
    (hg : D.om (resQ T.F g) = 1) : eta T g = 1 := by
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  have hk'' : ∀ g, eta T g = 1 ↔ g ∈ K'.fixingSubgroup.comap (resQ T.F) := fun g => by
    rw [Subgroup.mem_comap, hk']
  have hc : Continuous fun h : G T.F Ω => g⁻¹ * h := continuous_const_mul _
  have h0 : IsClosed (T.GalL : Set (G T.F Ω)) := closed_fix T.F T.K
  have hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1 := dvd_of_om D hD (resQ T.F g) hg
  obtain ⟨h, ⟨h1, h2⟩, h3⟩ := lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _
    (h0.inter ((closed_fix T.F K').preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by
      refine (hk'' _).1 ?_
      obtain ⟨m, hm⟩ := (hl.out.odd_of_ne_two hD.l_odd).pow (n := n)
      rw [map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, hsq g, one_pow, one_mul, inv_mul_cancel]⟩)
  have h4 : eta T h = 1 := (hk' h).2 (hne h ⟨h1, h3⟩)
  have h5 := (hk'' _).2 h2
  rwa [map_mul, h4, mul_one, map_inv, inv_eq_one] at h5

private theorem eta_mul (g : G T.F Ω) :
    eta T g * Raw.bar (chi D T.pr 1) (resQ T.F g) = Raw.bar (chi D T.pr 0) (resQ T.F g) ∧
    eta T g * Raw.bar (chi D T.pr 3) (resQ T.F g) = Raw.bar (chi D T.pr 2) (resQ T.F g) := by
  have e : (T.fr ∅).rt wAl g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ := by
    show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
      (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) = _
    rw [zpow_zero, zpow_one, mul_one]
  have e' : (T.fr ∅).rt wAl g = chi D T.pr 2 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹ := by
    rw [e]
    generalize resQ T.F g = s
    cases T.pr
    · show D.al s * D.Psi s * (D.Psi s)⁻¹ = D.al s * 1⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_right]
    · show D.al s * 1⁻¹ = D.al s * D.Psi s * (D.Psi s)⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_right]
  rw [eta_val]
  constructor
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]

private theorem eta_mul' (hsq : ∀ g, eta T g ^ 2 = 1) (g : G T.F Ω) {u v : ResidueField c.O} (h : eta T g * u = v) :
    eta T g * v = u := by
  rw [← h, ← mul_assoc, ← Units.val_mul, ← pow_two, hsq g, Units.val_one, one_mul]

private noncomputable def etaL : T.GalL →* (ResidueField c.O)ˣ := (eta T).comp T.GalL.subtype

private theorem etaL_app (g : T.GalL) : etaL T g = eta T g := rfl

private theorem etaL_sq (hsq : ∀ g, eta T g ^ 2 = 1) : etaL T ^ 2 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, hsq]

private theorem etaL_perm (hsq : ∀ g, eta T g ^ 2 = 1) (i : Fin 4) : ∃ j, ∀ g : T.GalL,
    etaL T g * Raw.bar (chi D T.pr i) (resQ T.F g) = Raw.bar (chi D T.pr j) (resQ T.F g) := by
  simp only [etaL_app]
  match i with
  | 0 => exact ⟨1, fun g => eta_mul' T hsq g (eta_mul T g).1⟩
  | 1 => exact ⟨0, fun g => (eta_mul T g).1⟩
  | 2 => exact ⟨3, fun g => eta_mul' T hsq g (eta_mul T g).2⟩
  | 3 => exact ⟨2, fun g => (eta_mul T g).2⟩

end

theorem UpperTheory.V.Cu.alNe : AlNe := by
  intro Ω _ _ _ l hl d T hT hO
  by_contra hne
  have hne' : ∀ g ∈ T.G', resQ T.F g ∈ d.K'.fixingSubgroup := fun g hg => by_contra fun h => hne ⟨g, hg, h⟩
  have hon : ∀ g : G T.F Ω, resQ T.F g ∈ d.K'.fixingSubgroup → T.rb wAl g = 1 := fun g hg => by
    rw [rb_le T hT]
    exact d.quad.on (resLe hT.le g) hg
  have hoff : ∀ g : G T.F Ω, resQ T.F g ∉ d.K'.fixingSubgroup → T.rb wAl g = -1 := fun g hg => by
    rw [rb_le T hT]
    exact d.quad.off (resLe hT.le g) hg
  have hn : (-1 : ResidueField d.c.O) ≠ 1 := by
    obtain ⟨g, -, hg⟩ := hO.g3 wAl (by decide)
    by_cases h : resQ T.F g ∈ d.K'.fixingSubgroup
    · exact absurd (hon g h) hg
    · rw [hoff g h] at hg
      exact hg
  have hsq := eta_sq T hon hoff
  have key := hO.g3' (etaL T) (etaL_sq T hsq)
    (fun g hg => by rw [etaL_app]; exact eta_om T d.ctx.1 d.K' (eta_iff T hon hoff hn) hsq hne' g g.2 hg)
    (etaL_perm T hsq)
  obtain ⟨g, hg, hg'⟩ := hO.g3 wAl (by decide)
  have h1 := etaL_app T ⟨g, hg⟩
  rw [key, MonoidHom.one_apply] at h1
  apply hg'
  rw [← eta_val, ← h1, Units.val_one]
end
