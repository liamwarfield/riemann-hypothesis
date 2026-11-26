module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem rFin_const {a : ℕ} (c : ℂ) : RFin (fun _ : GL (Fin a) ℂ => c) := by
  refine ⟨continuous_const, Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, fun y => ?_⟩
  exact Submodule.mem_span_singleton.2 ⟨c, by funext n; simp⟩

private theorem rFin_add {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h + q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.add cq, A ⊔ B, inferInstance, fun y => ?_⟩
  have h := Submodule.add_mem_sup (mA y) (mB y)
  exact h

private theorem rFin_mul {a : ℕ} {p q : GL (Fin a) ℂ → ℂ} (hp : RFin p) (hq : RFin q) :
    RFin (fun h => p h * q h) := by
  obtain ⟨cp, A, fA, mA⟩ := hp
  obtain ⟨cq, B, fB, mB⟩ := hq
  refine ⟨cp.mul cq, A * B, ?_, fun y => ?_⟩
  · have h1 : A.FG := (Submodule.fg_iff_finiteDimensional A).2 fA
    have h2 : B.FG := (Submodule.fg_iff_finiteDimensional B).2 fB
    exact (Submodule.fg_iff_finiteDimensional _).1 (h1.mul h2)
  · have h := Submodule.mul_mem_mul (mA y) (mB y)
    exact h

private theorem rFin_entry {a : ℕ} (i j : Fin a) :
    RFin (fun h : GL (Fin a) ℂ => (h : Matrix (Fin a) (Fin a) ℂ) i j) := by
  refine ⟨Units.continuous_val.matrix_elem i j,
    Submodule.span ℂ (Set.range fun r : Fin a => fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), fun y => ?_⟩
  have h : (fun n : GL (Fin a) ℂ => ((n * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ r, (y : Matrix (Fin a) (Fin a) ℂ) r j • fun n : GL (Fin a) ℂ => (n : Matrix (Fin a) (Fin a) ℂ) i r := by
    funext n
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

private theorem rFin_of_rep {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : GL (Fin a) ℂ →* (V →ₗ[ℂ] V)) (l : V →ₗ[ℂ] ℂ) (v : V) (X : GL (Fin a) ℂ)
    (hc : Continuous fun h : GL (Fin a) ℂ => l (ρ h v)) : RFin fun n => l (ρ (X * n) v) := by
  refine ⟨hc.comp (continuous_const.mul continuous_id),
    LinearMap.range (LinearMap.pi fun n : GL (Fin a) ℂ => l ∘ₗ ρ (X * n)), inferInstance,
    fun y => ⟨ρ y v, ?_⟩⟩
  funext n
  change l (ρ (X * n) (ρ y v)) = l (ρ (X * (n * y)) v)
  rw [← mul_assoc, map_mul ρ (X * n) y]
  rfl

private theorem rFin_delta {a : ℕ} (ν : DomWeight a) (X : GL (Fin a) ℂ) : RFin fun n => delta ν (X * n) := by
  haveI : FiniteDimensional ℂ (nablaSq ℂ a ν) := inferInstance
  exact rFin_of_rep (sqRep ℂ a ν) (ev1 ν) (top ν) X (GlobalTheory.BCT.TrKer.continuous_coef_sqRep a ν (top ν) (ev1 ν))

theorem UpperTheory.Gal.Wt.rFinEx_of :
    UpperTheory.Gal.Wt.RFinEx := by
  intro a
  refine ⟨rFin_delta, fun P => ?_⟩
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : pev (MvPolynomial.C c : MvPolynomial (Fin a × Fin a) ℂ) = fun _ => c := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_const c
  | add p q hp hq =>
    have h : pev (p + q) = fun g => pev p g + pev q g := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_add hp hq
  | mul_X p n hp =>
    have h : pev (p * MvPolynomial.X n) = fun g => pev p g * (g : Matrix (Fin a) (Fin a) ℂ) n.1 n.2 := by
      funext g
      simp [pev]
    rw [h]
    exact rFin_mul hp (rFin_entry n.1 n.2)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNearH
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial

private theorem zp {k : Type} [NormedField k] [IsUltrametricDist k] {u : k} {ε : ℝ} (h0 : 0 ≤ ε) (hu : ‖u‖ = 1) (h : ‖u - 1‖ ≤ ε)
    (n : ℤ) : ‖u ^ n - 1‖ ≤ ε := by
  have hu0 : u ≠ 0 := fun e => by simp [e] at hu
  have step : ∀ w x : k, ‖w‖ = 1 → ‖w - 1‖ ≤ ε → ‖x - 1‖ ≤ ε → ‖x * w - 1‖ ≤ ε := fun w x hw h1 h2 => by
    rw [show x * w - 1 = (x - 1) * w + (w - 1) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rwa [norm_mul, hw, mul_one]
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih => rw [zpow_add_one₀ hu0]; exact step _ _ hu h ih
  | pred n ih =>
    rw [zpow_sub_one₀ hu0]
    refine step _ _ (by rw [norm_inv, hu, inv_one]) ?_ ih
    rw [show u⁻¹ - 1 = -(u⁻¹ * (u - 1)) by field_simp; ring, norm_neg, norm_mul, norm_inv, hu, inv_one, one_mul]
    exact h

theorem UpperTheory.Gal.Wt.deltaNear_h : DeltaNear := by
  intro l _ ι a ν h hI
  let m : GL (Fin a) ℂ → Fin a × Fin a → Qbar l := fun g p => ι.symm ((g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1)
  let D : MvPolynomial (Fin a × Fin a) ℤ := (Matrix.of fun i j => (X (j, i) : MvPolynomial (Fin a × Fin a) ℤ)).det
  have hmap : ∀ (w : Fin a × Fin a → ℂ) (P : MvPolynomial (Fin a × Fin a) ℤ),
      ι.symm (aeval w P) = aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  have hD : ∀ g : GL (Fin a) ℂ, ι.symm (g : Matrix (Fin a) (Fin a) ℂ).det = aeval (m g) D := fun g => by
    rw [← hmap, AlgHom.map_det]
    congr 2
    ext i j
    simp
  have hδ : ∀ g : GL (Fin a) ℂ, ι.symm (delta ν g) = (aeval (m g) D) ^ ν.detShift * aeval (m g) (extremal ℤ a ν) := fun g => by
    have e1 : (aeval fun p : Fin a × Fin a => (1 : Matrix (Fin a) (Fin a) ℂ) p.1 p.2).comp
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g : Matrix (Fin a) (Fin a) ℂ).transpose) =
        aeval fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1 :=
      MvPolynomial.algHom_ext fun v => by simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
    have e2 : delta ν g = (g : Matrix (Fin a) (Fin a) ℂ).det ^ ν.detShift *
        aeval (fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1) (extremal ℤ a ν) := by
      change aeval _ (sqAct ℂ a ν g (extremal ℂ a ν)) = _
      rw [sqAct, map_smul, ← AlgHom.comp_apply, e1, detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
        ← Formalism.L2.DIV.map_extremal (algebraMap ℤ ℂ), aeval_map_algebraMap, smul_eq_mul]
    rw [e2, map_mul, map_zpow₀, hD, hmap]
  have hm : ∀ p, ‖m h p‖ ≤ 1 := fun p => (hI _ _).1
  have hb : ∀ (x : Fin a × Fin a → Qbar l), (∀ p, ‖x p‖ ≤ 1) → ∀ P : MvPolynomial (Fin a × Fin a) ℤ, ‖aeval x P‖ ≤ 1 :=
    fun x hx P => (aeval_sub_le le_rfl hx hx (fun _ => by simp) P).1
  have hd1 : ‖aeval (m h) D‖ = 1 := by
    have h1 := hb _ hm D
    have h2 := hb (m h⁻¹) (fun p => (hI _ _).2) D
    have h3 : ‖aeval (m h) D‖ * ‖aeval (m h⁻¹) D‖ = 1 := by
      rw [← norm_mul, ← hD, ← hD, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, norm_one]
    nlinarith [norm_nonneg (aeval (m h) D), norm_nonneg (aeval (m h⁻¹) D)]
  refine ⟨by rw [hδ, norm_mul, norm_zpow, hd1, one_zpow, one_mul]; exact hb _ hm _, fun ε hε hN => ?_⟩
  have h1 : ∀ p, ‖m 1 p‖ ≤ 1 := fun p => by
    simp only [m, Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  have hc : ∀ p, ‖m h p - m 1 p‖ ≤ ε := fun p => by
    have := hN p.2 p.1
    rwa [map_sub] at this
  have eD : aeval (m 1) D = 1 := by rw [← hD]; simp
  have eE : aeval (m 1) (extremal ℤ a ν) = 1 := by
    rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det]
    rw [show ∀ M : Matrix (Fin (s.val + 1)) (Fin (s.val + 1)) (Qbar l), M = 1 → M.det ^ (ν.natW s - Formalism.GradedWeylDivisibility.nuNext ν.natW s) = 1 from
      fun M hM => by rw [hM, Matrix.det_one, one_pow]]
    ext i j
    simp [m, Matrix.one_apply, eq_comm]
  have c1 : ‖aeval (m h) D - 1‖ ≤ ε := by rw [← eD]; exact (aeval_sub_le hε hm h1 hc D).2.2
  have c2 : ‖aeval (m h) (extremal ℤ a ν) - 1‖ ≤ ε := by rw [← eE]; exact (aeval_sub_le hε hm h1 hc (extremal ℤ a ν)).2.2
  rw [map_sub, map_one, hδ, show ∀ x y : Qbar l, x * y - 1 = x * (y - 1) + (x - 1) from fun x y => by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (zp hε hd1 c1 _))
  rwa [norm_mul, norm_zpow, hd1, one_zpow, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightAtEmbeddingOverPlace
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem ladic_weight_at_embedding_over_place : Kap0 := by
  intro E _ _ _ l _ ι a v' τ hτ
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l (ι.symm.toRingHom.comp τ)
  have hle : v'.asIdeal ≤ u.asIdeal := fun x hx => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    exact (hu _).2 (hτ x hx)
  have huv : v' = u := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le u.isPrime.ne_top hle)
  subst huv
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l (ι.symm.toRingHom.comp τ) v' hu
  have hl : ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    have h1 : ‖(ι.symm.toRingHom.comp τ) ((((l : ℕ) : 𝓞 E)) : E)‖ < 1 := by
      have h0 : (ι.symm.toRingHom.comp τ) ((((l : ℕ) : 𝓞 E)) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
      rw [h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])]
      exact Padic.norm_p_lt_one
    simpa using (hu (((l : ℕ) : 𝓞 E) : E)).2 h1
  have hκ : ∀ (g : UA E a) (p q : Fin a), ((((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v')) g :
      GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q = ι (j (((cLoc v' g : GL (Fin a) (v'.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q)) := fun _ _ _ => rfl
  refine ⟨(Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v'), ?_, ?_, ?_, ?_, ?_⟩
  · rintro γ ⟨g₀, hg₀⟩
    ext p q
    change ι (j (pLoc E v' (pFin E ((γ.1 : Matrix (Fin a) (Fin a) (Ad E)) p q)))) =
      coord τ (pInf E ((γ.1 : Matrix (Fin a) (Fin a) (Ad E)) p q))
    have hg₁ : (γ.1 : GL (Fin a) (Ad E)) = ratGL E a g₀ := hg₀.symm
    rw [hg₁]
    change ι (j (pLoc E v' (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin a) (Fin a) E) p q))))) =
      coord τ (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin a) (Fin a) E) p q)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin a) (Fin a) E) p q)) hjE
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j (algebraMap E (v'.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : cLoc v' x = Matrix.GeneralLinearGroup.map (pLoc E v') (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by
      ext; rfl
    rw [MonoidHom.comp_apply, h2, hx', map_one, map_one]
  · intro g
    constructor
    · intro h
      have hinj : Function.Injective (ι.toRingHom.comp j) := RingHom.injective _
      refine Units.ext (Matrix.ext fun p q => hinj ?_)
      have h3 := congrArg (fun m : GL (Fin a) ℂ => (m : Matrix (Fin a) (Fin a) ℂ) p q) h
      simp only [hκ] at h3
      have h4 : (ι.toRingHom.comp j) (((1 : GL (Fin a) (v'.adicCompletion E)) : Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q) =
          ((1 : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q := by
        simp only [Units.val_one, Matrix.one_apply]
        split_ifs <;> simp
      exact h3.trans h4.symm
    · intro h
      rw [MonoidHom.comp_apply, h, map_one]
  · intro p q
    have h1 : (fun g : UA E a => ι.symm (((((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v')) g :
        GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q)) =
        fun g => j (((cLoc v' g : GL (Fin a) (v'.adicCompletion E)) : Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q) :=
      funext fun g => by rw [hκ, RingEquiv.symm_apply_apply]
    rw [h1]
    exact hj.comp ((Units.continuous_val.matrix_elem p q).comp (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
  · intro g hg p q
    obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 hg
    constructor
    · rw [hκ, RingEquiv.symm_apply_apply]
      exact UpperTheory.Gal.Gen.Loc.norm_map_integer_le_one l v' j hl hj _ (h1 p q)
    · rw [MonoidHom.comp_apply, ← map_inv]
      change ‖ι.symm (ι (j ((((cLoc v' g)⁻¹ : GL (Fin a) (v'.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q)))‖ ≤ 1
      rw [RingEquiv.symm_apply_apply]
      exact UpperTheory.Gal.Gen.Loc.norm_map_integer_le_one l v' j hl hj _ (h2 p q)

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExistsDual
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem tor_one (a k : ℕ) : tor a k 1 = 1 := by
  apply Units.ext
  rw [tor_coe]
  simp

private theorem top_ne {a : ℕ} (κ : DomWeight a) : top κ ≠ 0 := by
  intro h
  have h1 : extremal ℂ a κ = 0 := congrArg Subtype.val h
  exact Formalism.GradedWeylDivisibility.hwNe ℂ a a le_rfl _ h1

private theorem exists_dual {a : ℕ} {κ : DomWeight a} {w : nablaSq ℂ a κ} (hw : w ≠ 0) :
    ∃ L : nablaSq ℂ a κ →ₗ[ℂ] ℂ, L w ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hc)

private theorem span_top {a : ℕ} {κ : DomWeight a} (A : Set (nablaSq ℂ a κ)) (hA : ∃ w ∈ A, w ≠ 0)
    (hst : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∀ w ∈ A, sqRep ℂ a κ (unitaryIncl a u) w ∈ A) :
    Submodule.span ℂ A = ⊤ := by
  let S : Subrepresentation (smallRep (unitaryIncl a) κ) :=
    ⟨Submodule.span ℂ A, fun u x hx => by
      change sqRep ℂ a κ (unitaryIncl a u) x ∈ Submodule.span ℂ A
      induction hx using Submodule.span_induction with
      | mem x h => exact Submodule.subset_span (hst u x h)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx⟩
  rcases (isIrreducible_smallRep_unitary a κ).eq_bot_or_eq_top S with h | h
  · exfalso
    obtain ⟨w, hw, hw0⟩ := hA
    have h1 : Submodule.span ℂ A = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hw0 ((Submodule.span_eq_bot.1 h1) w hw)
  · exact congrArg Subrepresentation.toSubmodule h

theorem UpperTheory.Gal.Wt.wtBd_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.ExpDisj → UpperTheory.Gal.Wt.SqExp → UpperTheory.Gal.Wt.TopUp → UpperTheory.Gal.Wt.TorFacts → UpperTheory.Gal.Wt.WtBd := by
  intro hB hD hS hT hF a k κ s
  have hz1 : ∀ f : Circle → ℂ, f = 0 → f 1 = 0 := fun f h => by rw [h]; rfl
  refine ⟨fun A hA hst hexp => ?_, fun w hw hexp => ?_⟩
  · have htop : Submodule.span ℂ A = ⊤ := span_top A hA hst
    by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual (top_ne κ)
    have hall : ∀ x ∈ Submodule.span ℂ A, (fun z => L (sqRep ℂ a κ (tor a k z) x)) ∈ ExpLe s := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x h => exact hexp x h L
      | zero =>
        have h0 := (ExpLe s).zero_mem
        convert h0 using 1
        funext z
        simp only [map_zero, Pi.zero_apply]
      | add x y _ _ hx hy =>
        have := (ExpLe s).add_mem hx hy
        convert this using 1
        funext z
        simp only [map_add, Pi.add_apply]
      | smul c x _ hx =>
        have := (ExpLe s).smul_mem c hx
        convert this using 1
        funext z
        simp only [map_smul, Pi.smul_apply]
    have hmem := hall (top κ) (htop.ge Submodule.mem_top)
    have hfun : (fun z => L (sqRep ℂ a κ (tor a k z) (top κ))) = fun z : Circle => L (top κ) * (z : ℂ) ^ psum κ k := by
      funext z
      obtain ⟨hup, -, hchi, -⟩ := hF a k z
      rw [hT a κ _ hup, hchi κ, map_smul, smul_eq_mul, mul_comm]
    rw [hfun] at hmem
    have hge := (hB.2.2.2.1 (L (top κ)) (psum κ k)).2
    have h0 := hz1 _ (hD s (psum κ k) _ hlt hmem hge)
    simp at h0
    exact hL h0
  · by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual hw
    have h0 := hz1 _ (hD (psum κ k) s _ hlt (hS a k κ w L).1 (hexp L))
    simp only [tor_one, map_one, Module.End.one_apply] at h0
    exact hL h0
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplFin
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

namespace UpperTheory.Gal.Wt.KaplanskyFiniteness

variable {k : Type} [NormedField k] [IsUltrametricDist k]

private lemma norm_unit_le (c x : k) (hc : c ≠ 0) (h : ‖x‖ ≤ ‖c‖) : ‖1 - c⁻¹ * x‖ ≤ 1 := by
  have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) ?_)
  rw [norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hc', mul_one]
  exact h

private lemma norm_le_of_near (c x : k) (h : ‖x - c‖ ≤ ‖c‖ / 2) : ‖x‖ ≤ ‖c‖ := by
  have hx : x = (x - c) + c := by ring
  rw [hx]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans ?_) le_rfl)
  have := norm_nonneg c
  linarith

private lemma pow_near {u : k} {ε : ℝ} (hε : 0 ≤ ε) (hu : ‖u‖ ≤ 1) (h : ‖u - 1‖ ≤ ε) (n : ℕ) :
    ‖u ^ n - 1‖ ≤ ε := by
  induction n with
  | zero => simpa using hε
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h)
    rw [norm_mul]
    calc ‖u‖ * ‖u ^ n - 1‖ ≤ 1 * ε := mul_le_mul hu ih (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

private lemma eval_bound (p : Polynomial k) (x : k) (R : ℝ) (hx : ‖x‖ ≤ R) :
    ‖p.eval x‖ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ * R ^ i := by
  rw [Polynomial.eval_eq_sum_range]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx i) (norm_nonneg _)

private lemma exists_pow_small (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ n : ℕ, M * (1 / 2 : ℝ) ^ n ≤ ε := by
  have hM1 : 0 < M + 1 := by linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hM1) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  calc M * (1 / 2 : ℝ) ^ n ≤ (M + 1) * (1 / 2 : ℝ) ^ n := by nlinarith
    _ ≤ (M + 1) * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hn.le hM1.le
    _ = ε := by field_simp

end UpperTheory.Gal.Wt.KaplanskyFiniteness

open UpperTheory.Gal.Wt.KaplanskyFiniteness in
theorem UpperTheory.Gal.Wt.kaplFin_of :
    UpperTheory.Gal.Wt.KaplFin := by
  classical
  intro k _ _ s δ ε hδ hε hε1
  refine Finset.induction_on_max_value (fun c : k => ‖c‖) s ?_ ?_
  · intro _
    refine ⟨1, fun x _ => by simp, fun c hc => absurd hc (Finset.notMem_empty c), fun x _ => ?_⟩
    simpa using hε.le
  · intro c s _ hmax ih hs
    obtain ⟨p', h1, h2, h3⟩ := ih fun c' hc' => hs c' (Finset.mem_insert_of_mem hc')
    have hδc : δ ≤ ‖c‖ := hs c (Finset.mem_insert_self c s)
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hδc
      linarith
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
    obtain ⟨n, hn⟩ := exists_pow_small (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c‖ ^ i) ε
      (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) hε
    have hev : ∀ x, ((p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n).eval x) =
        p'.eval x * (1 - c⁻¹ * x) ^ n := by
      intro x
      simp [Polynomial.eval_mul, Polynomial.eval_pow]
    refine ⟨p' * (1 - Polynomial.C c⁻¹ * Polynomial.X) ^ n, ?_, ?_, ?_⟩
    · intro x hx
      rw [hev, norm_mul, norm_pow]
      have hu := norm_unit_le c x hc0 (hx.trans hδc)
      calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ 1 * 1 :=
            mul_le_mul (h1 x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) zero_le_one
        _ = 1 := one_mul 1
    · intro c' hc' x hx
      rw [hev, norm_mul, norm_pow]
      rcases Finset.mem_insert.mp hc' with rfl | hc's
      · have hxc := norm_le_of_near c' x hx
        have hu : ‖1 - c'⁻¹ * x‖ ≤ 1 / 2 := by
          have e : 1 - c'⁻¹ * x = c'⁻¹ * (c' - x) := by field_simp
          rw [e, norm_mul, norm_inv, norm_sub_rev, inv_mul_le_iff₀ hcpos]
          linarith
        calc ‖p'.eval x‖ * ‖1 - c'⁻¹ * x‖ ^ n
            ≤ (∑ i ∈ Finset.range (p'.natDegree + 1), ‖p'.coeff i‖ * ‖c'‖ ^ i) * (1 / 2 : ℝ) ^ n :=
              mul_le_mul (eval_bound p' x _ hxc) (pow_le_pow_left₀ (norm_nonneg _) hu n)
                (by positivity) ((norm_nonneg _).trans (eval_bound p' x _ hxc))
          _ ≤ ε := hn
      · have hxc : ‖x‖ ≤ ‖c‖ := (norm_le_of_near c' x hx).trans (hmax c' hc's)
        have hu := norm_unit_le c x hc0 hxc
        calc ‖p'.eval x‖ * ‖1 - c⁻¹ * x‖ ^ n ≤ ε * 1 :=
              mul_le_mul (h2 c' hc's x hx) (pow_le_one₀ (norm_nonneg _) hu) (by positivity) hε.le
          _ = ε := mul_one ε
    · intro x hx
      have hxδ : ‖x‖ ≤ δ := hx.trans (by nlinarith)
      have hu := norm_unit_le c x hc0 (hxδ.trans hδc)
      have hu1 : ‖(1 - c⁻¹ * x) - 1‖ ≤ ε := by
        have e : (1 - c⁻¹ * x) - 1 = -(c⁻¹ * x) := by ring
        rw [e, norm_neg, norm_mul, norm_inv, inv_mul_le_iff₀ hcpos]
        calc ‖x‖ ≤ δ * ε := hx
          _ ≤ ‖c‖ * ε := mul_le_mul_of_nonneg_right hδc hε.le
      have hun := pow_near hε.le hu hu1 n
      have e : p'.eval x * (1 - c⁻¹ * x) ^ n - 1 =
          p'.eval x * ((1 - c⁻¹ * x) ^ n - 1) + (p'.eval x - 1) := by ring
      rw [hev, e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h3 x hx))
      rw [norm_mul]
      calc ‖p'.eval x‖ * ‖(1 - c⁻¹ * x) ^ n - 1‖ ≤ 1 * ε :=
            mul_le_mul (h1 x hxδ) hun (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SqExpH
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial

set_option maxHeartbeats 400000 in
private theorem coeff_diag {a : ℕ} (t : Fin a → ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) (m : Fin a × Fin a →₀ ℕ) :
    AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (Matrix.diagonal t) f) m = (∏ v : Fin a × Fin a, t v.1 ^ m v) * AddMonoidAlgebra.coeff f m := by
  have hg : (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2))
      = fun v => MvPolynomial.C (t v.1) * MvPolynomial.X v := by
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne t (Ne.symm hb), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show AddMonoidAlgebra.coeff (MvPolynomial.aeval
      (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2)) f) m = _
  rw [hg]
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [MvPolynomial.prod_X_pow_eq_monomial, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rw [mul_one, mul_comm]
      congr 1
      refine Finset.prod_subset (Finset.subset_univ _) ?_
      intro v _ hv
      simp only [Finsupp.mem_support_iff, not_not] at hv
      rw [hv, pow_zero]
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem UpperTheory.Gal.Wt.sqExp_h : ExpBasic → EvLem → Dom → SqExp := by
  intro hE hEv hDom a k κ w L
  obtain ⟨_, _, hle, hmon, _, _⟩ := hE
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (Finset.univ.filter fun i : Fin a => (i : ℕ) < k).card := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin a × Fin a →₀ ℕ) → ℕ,
      e = fun m => ∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), Formalism.GradedWeylDivisibility.rowDeg m i := ⟨_, rfl⟩
  have hdet : ∀ z : Circle, detPow ℂ a (tor a k z) κ.detShift = (z : ℂ) ^ ((D : ℤ) * κ.detShift) := by
    intro z
    simp only [detPow]
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, tor_coe, Matrix.det_diagonal,
      ← Finset.prod_filter, Finset.prod_const, zpow_mul, zpow_natCast, hD]
  have hprod : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      (∏ v : Fin a × Fin a, (if ((v.1 : Fin a) : ℕ) < k then (z : ℂ) else 1) ^ m v) = (z : ℂ) ^ e m := by
    intro z m
    have hin : ∀ i : Fin a, (∏ s : Fin a, (if (i : ℕ) < k then (z : ℂ) else 1) ^ m (i, s))
        = if (i : ℕ) < k then (z : ℂ) ^ Formalism.GradedWeylDivisibility.rowDeg m i else 1 := by
      intro i
      split_ifs
      · rw [Finset.prod_pow_eq_pow_sum]
        rfl
      · simp
    rw [Fintype.prod_prod_type]
    dsimp only
    simp only [hin]
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, he]
  have hcoeff : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      AddMonoidAlgebra.coeff ((sqRep ℂ a κ (tor a k z) w : nablaSq ℂ a κ) : MvPolynomial (Fin a × Fin a) ℂ) m
        = AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) m
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e m : ℤ)) := by
    intro z m
    show AddMonoidAlgebra.coeff (sqAct ℂ a κ (tor a k z) (w : MvPolynomial (Fin a × Fin a) ℂ)) m = _
    rw [sqAct, MvPolynomial.coeff_smul, hdet, tor_coe, Matrix.diagonal_transpose, coeff_diag]
    beta_reduce
    rw [hprod, smul_eq_mul, zpow_add₀ (Circle.coe_ne_zero z), zpow_natCast]
    ring
  let ev : (Fin a × Fin a →₀ ℕ) → nablaSq ℂ a κ →ₗ[ℂ] ℂ :=
    fun x => (MvPolynomial.lcoeff ℂ x).comp (nablaSq ℂ a κ).subtype
  have hsep : ∀ p : nablaSq ℂ a κ, (∀ x, ev x p = 0) → p = 0 := by
    intro p hp
    apply Subtype.ext
    ext x
    simpa [ev] using hp x
  have hterm : ∀ T : Submodule ℂ (Circle → ℂ),
      (∀ x, AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x ≠ 0 →
        (fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) ∈ T) →
      (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ T := by
    intro T hT
    refine hEv (nablaSq ℂ a κ) (Fin a × Fin a →₀ ℕ) Circle ev hsep T (fun z => sqRep ℂ a κ (tor a k z) w) ?_ L
    intro x
    have hfun : (fun z => ev x (sqRep ℂ a κ (tor a k z) w))
        = fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ)) := funext fun z => hcoeff z x
    rw [hfun]
    by_cases hx : AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x = 0
    · have h0 : (fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) = 0 := by
        funext z
        simp [hx]
      rw [h0]
      exact T.zero_mem
    · exact hT x hx
  have hds : ∀ i : Fin a, κ.detShift ≤ κ.w i := by
    intro i
    simp only [DomWeight.detShift, dif_pos (Fin.pos i)]
    exact κ.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  have hnat : ∀ i : Fin a, ((κ.natW i : ℕ) : ℤ) = κ.w i - κ.detShift :=
    fun i => Int.toNat_of_nonneg (sub_nonneg.mpr (hds i))
  have hDa : D ≤ a := by
    rw [hD]
    exact (Finset.card_filter_le _ _).trans (Finset.card_fin a).le
  refine ⟨hterm _ fun x hx => ?_, hterm _ fun x _ => ?_⟩
  · have hxs : x ∈ (w : MvPolynomial (Fin a × Fin a) ℂ).support := MvPolynomial.mem_support_iff.mpr hx
    have hbound := hDom a κ _ w.2 x hxs k
    have hup : (D : ℤ) * κ.detShift + (e x : ℤ) ≤ psum κ k := by
      have h1 : (e x : ℤ) ≤ ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) := by
        rw [he]
        exact_mod_cast hbound
      have h2 : (D : ℤ) * κ.detShift
          + ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) = psum κ k := by
        rw [Nat.cast_sum]
        simp only [hnat]
        rw [Finset.sum_sub_distrib, hD, psum]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      linarith
    exact (hle _ _ hup).1 (hmon _ _).1
  · have hlow : -((a * κ.detShift.natAbs : ℕ) : ℤ) ≤ (D : ℤ) * κ.detShift + (e x : ℤ) := by
      have hD0 : (0 : ℤ) ≤ D := Int.natCast_nonneg D
      have hDa' : (D : ℤ) ≤ a := by exact_mod_cast hDa
      have he0 : (0 : ℤ) ≤ (e x : ℤ) := Int.natCast_nonneg _
      have habs : 0 ≤ κ.detShift + |κ.detShift| := by linarith [neg_abs_le κ.detShift]
      push_cast
      nlinarith [mul_nonneg hD0 habs, mul_nonneg (sub_nonneg.mpr hDa') (abs_nonneg κ.detShift)]
    exact (hle _ _ hlow).2 (hmon _ _).2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpBasic
noncomputable section

namespace UpperTheory.Gal.Wt

private theorem pow_mem_le {s m : ℤ} (h : m ≤ s) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpLe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem pow_mem_ge {s m : ℤ} (h : s ≤ m) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpGe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem circle_mul_mem_of_mem_span_of_mem_span {S T : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, ∀ g ∈ T, (fun z => f z * g z) ∈ P) {f g : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) (hg : g ∈ Submodule.span ℂ T) :
    (fun z => f z * g z) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    induction hg using Submodule.span_induction with
    | mem g hgT => exact h f hfS g hgT
    | zero =>
      have e : (fun z => f z * (0 : Circle → ℂ) z) = 0 := by
        funext z
        simp
      rw [e]
      exact P.zero_mem
    | add g₁ g₂ _ _ h₁ h₂ =>
      have e : (fun z => f z * (g₁ + g₂) z) = (fun z => f z * g₁ z) + (fun z => f z * g₂ z) := by
        funext z
        simp [mul_add]
      rw [e]
      exact P.add_mem h₁ h₂
    | smul c g _ h₁ =>
      have e : (fun z => f z * (c • g) z) = c • (fun z => f z * g z) := by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact P.smul_mem c h₁
  | zero =>
    have e : (fun z => (0 : Circle → ℂ) z * g z) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z => (f₁ + f₂) z * g z) = (fun z => f₁ z * g z) + (fun z => f₂ z * g z) := by
      funext z
      simp [add_mul]
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z => (c • f) z * g z) = c • (fun z => f z * g z) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_comp_inv_mem_of_mem_span {S : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, (fun z : Circle => f z⁻¹) ∈ P) {f : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) : (fun z : Circle => f z⁻¹) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS => exact h f hfS
  | zero =>
    have e : (fun z : Circle => (0 : Circle → ℂ) z⁻¹) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z : Circle => (f₁ + f₂) z⁻¹) = (fun z => f₁ z⁻¹) + (fun z => f₂ z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z : Circle => (c • f) z⁻¹) = c • (fun z => f z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_zpow_mul_zpow_eq_zpow_add (m n : ℤ) :
    (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) = fun z : Circle => (z : ℂ) ^ (m + n) := by
  funext z
  rw [zpow_add₀ (Circle.coe_ne_zero z)]

private theorem circle_inv_zpow_eq_zpow_neg (m : ℤ) :
    (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) = fun z : Circle => (z : ℂ) ^ (-m) := by
  funext z
  rw [Circle.coe_inv, inv_zpow, zpow_neg]

theorem expBasic_of : ExpBasic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_le (by omega)
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_ge (by omega)
  · intro s t hst
    constructor
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hm.trans hst, rfl⟩
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hst.trans hm, rfl⟩
  · intro c m
    exact ⟨(ExpLe m).smul_mem c (pow_mem_le le_rfl), (ExpGe m).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro c
    have e : (fun _ : Circle => c) = c • (fun z : Circle => (z : ℂ) ^ (0 : ℤ)) := by
      funext z
      simp
    rw [e]
    exact ⟨(ExpLe 0).smul_mem c (pow_mem_le le_rfl), (ExpGe 0).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro s f
    constructor
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_ge (by omega)
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_le (by omega)

end UpperTheory.Gal.Wt

end
end
