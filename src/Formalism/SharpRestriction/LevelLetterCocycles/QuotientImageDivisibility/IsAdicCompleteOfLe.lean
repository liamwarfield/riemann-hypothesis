module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemKD

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LMemMaxOL
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExpCritPOf
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IndepPhiCmp
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.HasSubstPi0Series
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PhiExp
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Phi

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem phi_exp (hs : W.s = 1) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p)
    (y : W.DD T) (hy : y ∈ W.N T) (hyl : (letE (i - 1) : LetA O n) • y = y) :
    ∃ d : ℤ → T.V ⊗[Qp] BdR, Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (W.φD T y) d ∧ (∀ k : ℤ, k < 0 → d k = 0) ∧
      d 0 = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (W.cmp T ⟨y, hy⟩)) := by
  have hp := p_ne_zero_LL W
  obtain ⟨u, hu0, hq⟩ := MC.lev_q_eq W i hζ hp
  have hQ : W.lev i ζ W.Q = PowerSeries.X * u := by rw [MC.Q_eq_q W hs]; exact hq
  obtain ⟨m, hm⟩ := W.N_φ T y hy
  have hm' : W.Q ^ m • W.φD T y ∈ W.N T := hm
  set y' : ↥(W.N T) := ⟨y, hy⟩ with hy'

  have hcX : PowerSeries.constantCoeff (W.lev (i - 1) 1 W.X) = 0 := by
    have e : W.X = letπ := by simp [LocWach.X, hs]
    rw [e, MC.cc_lev_pi W (i - 1) 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩, sub_self]
  have hneg : ∀ k : ℤ, k < 0 → C.levB T (i - 1) 1 y' k = 0 := by
    intro k hk
    have h0 := (((h4W T hT).1 (i - 1) 1 ⟨0, by simp⟩ hcX).1 y' k).2 hk
    rw [C.levN_eq] at h0
    exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (V := T.V) (h0.trans (map_zero _).symm)
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hφrule : ∀ k : ℤ, W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ k =
      ιV PD (LL := LL) (V := T.V) (∑ᶠ j : ℕ, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) •
        (((PD.p : LL) ^ (k - (j : ℤ))) •
          φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ))))) := by
    intro k
    rw [C.levN_eq, C.levB_φ T hT i ζ ⟨1, by rwa [pow_one]⟩ y' m hm' k, hζp]
  have hcoef : ∀ j : ℕ, j < m → PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0 := by
    intro j hj
    rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hterm0 : ∀ (k : ℤ) (j : ℕ), (j < m ∨ k < (j : ℤ)) →
      PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) • (((PD.p : LL) ^ (k - (j : ℤ))) •
        φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' (k - (j : ℤ)))) = 0 := by
    intro k j h
    rcases h with h | h
    · rw [hcoef j h, zero_smul]
    · rw [hneg _ (by omega), map_zero, smul_zero, smul_zero]
  set e : ℤ → T.V ⊗[Qp] BdR := W.levN T i ζ ⟨W.Q ^ m • W.φD T y, hm'⟩ with he
  have he_low : ∀ k : ℤ, k < m → e k = 0 := by
    intro k hk
    rw [hφrule, finsum_eq_zero_of_forall_eq_zero, map_zero]
    intro j
    by_cases hj : j < m
    · exact hterm0 k j (Or.inl hj)
    · exact hterm0 k j (Or.inr (by omega))
  have he_m : e m = (PowerSeries.constantCoeff u) ^ m •
      ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (C.levB T (i - 1) 1 y' 0)) := by
    rw [hφrule, finsum_eq_single _ m (fun j hj => ?_)]
    · rw [map_pow, hQ, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, sub_self, zpow_zero, one_smul,
        map_smul]
    · rcases Nat.lt_or_gt_of_ne hj with h | h
      · exact hterm0 _ j (Or.inl h)
      · exact hterm0 _ j (Or.inr (by exact_mod_cast h))

  set e' : ℤ → T.V ⊗[Qp] BdR := fun k => e (k + m) with he'
  have hLBe' : LB 0 e' := fun k hk => he_low _ (by omega)
  have huK : PowerSeries.constantCoeff (u ^ m) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hu0
  set d : ℤ → T.V ⊗[Qp] BdR := smulS (u ^ m)⁻¹ e' with hd
  have hLBd : LB 0 d := LB_smulS hLBe' _
  have hde : smulS ((PowerSeries.X * u) ^ m) d = e := by
    rw [mul_pow, smulS_mul hLBd, hd, ← smulS_mul hLBe', PowerSeries.mul_inv_cancel _ huK,
      smulS_one hLBe', smulS_X_pow hLBe']
    funext k
    simp [he']
  refine ⟨d, ⟨⟨0, hLBd⟩, W.Q ^ m, hm', ?_, fun k => ?_⟩, fun k hk => hLBd k hk, ?_⟩
  · rw [map_pow, hQ]
    exact pow_ne_zero _ (mul_ne_zero PowerSeries.X_ne_zero
      (fun h0 => hu0 (by rw [h0, map_zero])))
  · rw [map_pow, hQ, conv_eq, hde]
  ·
    have h1 : d 0 = PowerSeries.constantCoeff ((u ^ m)⁻¹) • e' 0 := by
      rw [hd, smulS_eq_sum hLBe' _ 0 1 (by norm_num)]
      simp
    rw [h1]
    simp only [he']
    rw [zero_add, he_m, smul_smul, PowerSeries.constantCoeff_inv, map_pow, inv_mul_cancel₀
      (pow_ne_zero _ hu0), one_smul]
    congr 2
    rw [← C.cmp_eq T hT (i - 1) y']
    congr 1
    exact Subtype.ext hyl

end Phi

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.DvdOfDvdImage
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Wd

open PowerSeries

variable {O LL : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
  (hinj : Function.Injective (algebraMap O LL)) (l : O)
  (ψ : PowerSeries O →+* PowerSeries LL) (hψC : ∀ o : O, ψ (PowerSeries.C o) = PowerSeries.C (algebraMap O LL o))
  (u : PowerSeries LL) (hu : IsUnit u) (hψ : ψ (PowerSeries.X + PowerSeries.C l) = PowerSeries.X * u)
include hinj hψC hu hψ


theorem poly_eq_zero : ∀ (k : ℕ) (r : Polynomial O), r.degree < k →
    PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) → r = 0 := by
  have dvd_of_dvd_isUnit_mul_lemma {R : Type _} [CommRing R] {u f g : R} (hu : IsUnit u)
      (h : g ∣ u * f) : g ∣ f := by
    obtain ⟨v, rfl⟩ := hu
    have e : f = ↑v⁻¹ * (↑v * f) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact dvd_mul_of_dvd_right h _
  have hψX : ψ PowerSeries.X = PowerSeries.X * u - PowerSeries.C (algebraMap O LL l) := by
    have h := hψ
    rw [map_add (f := _), hψC] at h
    exact eq_sub_of_add_eq h
  intro k
  induction k with
  | zero =>
    intro r hr _
    by_contra hr0
    rw [Polynomial.degree_eq_natDegree hr0] at hr
    have h0 : r.natDegree < 0 := by exact_mod_cast hr
    omega
  | succ k ih =>
    intro r hr hdvd
    have hmon : (Polynomial.X + Polynomial.C l : Polynomial O).Monic := Polynomial.monic_X_add_C l
    have hrem : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) = Polynomial.C (r.eval (-l)) := by
      have hg : (Polynomial.X + Polynomial.C l : Polynomial O) = Polynomial.X - Polynomial.C (-l) := by
        rw [map_neg, sub_neg_eq_add]
      rw [hg]
      exact Polynomial.modByMonic_X_sub_C_eq_C_eval r (-l)
    have hsplit : r = Polynomial.C (r.eval (-l)) +
        (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) := by
      have h1 : Polynomial.modByMonic r (Polynomial.X + Polynomial.C l) +
          (Polynomial.X + Polynomial.C l) * Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = r := by
        first
          | exact Polynomial.modByMonic_add_div r (Polynomial.X + Polynomial.C l)
          | exact Polynomial.modByMonic_add_div r _ hmon
          | exact Polynomial.modByMonic_add_div r hmon
      rw [hrem] at h1
      exact h1.symm
    have hqdeg : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < k := by
      by_cases hq0 : Polynomial.divByMonic r (Polynomial.X + Polynomial.C l) = 0
      · rw [hq0, Polynomial.degree_zero]
        first
          | exact WithBot.bot_lt_coe _
          | simp
      · have hr0 : r ≠ 0 := by
          rintro rfl
          exact hq0 (Polynomial.zero_divByMonic _)
        have hpos : 0 < (Polynomial.X + Polynomial.C l : Polynomial O).degree := by
          first
            | (rw [Polynomial.degree_X_add_C]; exact zero_lt_one)
            | simp
        have h1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).degree < r.degree := by
          first
            | exact Polynomial.degree_divByMonic_lt r (Polynomial.X + Polynomial.C l) hr0 hpos
            | exact Polynomial.degree_divByMonic_lt r _ hmon hr0 hpos
            | exact Polynomial.degree_divByMonic_lt r hmon hr0 hpos
        rw [Polynomial.degree_eq_natDegree hq0, Polynomial.degree_eq_natDegree hr0] at h1
        rw [Polynomial.degree_eq_natDegree hr0] at hr
        rw [Polynomial.degree_eq_natDegree hq0]
        have a1 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < r.natDegree := by
          exact_mod_cast h1
        have a2 : r.natDegree < k + 1 := by exact_mod_cast hr
        have a3 : (Polynomial.divByMonic r (Polynomial.X + Polynomial.C l)).natDegree < k := by omega
        exact_mod_cast a3
    obtain ⟨c, q, hrq, hq⟩ : ∃ (c : O) (q : Polynomial O),
        r = Polynomial.C c + (Polynomial.X + Polynomial.C l) * q ∧ q.degree < k :=
      ⟨_, _, hsplit, hqdeg⟩
    have hψr : ψ (r : PowerSeries O) =
        PowerSeries.C (algebraMap O LL c) + PowerSeries.X * (u * ψ (q : PowerSeries O)) := by
      rw [hrq]
      first
        | (simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X,
            map_add, map_mul, hψC, hψX]; ring)
        | (simp [hψC, hψX]; ring)
    have hX : PowerSeries.X ∣ ψ (r : PowerSeries O) :=
      (dvd_pow_self _ (Nat.succ_ne_zero k)).trans hdvd
    rw [hψr, PowerSeries.X_dvd_iff] at hX
    first
      | simp only [map_add (f := _), map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
          zero_mul, add_zero] at hX
      | simp at hX
    have hc0 : c = 0 := hinj (hX.trans (map_zero _).symm)
    simp only [hc0, map_zero, zero_add] at hψr
    rw [hψr, pow_succ'] at hdvd
    have h2 : PowerSeries.X ^ k ∣ u * ψ (q : PowerSeries O) :=
      (mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hdvd
    have hq0 : q = 0 := ih q hq (dvd_of_dvd_isUnit_mul_lemma hu h2)
    rw [hrq, hc0, hq0]
    simp

theorem dvd_of_dvd_image [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : l ∈ IsLocalRing.maximalIdeal O) (k : ℕ) (a : PowerSeries O)
    (ha : PowerSeries.X ^ k ∣ ψ a) : (PowerSeries.X + PowerSeries.C l) ^ k ∣ a := by
  have hres : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) =
      PowerSeries.X ^ k := by
    rw [map_pow, map_add (f := _), PowerSeries.map_X, PowerSeries.map_C,
      (IsLocalRing.residue_eq_zero_iff l).mpr hlm, map_zero, add_zero]
  have hg : PowerSeries.map (IsLocalRing.residue O) ((PowerSeries.X + PowerSeries.C l) ^ k) ≠ 0 := by
    rw [hres]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision (f := a) hg
  have hdeg : r.degree < k := by
    have h := hdiv.degree_lt
    have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) l = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hlm
    first
      | simpa [hz, PowerSeries.order_X_pow] using h
      | simpa [hz] using h
      | (rw [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
      | (simp only [hres, PowerSeries.order_X_pow, ENat.toNat_coe] at h; exact h)
      | simpa [hres] using h
  have hψa : ψ a = (PowerSeries.X * u) ^ k * ψ q + ψ (r : PowerSeries O) := by
    rw [hdiv.eq_mul_add, map_add (f := _), map_mul, map_pow, hψ]
  have h1 : PowerSeries.X ^ k ∣ (PowerSeries.X * u) ^ k * ψ q :=
    dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  have h2 : PowerSeries.X ^ k ∣ ψ (r : PowerSeries O) := by
    rw [hψa] at ha
    first
      | exact (dvd_add_right h1).mp ha
      | simpa using dvd_sub ha h1
  have hr0 : r = 0 := poly_eq_zero hinj l ψ hψC u hu hψ k r hdeg h2
  rw [hdiv.eq_mul_add, hr0, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

end Formalism.MainNotions.N.Pv.LocalLengthBound.Wd
end
end

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section CritB

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem hasSubst_pi0_series (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries.HasSubst W.π₀₁ :=
  PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)

def at0Hom (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries O →+* LetA O n :=
  Pi.ringHom fun _ => (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)).toRingHom

theorem at0Hom_apply (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f : PowerSeries O) :
    at0Hom W hR f = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
  funext i
  show (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)) f = PowerSeries.subst W.π₀₁ f
  rw [PowerSeries.coe_substAlgHom]

theorem evalZero_X_eq_pi0 (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  exact PowerSeries.subst_X (hasSubst_pi0_series W hR)

theorem evalZero_C (o : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C o) = algebraMap O (LetA O n) o := by
  funext i
  simp [Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0, PowerSeries.subst_C, PowerSeries.algebraMap_eq]
  rfl

theorem evalZero_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  rw [← at0Hom_apply W hR, ← at0Hom_apply W hR, ← at0Hom_apply W hR, map_mul]

theorem qp_unit_EE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπ₀ : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  obtain ⟨U, hU⟩ := hπ₀
  haveI := W.EE_complete
  have hJ : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
      (Ideal.subset_span (Set.mem_singleton _))
  have h1 : IsUnit (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) :=
    Ideal.mem_jacobson_bot.1 hJ _
  have e : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) =
      (U : W.EE) * (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (U : W.EE), mul_assoc, Units.mul_inv, mul_one, hU]
    simp [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast, add_comm]
  rw [e]
  exact U.isUnit.mul h1

theorem qp_pow_cancel (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (k : ℕ)
    {x y : W.DD T} (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = Formalism.MainNotions.LiftingTheory.qp W ^ k • y) : x = y := by
  have hu : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k)) := by
    rw [map_pow]; exact (qp_unit_EE W hR).pow _
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x,
    ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) y] at h
  exact hu.smul_left_cancel.1 h

end CritB

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section PhiInj

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem φVB_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := V) y = ((PD.φ.toLinearMap).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj hab

end PhiInj

section CritB2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem isExp_zero (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (0 : W.DD T) (fun _ => 0) := by
  have h0 : (1 : LetA O n) • (0 : W.DD T) ∈ W.N T := by rw [smul_zero]; exact (W.N T).zero_mem
  refine ⟨⟨0, fun _ _ => rfl⟩, 1, h0, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩
  have e : (⟨(1 : LetA O n) • (0 : W.DD T), h0⟩ : ↥(W.N T)) = 0 := Subtype.ext (smul_zero _)
  rw [e, map_zero, conv_eq]
  simp [smulS]

theorem pullJ_exp (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) :
    ∀ x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1, ∃ d : ℤ → T.V ⊗[Qp] BdR,
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d ∧ ∀ k : ℤ, k < 0 → d k = 0 := by
  have hs : W.s = 1 := hA.2.1
  obtain ⟨hN, hAg⟩ := gam_of_tie W hs C
  obtain ⟨-, -, hAdd, -, -, -, -⟩ := expRules_of W h4 hN hAg hA T hT i ζ hζ
  intro x hx
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hy, hyD⟩, rfl⟩ := hx
    rw [pow_one]
    obtain ⟨d, hd, hn, -⟩ := phi_exp W hs C h4W T hT i hζ y hy hyD.1
    exact ⟨d, hd, hn⟩
  | zero => exact ⟨fun _ => 0, isExp_zero W T i ζ, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hn⟩ := hx
    obtain ⟨e, he, hn'⟩ := hy
    exact ⟨d + e, hAdd _ _ _ _ hd he, fun k hk => by simp [hn k hk, hn' k hk]⟩
  | smul a x _ hx =>
    obtain ⟨d, hd, hn⟩ := hx
    exact ⟨smulS (W.lev i ζ a) d, isExp_smulA W T i ζ hd a, fun k hk => LB_smulS hn _ k hk⟩

theorem indep_phi_cmp (hdom : IsDomain O) (hFr : IsFractionRing O LL)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (i : ZMod n) {r : ℕ} (e : Fin r → W.DD T)
    (he : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) (c : Fin r → LL)
    (hc : ∑ m, c m • ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V)
      (W.cmp T ⟨e m, (he.1 m).1⟩)) = 0) : c = 0 := by
  haveI := hdom
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  have hsum : ∑ m, c m • W.cmp T ⟨e m, (he.1 m).1⟩ = 0 := by
    apply φVB_inj PD (LL := LL) (V := T.V)
    apply Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (LL := LL) (V := T.V)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_zero, map_sum, map_sum]
    simpa [map_smul] using hc
  obtain ⟨⟨dd, hdd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin r)) c
  choose o ho using fun m => hint m (Finset.mem_univ m)
  have hdne : algebraMap O LL dd ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdd
  set z : W.DD T := ∑ m, o m • e m with hz
  have hzN : z ∈ W.N T := Submodule.sum_mem _ fun m _ => by
    rw [← algebraMap_smul (LetA O n) (o m) (e m)]; exact (W.N T).smul_mem _ (he.1 m).1
  have hzD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [hz, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [smul_comm, (he.1 m).2.1]
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [map_smul, (he.1 m).2.2 δ hδ]
  have hcz : W.cmp T ⟨z, hzN⟩ = 0 := by
    have e1 : (⟨z, hzN⟩ : ↥(W.N T)) = ∑ m, o m • (⟨e m, (he.1 m).1⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp [hz, Submodule.coe_sum])
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [W.cmp_smul]
    calc ∑ m, algebraMap O LL (o m) • W.cmp T ⟨e m, (he.1 m).1⟩
        = ∑ m, algebraMap O LL dd • (c m • W.cmp T ⟨e m, (he.1 m).1⟩) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [ho m, Algebra.smul_def, mul_smul]
      _ = 0 := by rw [← Finset.smul_sum, hsum, smul_zero]
  have hPN := ker_NDl W T i h3 hmod hR (x := z) ⟨hzN, hzD⟩
    (by unfold Formalism.MainNotions.ArcLiftingSetup.cmpD; rw [dite_eq_left hzN]; exact hcz)
  obtain ⟨y, hy, hyΔ, hzy⟩ := hPN
  rw [pow_one] at hzy
  have hyl : (letE i : LetA O n) • y = y := by
    apply RL.pi0_pow_smul_injective W T hR.2.2.1 1
    rw [pow_one, smul_comm, ← hzy, hzD.1]
  obtain ⟨b, hb, -⟩ := he.2 y hy ⟨hyl, hyΔ⟩
  have rep1 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C (o m)) • e m := by
    rw [hz]
    exact Finset.sum_congr rfl fun m _ => by rw [evalZero_C, algebraMap_smul]
  have rep2 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.X * b m) • e m := by
    rw [hzy, hb, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul, evalZero_mul W hR, evalZero_X_eq_pi0 W hR]
  have heq := (he.2 z hzN hzD).unique rep1 rep2
  funext m
  have h0 : o m = 0 := by
    have := congrArg (fun f => PowerSeries.constantCoeff (f m)) heq
    simpa using this
  have : algebraMap O LL dd * c m = 0 := by
    rw [← Algebra.smul_def, ← ho m, h0, map_zero]
  exact (mul_eq_zero.1 this).resolve_left hdne

end CritB2

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section CritB3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem expCritP_of [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) [IsDomain O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hinj : Function.Injective (algebraMap O LL))
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hFr : IsFractionRing O LL)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt) :
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x →
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d →
        ((∃ k : ℕ, Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1) →
          (x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1 ↔ ∀ k : ℤ, k < 0 → d k = 0)) := by
  intro T hT i ζ hζ x d hDL hd ⟨k, hk⟩
  have hs : W.s = 1 := hA.2.1
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have h9T := ((h9 T hT) hs hA.2.2).2.2 hfin
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W := h9T.1
  have hmod := h9T.2
  obtain ⟨hN, hAg⟩ := gam_of_tie W hs C
  obtain ⟨-, hval, hAdd, -, -, -, -⟩ := expRules_of W h4 hN hAg hA T hT i ζ hζ
  constructor
  · intro hx
    obtain ⟨d', hd', hn'⟩ := pullJ_exp W hA h4 C h4W T hT i hζ x hx
    rw [isExp_unique W T i ζ hd hd']
    exact hn'
  · intro hneg
    obtain ⟨⟨e, he⟩, hB2⟩ := hB hA T hT (i - 1)
    have hi1 : i - 1 + ((1 : ℕ) : ZMod n) = i := by push_cast; ring
    have hqΔ : ∀ δ ∈ W.DelF, W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
      intro δ hδ
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add (f := _), map_natCast, hring.1 δ hδ]
    have hDLy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (i - 1 + ((1 : ℕ) : ZMod n)) (Formalism.MainNotions.LiftingTheory.qp W ^ k • x) := by
      rw [hi1]
      refine ⟨by rw [smul_comm, hDL.1], fun δ hδ => ?_⟩
      rw [RL.γD_smulA, map_pow, hqΔ δ hδ, hDL.2 δ hδ]
    obtain ⟨a, ha, -⟩ := (hB2 _ e he 1).1 _ hk hDLy

    have hE : ∀ m, ∃ Em : ℤ → T.V ⊗[Qp] BdR,
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (((W.φD T) ^ 1) (e m)) Em ∧ (∀ j : ℤ, j < 0 → Em j = 0) ∧
          Em 0 = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V)
            (W.cmp T ⟨e m, (he.1 m).1⟩)) := by
      intro m
      rw [pow_one]
      exact phi_exp W hs C h4W T hT i hζ (e m) (he.1 m).1 (he.1 m).2.1
    choose Em hEx hEn hE0 using hE
    have hsumExp : ∀ s : Finset (Fin (Module.finrank LL T.V)),
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (∑ m ∈ s, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m) • ((W.φD T) ^ 1) (e m))
          (∑ m ∈ s, smulS (W.lev i ζ (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m))) (Em m)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact isExp_zero W T i ζ
      | insert m s hm ih =>
        rw [Finset.sum_insert hm, Finset.sum_insert hm]
        exact hAdd _ _ _ _ (isExp_smulA W T i ζ (hEx m) _) ih
    have hy := hsumExp Finset.univ
    rw [← ha] at hy
    have heq := isExp_unique W T i ζ (isExp_smulA W T i ζ hd (Formalism.MainNotions.LiftingTheory.qp W ^ k)) hy
    obtain ⟨u, hu, hlq⟩ := (expRing_of W hring hA i ζ hζ).1
    have hdLB : LB 0 d := fun j hj => hneg j hj

    let Fil : ℤ → Submodule LL (T.V ⊗[Qp] BdR) := fun a => if a ≤ 0 then ⊤ else ⊥
    have hFa : Antitone Fil := by
      intro a b hab
      by_cases hb : b ≤ 0
      · rw [show Fil a = ⊤ from if_pos (le_trans hab hb), show Fil b = ⊤ from if_pos hb]
      · rw [show Fil b = ⊥ from if_neg hb]; exact bot_le
    haveI := fd_ιDi W hA hD T hT i
    have hDLφ : ∀ m, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (((W.φD T) ^ 1) (e m)) := by
      intro m
      rw [pow_one]
      refine ⟨Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T i (he.1 m).2.1, fun δ hδ => ?_⟩
      rw [← W.φγ_comm, (he.1 m).2.2 δ hδ]
    have hEmem : ∀ m j, Em m j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ⊓ Fil (-j) := by
      intro m j
      refine Submodule.mem_inf.2 ⟨hval _ _ (hDLφ m) (hEx m) j, ?_⟩
      by_cases hj : j < 0
      · rw [hEn m j hj]; exact Submodule.zero_mem _
      · rw [show Fil (-j) = ⊤ from if_pos (by omega)]; exact Submodule.mem_top
    have h₁ : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ⊓ Fil 1 = ⊥ := by
      rw [show Fil 1 = ⊥ from if_neg (by norm_num), inf_bot_eq]
    have hind : ∀ c : Fin (Module.finrank LL T.V) → LL,
        (∀ j, ∑ m, c m • Em m j ∈ Fil (-j + 1)) → c = 0 := by
      intro c hc
      have h0 := hc 0
      rw [show Fil (-(0 : ℤ) + 1) = ⊥ from if_neg (by norm_num), Submodule.mem_bot] at h0
      apply indep_phi_cmp W inferInstance hFr hring T (h3 T hT) hmod (i - 1) e he c
      rw [← h0]
      exact Finset.sum_congr rfl fun m _ => by rw [hE0 m]
    have hdg : ∀ j : ℤ, ∑ m, smulS (W.lev i ζ (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m))) (Em m) j ∈
        Fil ((k : ℤ) - j) := by
      intro j
      have e1 := congrFun heq j
      rw [Finset.sum_apply] at e1
      rw [← e1]
      by_cases hj : j < k
      · have h0 : smulS (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k)) d j = 0 := by
          rw [map_pow, hlq, mul_pow, mul_comm, smulS_mul hdLB, smulS_X_pow (LB_smulS hdLB _)]
          exact LB_smulS hdLB _ _ (by omega)
        rw [h0]; exact Submodule.zero_mem _
      · rw [show Fil ((k : ℤ) - j) = ⊤ from if_pos (by omega)]; exact Submodule.mem_top
    have hdvd := MC.dvd_of_dg hFa (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i) 1 h₁ hEmem hind k _ hdg

    let ψ : PowerSeries O →+* PowerSeries LL := (W.lev i ζ).toRingHom.comp (at0Hom W hring)
    have hψa : ∀ f, ψ f = W.lev i ζ (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f) := fun f => by
      show W.lev i ζ (at0Hom W hring f) = _
      rw [at0Hom_apply]
    have hψC : ∀ o : O, ψ (PowerSeries.C o) = PowerSeries.C (algebraMap O LL o) := by
      intro o
      rw [hψa, evalZero_C, AlgHom.commutes, PowerSeries.algebraMap_apply]
    have hqpe : W.π₀ + algebraMap O (LetA O n) ((PD.p : ℕ) : O) = Formalism.MainNotions.LiftingTheory.qp W := by
      rw [map_natCast]; rfl
    have hψ : ψ (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = PowerSeries.X * u := by
      rw [hψa, ← at0Hom_apply W hring, map_add (f := _), at0Hom_apply, at0Hom_apply, evalZero_X_eq_pi0 W hring, evalZero_C,
        hqpe, hlq, mul_comm]
    have hdiv : ∀ m, (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ k ∣ a m := fun m =>
      Wd.dvd_of_dvd_image hinj ((PD.p : ℕ) : O) ψ hψC u hu hψ hlm k (a m)
        (by rw [hψa]; exact hdvd m)
    choose g hg using hdiv
    have hat0 : ∀ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m) =
        Formalism.MainNotions.LiftingTheory.qp W ^ k * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (g m) := by
      intro m
      rw [hg m, evalZero_mul W hring, ← at0Hom_apply W hring
        ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ k), map_pow, map_add, at0Hom_apply,
        at0Hom_apply, evalZero_X_eq_pi0 W hring, evalZero_C, hqpe]
    have hx' : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = Formalism.MainNotions.LiftingTheory.qp W ^ k •
        ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (g m) • ((W.φD T) ^ 1) (e m) := by
      rw [ha, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [hat0 m, mul_smul]
    rw [qp_pow_cancel W hring T k hx']
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨e m, ⟨(he.1 m).1, (he.1 m).2⟩, rfl⟩)

theorem expCrit_of [NeZero n] [IsDomain O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hinj : Function.Injective (algebraMap O LL))
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hFr : IsFractionRing O LL)
    (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt) (hΔ : PtTrans W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W := by
  intro hA T hT i ζ hζ x d hDL hd
  have hs : W.s = 1 := hA.2.1
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W := (((h9 T hT) hs hA.2.2).2.2 hfin).1
  exact ⟨expCritN_of W hA inferInstance hFr h1 h3 h4 h5 hD hring (gamΔ_of_tie W C) hΔ T hT i ζ hζ
      x d hDL hd,
    expCritP_of W hA hinj hlm hFr h3 h4 h9 hD hB C h4W T hT i ζ hζ x d hDL hd⟩

end CritB3

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem l_mem_maxOL {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) [IsLocalRing ↥(OL LL)] :
    ((l : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨w, hw⟩
  have hv := P.v_l LL
  have h1 := (P.v_O LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))).2 (w : ↥(OL LL)).2
  have h2 := (P.v_O LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)))).2
    ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2
  have h3 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
      P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
  have h4 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0 :=
    le_antisymm (le_trans (le_add_of_nonneg_right h2) h3.le) h1
  rw [hw, map_natCast] at h4
  rw [h4] at hv
  exact zero_ne_one hv


set_option maxHeartbeats 800000 in
theorem expCrit_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F)
    (hB : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hg))
    (hCpl : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) [IsLocalRing ↥(OL LL)],
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL)) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL hA' h5
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI := hCpl l LL
  have h1 := hA.1 l K 1 LL hA'.2.2
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1
  have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact l_mem_maxOL (D.loc l) LL
  have tie := ((Cm l).C K 1 LL hA'.2.2).tie
  exact expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL) h1.1 h1.2.2.1
    (hL l K LL hA' h5) h1.2.2.2.2.1 h1.2.2.2.2.2.2.2.2.1 h11.2.2 (hB l K LL hA'.2.2) tie
    h1.2.2.2.1 (ptTrans_rec D HW F hP9 l K LL hA' h5)

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.OLC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem isAdicComplete_of_le {R : Type} [CommRing R] (I J : Ideal R) (a : ℕ) (ha : 1 ≤ a)
    (h1 : I ^ a ≤ J) (h2 : J ≤ I) [hJ : IsAdicComplete J R] : IsAdicComplete I R := by
  have hpow : ∀ n, I ^ (a * n) ≤ J ^ n := fun n => by
    rw [pow_mul]; exact Ideal.pow_right_mono h1 n
  have hJI : ∀ n, J ^ n ≤ I ^ n := fun n => Ideal.pow_right_mono h2 n
  have hsm : ∀ (K L : Ideal R), K ≤ L → K • (⊤ : Submodule R R) ≤ L • ⊤ := fun K L h =>
    Submodule.smul_mono_left h
  have hH : IsHausdorff I R := ⟨fun x hx => by
    apply IsHausdorff.haus hJ.toIsHausdorff x
    intro n
    exact (hx (a * n)).mono (hsm _ _ (hpow n))⟩
  have hP : IsPrecomplete I R := ⟨fun f hf => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ.toIsPrecomplete (f := fun k => f (a * k)) (fun {m n} hmn =>
      (hf (Nat.mul_le_mul_left a hmn)).mono (hsm _ _ (hpow m)))
    refine ⟨L, fun n => ?_⟩
    have h3 : f n ≡ f (a * n) [SMOD I ^ n • (⊤ : Submodule R R)] := hf (by nlinarith)
    exact h3.trans ((hL n).mono (hsm _ _ (hJI n)))⟩
  exact ⟨⟩

theorem complete_max {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  have := Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h
    have h' : ((((l : ℕ) : ↥(OL LL)) : ↥LL.1) : Om l) = 0 := by rw [h]; rfl
    norm_cast at h'
    exact (Fact.out : l.Prime).ne_zero h'
  obtain ⟨e, u, hle⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have he : 1 ≤ e := by
    by_contra h0
    push Not at h0
    have : e = 0 := by omega
    rw [this, pow_zero, mul_one] at hle
    rw [hle] at hlm
    exact (IsLocalRing.mem_maximalIdeal _).mp hlm u.isUnit
  refine isAdicComplete_of_le _ (Ideal.span {((l : ℕ) : ↥(OL LL))}) e he ?_ ?_
  · rw [hmax, Ideal.span_singleton_pow, hle, Ideal.span_singleton_mul_left_unit u.isUnit]
  · rw [Ideal.span_le]; rintro _ rfl; exact hlm

end Formalism.MainNotions.N.Pv.LocalLengthBound.OLC

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem expCrit_D' (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F)
    (hB : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hg : Good K 1 LL)
      [NeZero (Module.finrank ℚ_[l] ↥(K0 K))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hg)) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL h.2.2) :=
  expCrit_D D HW F Cm CR CA CB CK hA hL hB fun l _ LL _ => by
    convert OLC.complete_max LL

end Formalism.MainNotions.N.Pv.LocalLengthBound
