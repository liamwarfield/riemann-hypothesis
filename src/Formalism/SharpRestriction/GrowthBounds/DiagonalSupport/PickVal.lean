module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickLem
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section Co

variable {σ τ : Type} {Kf : Type} [Field Kf]

theorem coeff_planeCoeff (nu : τ →₀ ℕ) (F : MvPolynomial σ (MvPolynomial τ Kf)) (bp : σ →₀ ℕ) :
    (planeCoeff nu F).coeff bp = (F.coeff bp).coeff nu := by
  unfold planeCoeff
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [notMem_support_iff.1 h]

theorem coeff_oneT (e : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf)) (bp : σ →₀ ℕ) :
    (oneT e F).coeff bp = e (F.coeff bp) := by
  unfold oneT
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem coeff_diagK (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) (mo : σ →₀ ℕ) :
    (diagK g F).coeff mo = g mo * F.coeff mo := by
  unfold diagK
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, mul_zero]

theorem diagK_mem_pol {ι : Type} {n : ℕ} (d : ι → ℕ) (g : (ι × Fin n →₀ ℕ) → Kf) {F : MvPolynomial (ι × Fin n) Kf}
    (hF : F ∈ Pol Kf n d) : diagK g F ∈ Pol Kf n d := by
  rw [Pol, mem_restrictSupport_iff] at hF ⊢
  intro mo hmo
  apply hF
  rw [Finset.mem_coe, mem_support_iff] at hmo ⊢
  rw [coeff_diagK] at hmo
  exact right_ne_zero_of_mul hmo

theorem fock_eq_sum (F G : MvPolynomial σ Kf) (s : Finset (σ →₀ ℕ)) (hs : G.support ⊆ s) :
    fock F G = ∑ m ∈ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
  unfold fock
  have h1 : ∑ m ∈ F.support, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) =
      ∑ m ∈ F.support ∪ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
    refine Finset.sum_subset Finset.subset_union_left fun m _ hm => ?_
    rw [notMem_support_iff.1 hm, zero_mul, zero_mul]
  have h2 : ∑ m ∈ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) =
      ∑ m ∈ F.support ∪ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
    refine Finset.sum_subset Finset.subset_union_right fun m _ hm => ?_
    have : m ∉ G.support := fun h => hm (hs h)
    rw [notMem_support_iff.1 this, mul_zero, zero_mul]
  rw [h1, h2]

theorem fock_monomial_right (F : MvPolynomial σ Kf) (nu : σ →₀ ℕ) :
    fock F (monomial nu 1) = F.coeff nu * ((expFact nu : ℕ) : Kf) := by
  rw [fock_eq_sum F _ {nu} (by
    intro m hm
    rw [mem_support_iff, coeff_monomial] at hm
    by_contra h
    rw [Finset.mem_singleton] at h
    exact hm (if_neg fun h' => h h'.symm))]
  rw [Finset.sum_singleton, coeff_monomial, if_pos rfl, mul_one]

theorem fock_smul_left (c : Kf) (F G : MvPolynomial σ Kf) : fock (c • F) G = c * fock F G := by
  rw [fock_eq_sum _ _ _ (Finset.Subset.refl _), fock_eq_sum F _ _ (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring

theorem fock_smul_right (c : Kf) (F G : MvPolynomial σ Kf) : fock F (c • G) = c * fock F G := by
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring

end Co

section VB

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem vBB_le_coeff (F : MvPolynomial σ (KK O)) (m : σ →₀ ℕ) :
    vBB (O := O) p F ≤ vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  by_cases h : m ∈ F.support
  · exact Finset.inf_le h
  · rw [notMem_support_iff.1 h, valuation_zero_alt, WithTop.top_add]
    exact le_top

theorem vBB_attained (F : MvPolynomial σ (KK O)) (hF : vBB (O := O) p F ≠ ⊤) :
    ∃ m ∈ F.support, vBB (O := O) p F = vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  have hne : F.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hF
    unfold vBB
    rw [h, Finset.inf_empty]
  exact Finset.exists_mem_eq_inf _ hne _

theorem vBB_smul (c : KK O) (hc : c ≠ 0) (F : MvPolynomial σ (KK O)) :
    vBB (O := O) p (c • F) = vK p c + vBB (O := O) p F := by
  unfold vBB
  have hs : (c • F).support = F.support := by
    ext m
    simp [MvPolynomial.mem_support_iff, hc]
  rw [hs]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, valuation_mul_alt, add_assoc]
  by_cases hne : F.support.Nonempty
  · exact (Finset.apply_inf_eq_inf_comp_of_linearOrder (fun y : WithTop ℚ => vK p c + y)
      (fun a b hab => add_le_add_right hab _) (by simp)).symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

theorem vK_inv (x : KK O) (q : ℚ) (hx : vK p x = (q : WithTop ℚ)) : vK p x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [valuation_zero_alt] at hx
    exact WithTop.top_ne_coe hx
  have h := valuation_mul_alt p x x⁻¹
  rw [mul_inv_cancel₀ hx0, valuation_one_eq_zero_alt, hx] at h
  obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 (h.symm.trans (by rfl : (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ)))
  have h1 : a = q := by exact_mod_cast ha
  rw [← hb]
  congr 1
  linarith

theorem vK_w_pow (hp : p.Prime) (S : UniformizedDVR p O) (w : O) (hw : w ^ 2 = (p : O)) (n : ℕ) :
    vK p ((algebraMap O (KK O) w) ^ n) = (((n : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  have h1 : vK p (algebraMap O (KK O) w) = (((1 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    have h2 : (algebraMap O (KK O) w) * (algebraMap O (KK O) w) = ((p : ℕ) : KK O) := by
      rw [← map_mul, ← pow_two, hw, map_natCast]
    have h3 := congrArg (vK p) h2
    rw [valuation_mul_alt, valuation_natCast_padicVal hp S p hp.ne_zero, Nat.padicValNat_def, Nat.multiplicity_self hp.one_lt] at h3
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 h3
    have hab' : a = b := by
      have : (a : WithTop ℚ) = (b : WithTop ℚ) := by rw [ha, hb]
      exact_mod_cast this
    rw [← ha]
    congr 1
    push_cast at hab
    linarith
  induction n with
  | zero => rw [pow_zero, valuation_one_eq_zero_alt]; simp
  | succ n ih =>
    rw [pow_succ, valuation_mul_alt, ih, h1, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

end VB

end Formalism.MainNotions.Proposition5Numerics
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem support_diagK_subset {σ Kf : Type} [Field Kf] (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) :
    (diagK g F).support ⊆ F.support := by
  intro mo hmo
  rw [mem_support_iff] at hmo ⊢
  rw [coeff_diagK] at hmo
  exact right_ne_zero_of_mul hmo

section Id

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem value_exact (d : Fin n' → ℕ) (hDig : DigFacts Fr p O hk nL d) (G : MvPolynomial (TV n' (m + 1)) (KK O))
    (hG : HasMultideg G d) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (hrho : ∀ x c, rho (x, c) < lowP Fr p x)
    (hgn : ∀ bn, ((gamNo Fr p nL rho bn : ℚ) : KK O) ≠ 0)
    (e : Module.End (KK O) (MvPolynomial (TL J nL r × Fin K) (KK O)))
    (hsa : ∀ F G, fock (e F) G = fock F (e G)) (nu : TL J nL r × Fin K →₀ ℕ) (cY : KK O)
    (hpol : e (monomial nu 1) ∈ Pol (KK O) K dNo)
    (A : MvPolynomial (TL J nL r × Fin r) (KK O)) (hA : A ∈ Pol (KK O) r dPl) :
    fock G (asm Fr p O hk nL rho A
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)))) =
      ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) * cY * ((expFact nu : ℕ) : KK O) *
        fock (planeCoeff nu (oneT e (levImg Fr p hk nL rho dPl dNo G)))
          (diagK (fun bp => ((gamPl Fr p nL rho bp : ℚ) : KK O)) A) := by
  have hNpol0 : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) ∈ Pol (KK O) K dNo :=
    diagK_mem_pol _ _ (Submodule.smul_mem _ _ hpol)
  obtain ⟨Nex, hNex⟩ : ∃ Nex, Nex = diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1)) :=
    ⟨_, rfl⟩
  rw [← hNex]
  have hNpol : Nex ∈ Pol (KK O) K dNo := by rw [hNex]; exact hNpol0
  rw [(hDig G hG).1 rho dPl dNo hrho A hA Nex hNpol]
  have hback : diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex = cY • e (monomial nu 1) := by
    ext bn
    rw [coeff_diagK, hNex, coeff_diagK, ← mul_assoc, mul_inv_cancel₀ (hgn bn), one_mul]
  have hin : ∀ bp : TL J nL r × Fin r →₀ ℕ,
      ∑ bn ∈ Nex.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * Nex.coeff bn * ((expFact bn : ℕ) : KK O)) =
        (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
          (cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O))) := by
    intro bp
    have h1 : fock ((levImg Fr p hk nL rho dPl dNo G).coeff bp)
        (diagK (fun bn => ((gamNo Fr p nL rho bn : ℚ) : KK O)) Nex) =
        cY * ((e ((levImg Fr p hk nL rho dPl dNo G).coeff bp)).coeff nu * ((expFact nu : ℕ) : KK O)) := by
      rw [hback, fock_smul_right, ← hsa, fock_monomial_right]
    rw [← h1, fock_eq_sum _ _ Nex.support (support_diagK_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun bn _ => ?_
    rw [coeff_diagK]; ring
  rw [Finset.sum_congr rfl fun bp _ => hin bp]
  rw [fock_eq_sum _ _ A.support (support_diagK_subset _ _), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun bp _ => ?_
  rw [coeff_planeCoeff, coeff_oneT, coeff_diagK]; ring

theorem asm_add_right (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N N' : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    asm Fr p O hk nL rho A (N + N') = asm Fr p O hk nL rho A N + asm Fr p O hk nL rho A N' := by
  unfold asm
  rw [map_add (f := _)]; ring

end Id

theorem asm_coefGe' {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
    (rho : TL J nL r × Fin (r + K) → ℕ) {A : MvPolynomial (TL J nL r × Fin r) (KK O)}
    {N : MvPolynomial (TL J nL r × Fin K) (KK O)} {t : ℝ} (hA : CoefGe p A 0) (hN : CoefGe p N t) :
    CoefGe p (asm Fr p O hk nL rho A N) t := by
  unfold asm
  have h1 : CoefGe p (monomial (labMon Fr hk nL rho) (1 : KK O)) 0 := CoefGe.monomial _ geQ_one
  have h2 : CoefGe p (upPl Fr p O hk nL A) 0 := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hA
  have h3 : CoefGe p (upNo Fr p O hk nL N) t := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hN
  have h4 := CoefGe.mul (CoefGe.mul h1 h2) h3
  simpa using h4

theorem padicVal_expFact_le (p : ℕ) [hp : Fact p.Prime] {n' k : ℕ} (d : Fin n' → ℕ) (α : Fin n' × Fin k →₀ ℕ)
    (hα : ∀ s, multideg α s = d s) : padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : Fin n', ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : Fin n', Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hMn0 hE0]
  omega

end Formalism.MainNotions.Proposition5Numerics
