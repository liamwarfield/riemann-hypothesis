module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AdjointEndPairMemGaugedCurveLogarithms
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitsInLevelPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralSmulCurveCoeffSeriesOfChartHOfLinearLog
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupCocycleLthPowerCoboundaryModMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupCocycleLthPowerCoboundaryModMaximal
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowVal GlobalTheory.RowVal.EndCalc ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.CocyclePow

open MvPowerSeries

section Alg

variable {C R : Type} [Field C] [CommRing R] [Algebra C R]

theorem coeff_pow_mem (S : Subring R) (G : PowerSeries R) (j : ℕ) (h : ∀ i ≤ j, PowerSeries.coeff i G ∈ S) (k : ℕ) :
    ∀ i ≤ j, PowerSeries.coeff i (G ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ k ih =>
    intro i hi
    rw [pow_succ, PowerSeries.coeff_mul]
    refine sum_mem fun p hp => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    exact mul_mem (ih _ (by omega)) (h _ (by omega))

theorem exp_coeff_split (G : PowerSeries R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1 + 1), ((k.factorial : C))⁻¹ • PowerSeries.coeff (n + 1) ((PowerSeries.X * G) ^ k) =
      ∑ k ∈ Finset.range n, (((k + 2).factorial : C))⁻¹ • PowerSeries.coeff (n - (k + 1)) (G ^ (k + 2)) +
        PowerSeries.coeff n G := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, smul_zero, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
  congr 3
  omega

theorem exp_low [CharZero C] (S : Subring R) {l : ℕ} (hl : l.Prime)
    (hS : ∀ u : ℕ, ¬ l ∣ u → ∀ x ∈ S, (u : C)⁻¹ • x ∈ S) (G : PowerSeries R) (h0 : PowerSeries.constantCoeff G = 0)
    (hA : ∀ n, ∑ k ∈ Finset.range (n + 1), ((k.factorial : C))⁻¹ • PowerSeries.coeff n (G ^ k) ∈ S) :
    PowerSeries.coeff 1 G ∈ S ∧
      ∃ s ∈ S, PowerSeries.coeff 1 G ^ l - (l : C) • PowerSeries.coeff l G = (l : C) • s := by
  obtain ⟨G, rfl⟩ := PowerSeries.X_dvd_iff.2 h0
  have hfac : ∀ k < l, ¬ l ∣ k.factorial := fun k hk h => absurd ((hl.dvd_factorial).1 h) (by omega)
  have low : ∀ n, n + 1 < l → PowerSeries.coeff n G ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h := hA (n + 1)
      rw [exp_coeff_split] at h
      refine (add_mem_cancel_left (sum_mem fun k hk => ?_)).1 h
      have hk' := Finset.mem_range.1 hk
      exact hS _ (hfac _ (by omega)) _
        (coeff_pow_mem S G (n - (k + 1)) (fun i hi => ih i (by omega) (by omega)) _ _ le_rfl)
  have e1 : PowerSeries.coeff 0 G ∈ S := by
    have h := hA (0 + 1)
    rw [exp_coeff_split] at h
    simpa using h
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by have := hl.two_le; omega⟩
  have h := hA (m + 1 + 1)
  rw [exp_coeff_split, Finset.sum_range_succ, add_assoc] at h
  have h2 := (add_mem_cancel_left (sum_mem fun k hk => by
    have hk' := Finset.mem_range.1 hk
    exact hS _ (hfac _ (by omega)) _
      (coeff_pow_mem S G (m + 1 - (k + 1)) (fun i hi => by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact e1
        · exact low i (by omega)) _ _ le_rfl))).1 h
  rw [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow] at h2
  have c1 : PowerSeries.coeff 1 (PowerSeries.X * G) = PowerSeries.constantCoeff G := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact PowerSeries.coeff_succ_X_mul 0 G
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at e1
  rw [c1, PowerSeries.coeff_succ_X_mul]
  refine ⟨e1, ?_⟩
  obtain ⟨w, hw⟩ : m + 2 ∣ (m + 1).factorial + 1 := by
    haveI := Fact.mk hl
    rw [← ZMod.natCast_eq_zero_iff]
    have := ZMod.wilsons_lemma (m + 2)
    push_cast
    rw [show m + 2 - 1 = m + 1 from rfl] at this
    rw [this]; ring
  have hwC : ((m + 1).factorial : C) + 1 = ((m + 2 : ℕ) : C) * w := by exact_mod_cast hw
  refine ⟨_, sub_mem (nsmul_mem (hS _ (hfac (m + 1) (by omega)) _ (pow_mem e1 (m + 2))) w) h2, ?_⟩
  have hu : ((m + 1).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hl0 : ((m + 2 : ℕ) : C) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hf : ((m + 2).factorial : C) = ((m + 2 : ℕ) : C) * (m + 1).factorial := by
    rw [Nat.factorial_succ (m + 1)]; push_cast; ring
  rw [← Nat.cast_smul_eq_nsmul C, smul_sub, smul_add, smul_smul, smul_smul, smul_smul, hf]
  have k1 : ((m + 2 : ℕ) : C) * w * ((m + 1).factorial : C)⁻¹ =
      1 + ((m + 2 : ℕ) : C) * (((m + 2 : ℕ) : C) * (m + 1).factorial)⁻¹ := by
    rw [← hwC]; field_simp
  rw [k1, add_smul, one_smul]
  abel

end Alg

variable {C : Type} [Field C]

open scoped MvPowerSeries.WithPiTopology in
theorem ext_cont [UniformSpace C] [DiscreteUniformity C] {σ : Type} (L M : MvPowerSeries σ C → C)
    (hL : Continuous L) (hM : Continuous M) (aL : ∀ f g, L (f + g) = L f + L g) (aM : ∀ f g, M (f + g) = M f + M g)
    (h : ∀ e c, L (monomial e c) = M (monomial e c)) (f : MvPowerSeries σ C) : L f = M f := by
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries (σ := σ) (R := C)).equalizer hL hM (by
    funext p
    induction p using MvPolynomial.induction_on' with
    | monomial e c => simpa [MvPolynomial.coe_monomial] using h e c
    | add p q hp hq =>
      simp only [Function.comp] at hp hq ⊢
      rw [MvPolynomial.coe_add, aL, aM, hp, hq])
  exact congrFun this f

theorem split_bij {ρ κ β : Type} [Finite κ] [Finite β] {j0 : κ → ρ} {j1 : β → ρ}
    (hj : Function.Bijective (Sum.elim j0 j1)) :
    Function.Bijective fun p : (κ →₀ ℕ) × (β →₀ ℕ) => p.1.mapDomain j0 + p.2.mapDomain j1 := by
  have i0 : Function.Injective j0 := fun a b h => Sum.inl_injective (hj.1 (a₁ := Sum.inl a) (a₂ := Sum.inl b) h)
  have i1 : Function.Injective j1 := fun a b h => Sum.inr_injective (hj.1 (a₁ := Sum.inr a) (a₂ := Sum.inr b) h)
  have dj : ∀ a b, j0 a ≠ j1 b := fun a b h => Sum.inl_ne_inr (hj.1 (a₁ := Sum.inl a) (a₂ := Sum.inr b) h)
  have v0 : ∀ (ν : κ →₀ ℕ) (μ : β →₀ ℕ) a, (ν.mapDomain j0 + μ.mapDomain j1) (j0 a) = ν a := by
    intro ν μ a
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective i0, Finsupp.mapDomain_notin_range, add_zero]
    rintro ⟨b, hb⟩; exact dj a b hb.symm
  have v1 : ∀ (ν : κ →₀ ℕ) (μ : β →₀ ℕ) b, (ν.mapDomain j0 + μ.mapDomain j1) (j1 b) = μ b := by
    intro ν μ b
    rw [Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective i1, Finsupp.mapDomain_notin_range, zero_add]
    rintro ⟨a, ha⟩; exact dj a b ha
  constructor
  · rintro ⟨ν, μ⟩ ⟨ν', μ'⟩ h
    simp only at h
    ext a
    · rw [← v0 ν μ, ← v0 ν' μ', h]
    · rw [← v1 ν μ, ← v1 ν' μ', h]
  · intro e
    refine ⟨(Finsupp.equivFunOnFinite.symm fun a => e (j0 a), Finsupp.equivFunOnFinite.symm fun b => e (j1 b)), ?_⟩
    ext r
    obtain ⟨x, rfl⟩ := hj.2 r
    rcases x with a | b
    · exact v0 _ _ a
    · exact v1 _ _ b

def row {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (μ : β →₀ ℕ) (P : MvPowerSeries ρ C) : MvPowerSeries κ C :=
  fun ν => coeff (ν.mapDomain j0 + μ.mapDomain j1) P

theorem coeff_row {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (μ : β →₀ ℕ) (P : MvPowerSeries ρ C) (ν : κ →₀ ℕ) :
    coeff ν (row j0 j1 μ P) = coeff (ν.mapDomain j0 + μ.mapDomain j1) P := rfl

def slice {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (γ : κ → PowerSeries C) (n : ℕ) (P : MvPowerSeries ρ C) :
    MvPowerSeries β C :=
  fun μ => PowerSeries.coeff n (alongCv γ (row j0 j1 μ P))

theorem coeff_slice {ρ κ β : Type} (j0 : κ → ρ) (j1 : β → ρ) (γ : κ → PowerSeries C) (n : ℕ) (P : MvPowerSeries ρ C)
    (μ : β →₀ ℕ) : coeff μ (slice j0 j1 γ n P) = PowerSeries.coeff n (subst γ (row j0 j1 μ P)) := rfl

open scoped MvPowerSeries.WithPiTopology in
theorem jet_subst {ρ κ β τ : Type} [Finite ρ] [Finite κ] [Finite β] [Finite τ] {j0 : κ → ρ} {j1 : β → ρ}
    (hj : Function.Bijective (Sum.elim j0 j1)) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {a : β → MvPowerSeries τ C} (ha : ∀ b, constantCoeff (a b) = 0)
    {s : ρ → MvPowerSeries (Option τ) C} (hs : ∀ r, constantCoeff (s r) = 0)
    (s0 : ∀ i, s (j0 i) = CurveJet.inT τ (γ i)) (s1 : ∀ b, s (j1 b) = rename some (a b)) (n : ℕ)
    (P : MvPowerSeries ρ C) :
    PowerSeries.coeff n (optionEquivLeft τ C (subst s P)) = subst a (slice j0 j1 γ n P) := by
  classical
  letI : UniformSpace C := ⊥
  have Hs := hasSubst_of_constantCoeff_zero hs
  have Ha := hasSubst_of_constantCoeff_zero ha
  have Hγ : HasSubst γ := hasSubst_of_constantCoeff_zero hγ
  ext x
  refine ext_cont (fun P => coeff x (PowerSeries.coeff n (optionEquivLeft τ C (subst s P))))
    (fun P => coeff x (subst a (slice j0 j1 γ n P))) ?_ ?_ ?_ ?_ ?_ P
  · simp only [coeff_coeff_optionEquivLeft]
    exact (WithPiTopology.continuous_coeff C _).comp (continuous_subst Hs)
  · refine (WithPiTopology.continuous_coeff C _).comp ((continuous_subst Ha).comp ?_)
    refine continuous_pi fun μ => ?_
    refine (WithPiTopology.continuous_coeff C (Finsupp.single () n)).comp ((continuous_subst Hγ).comp ?_)
    exact continuous_pi fun ν => WithPiTopology.continuous_coeff C _
  · intro f g
    simp only [subst_add Hs, map_add (f := _)]
  · intro f g
    have : slice j0 j1 γ n (f + g) = slice j0 j1 γ n f + slice j0 j1 γ n g := by
      ext μ
      rw [map_add (f := _), coeff_slice, coeff_slice, coeff_slice, ← map_add (f := _), ← subst_add Hγ]
      rfl
    simp only [this, subst_add Ha, map_add (f := _)]
  · intro e c
    obtain ⟨⟨ν0, μ0⟩, rfl⟩ := (split_bij hj).2 e
    have hsl : slice j0 j1 γ n (monomial (ν0.mapDomain j0 + μ0.mapDomain j1) c) =
        monomial μ0 (c * PowerSeries.coeff n (ν0.prod fun i k => γ i ^ k)) := by
      ext μ
      rw [coeff_slice]
      by_cases hμ : μ = μ0
      · subst hμ
        have : row j0 j1 μ (monomial (ν0.mapDomain j0 + μ.mapDomain j1) c) = monomial ν0 c := by
          ext ν
          rw [coeff_row, coeff_monomial, coeff_monomial]
          refine if_congr ⟨fun h => ?_, fun h => by rw [h]⟩ rfl rfl
          exact congrArg Prod.fst ((split_bij hj).1 (a₁ := (ν, μ)) (a₂ := (ν0, μ)) h)
        rw [this, subst_monomial Hγ, coeff_monomial_same, ← Algebra.smul_def]
        rfl
      · have : row j0 j1 μ (monomial (ν0.mapDomain j0 + μ0.mapDomain j1) c) = 0 := by
          ext ν
          rw [coeff_row, coeff_monomial, if_neg, map_zero]
          exact fun h => hμ (congrArg Prod.snd ((split_bij hj).1 (a₁ := (ν, μ)) (a₂ := (ν0, μ0)) h))
        rw [this, ← coe_substAlgHom Hγ, map_zero, map_zero, coeff_monomial_ne hμ]
    simp only
    rw [hsl, subst_monomial Hs, subst_monomial Ha,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    have p0 : optionEquivLeft τ C (ν0.prod fun i k => s (j0 i) ^ k) =
        PowerSeries.map (MvPowerSeries.C : C →+* MvPowerSeries τ C) (ν0.prod fun i k => γ i ^ k) := by
      simp only [map_finsuppProd, map_pow, s0, CurveJet.optionEquivLeft_inT]
    have p1 : optionEquivLeft τ C (μ0.prod fun b k => s (j1 b) ^ k) =
        PowerSeries.C (μ0.prod fun b k => a b ^ k) := by
      simp only [map_finsuppProd, map_pow, s1, CurveJet.optionEquivLeft_rename_some]
    rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_mul, p0, p1, PowerSeries.coeff_smul,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_map, mul_smul, ← smul_eq_C_mul]

theorem coeff_one_subst {κ : Type} [Fintype κ] {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (f : MvPowerSeries κ C) :
    PowerSeries.coeff 1 (subst γ f : PowerSeries C) =
      ∑ i, PowerSeries.coeff 1 (γ i) * coeff (Finsupp.single i 1) f := by
  have e : ∀ g : PowerSeries C, PowerSeries.coeff 1 g = constantCoeff (pderiv (R := C) () g) := by
    intro g
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
    simp [PowerSeries.coeff]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, GlobalTheory.FormalCalc.pderiv_subst (a := γ) (hasSubst_of_constantCoeff_zero hγ), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, cc_subst (a := γ) hγ, e, mul_comm, ← coeff_zero_eq_constantCoeff_apply (pderiv (R := C) i f), coeff_pderiv]
  simp

theorem v_nat (V : VF C) {u : ℕ} (hu : ¬ V.l ∣ u) : V.v (u : C) = 0 := by
  refine PlaceProj.v_eq_zero_of_not_mm (VF.ge_natCast u) fun h => PlaceProj.not_mm_one (V := V) ?_
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (((Nat.Prime.coprime_iff_not_dvd V.l_prime).2 hu).symm) V.l_prime.one_lt
  have h1 : (1 : C) = (m : C) * u - (V.l : C) * ((u * m / V.l : ℕ) : C) := by
    have := congrArg (Nat.cast : ℕ → C) (Nat.mod_add_div (u * m) V.l)
    rw [hm] at this
    push_cast at this
    linear_combination this
  rw [h1]
  exact PlaceProj.mm_sub (PlaceProj.mm_mul (VF.ge_natCast m) h) (PlaceProj.mm_l_mul (VF.ge_natCast _))

theorem coeff_option_exp {σ : Type} {F : MvPowerSeries (Option σ) C} (hc : constantCoeff F = 0)
    (h0 : PowerSeries.constantCoeff (optionEquivLeft σ C F) = 0) (n : ℕ) :
    PowerSeries.coeff n (optionEquivLeft σ C (mvExp F)) =
      ∑ k ∈ Finset.range (n + 1), ((k.factorial : C))⁻¹ • PowerSeries.coeff n (optionEquivLeft σ C F ^ k) := by
  ext x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_coeff_optionEquivLeft, map_sum]
  show (∑ k ∈ Finset.range ((x.optionElim n).degree + 1), coeff (x.optionElim n) (F ^ k) / (k.factorial : C)) = _
  have hle : n ≤ (x.optionElim n).degree := by
    simpa using Finsupp.le_degree none (x.optionElim n)
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hle))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← map_pow, coeff_coeff_optionEquivLeft, smul_eq_mul, div_eq_inv_mul]
  · intro k _ hk
    have hk' : n < k := by simpa using hk
    rw [← coeff_coeff_optionEquivLeft, map_pow,
      PowerSeries.X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 h0) k) n hk', map_zero, zero_div]

variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem bij_two : Function.Bijective (Sum.elim (fun x : κ => ((0 : Fin 2), x)) (fun x : κ => ((1 : Fin 2), x))) := by
  constructor
  · rintro (a | a) (b | b) h <;> simp_all
  · rintro ⟨j, x⟩
    fin_cases j
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr x, rfl⟩

theorem bij_three : Function.Bijective
    (Sum.elim (fun x : κ => ((0 : Fin 3), x)) (fun p : Fin 2 × κ => (p.1.succ, p.2))) := by
  constructor
  · rintro (a | ⟨i, a⟩) (b | ⟨j, b⟩) h <;> simp_all [(Fin.succ_ne_zero _).symm]
  · rintro ⟨j, x⟩
    refine Fin.cases ⟨Sum.inl x, rfl⟩ (fun j => ⟨Sum.inr (j, x), rfl⟩) j

theorem jet_hAt {τ : Type} [Finite τ] {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    {a : κ → MvPowerSeries τ C} (ha : ∀ b, constantCoeff (a b) = 0) (n : ℕ) :
    PowerSeries.coeff n (optionEquivLeft τ C (hAt X (fun i => CurveJet.inT τ (γ i)) (fun i => rename some (a i)))) =
      subst a (hCoef X γ n) := by
  have e : hCoef X γ n = slice (fun x : κ => ((0 : Fin 2), x)) (fun x : κ => ((1 : Fin 2), x)) γ n X.h := by
    funext μ
    unfold hCoef slice row
    rfl
  rw [e]
  unfold hAt
  refine jet_subst bij_two hγ ha (fun p => ?_) (fun _ => if_pos rfl) (fun _ => if_neg (by simp)) n X.h
  split_ifs
  · exact CurveJet.constantCoeff_inT τ (hγ _)
  · rw [constantCoeff_rename, ha]

theorem hCoef_zero (H : RLaw X V) {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) :
    hCoef X γ 0 = 0 := by
  ext μ
  show PowerSeries.coeff 0 (subst γ (row (fun x : κ => ((0 : Fin 2), x)) (fun x : κ => ((1 : Fin 2), x)) μ X.h)) = 0
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  refine (cc_subst (a := γ) hγ _).trans ?_
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_row]
  refine H.axes 0 _ fun s hs => ?_
  rw [Finsupp.mapDomain_zero, zero_add] at hs
  classical
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hs)
  simp

theorem cob_smul (H : RLaw X V) (c : C) (b : MvPowerSeries κ C) : cob X (c • b) = c • cob X b := by
  unfold cob
  rw [subst_smul (hasSubst_of_constantCoeff_zero (formalAdd_constantCoeff H (gp_cc 0) (gp_cc 1))),
    subst_smul (hasSubst_of_constantCoeff_zero (gp_cc 0)), subst_smul (hasSubst_of_constantCoeff_zero (gp_cc 1)),
    smul_sub, smul_sub]

theorem exists_series [CharZero C] (H : RLaw X V) {γ : κ → PowerSeries C} (hγ : IsCv V γ) :
    ∃ F : MvPowerSeries (Option (Fin 2 × κ)) C, constantCoeff F = 0 ∧ IntS V (mvExp F) ∧
      (∀ n, PowerSeries.coeff n (optionEquivLeft _ C F) = - cob X (hCoef X γ n)) ∧
      PowerSeries.coeff 1 (optionEquivLeft _ C F) = c2 X fun i => PowerSeries.coeff 1 (γ i) := by
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  let P : Fin 3 → κ → MvPowerSeries (Option (Fin 2 × κ)) C :=
    Fin.cons (fun i => CurveJet.inT _ (γ i)) (fun j i => rename some (gp C κ j i))
  have hP : ∀ j s, constantCoeff (P j s) = 0 := by
    intro j s
    refine Fin.cases (CurveJet.constantCoeff_inT _ (hγ0 s)) (fun j => ?_) j
    show constantCoeff (rename some (gp C κ j s)) = 0
    rw [constantCoeff_rename, gp_cc]
  have hI : ∀ j s, IntS V (P j s) := by
    intro j s
    refine Fin.cases ?_ (fun j => ?_) j
    · exact intS_subst (fun _ => constantCoeff_X _) (fun _ => intS_X _)
        (GlobalTheory.RowLaw.AddCurve.intS_iff.2 (hγ s).2)
    · show IntS V (rename some (MvPowerSeries.X (j, s)))
      rw [rename_X]; exact intS_X _
  have hb : ∀ p : Fin 3 × κ, constantCoeff (P p.1 p.2) = 0 := fun p => hP p.1 p.2
  have hs := hasSubst_of_constantCoeff_zero hb
  have hadd := formalAdd_constantCoeff H (gp_cc (C := C) (κ := κ) (1 : Fin 3)) (gp_cc 2)
  have hΦ : constantCoeff (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1) + hAt X (gp C κ 0) (gp C κ 2) -
      hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2))) = 0 := by
    rw [map_sub, map_add (f := _), hAt_cc H (gp_cc 0) (gp_cc 1), hAt_cc H (gp_cc 0) (gp_cc 2), hAt_cc H (gp_cc 0) hadd]
    simp
  have h := logInt_subst hb (fun p => hI p.1 p.2) (mem_logInt.2 ⟨hΦ, H.ph2⟩)
  refine ⟨_, h.1, h.2, fun n => ?_, ?_⟩
  · have ea : (fun s => subst (fun p : Fin 3 × κ => P p.1 p.2) (addP X (gp C κ 1) (gp C κ 2) s)) =
        fun s => rename some (addP X (gp C κ (0 : Fin 2)) (gp C κ 1) s) := by
      funext s
      rw [subst_addP H (gp_cc 1) (gp_cc 2) hb, subst_gp hP, subst_gp hP, rename_eq_subst,
        subst_addP (b := MvPowerSeries.X ∘ some) H (gp_cc 0) (gp_cc 1) (fun _ => constantCoeff_X _)]
      simp only [← rename_eq_subst]
      rfl
    rw [subst_sub hs, subst_add hs, subst_hAt (gp_cc 0) (gp_cc 1) hb, subst_hAt (gp_cc 0) (gp_cc 2) hb,
      subst_hAt (gp_cc 0) hadd hb, ea, subst_gp hP, subst_gp hP, subst_gp hP, map_sub, map_add, map_sub, map_add]
    have e0 := jet_hAt (X := X) hγ0 (gp_cc (C := C) (κ := κ) (0 : Fin 2)) n
    have e1 := jet_hAt (X := X) hγ0 (gp_cc (C := C) (κ := κ) (1 : Fin 2)) n
    have e2 := jet_hAt (X := X) hγ0 (formalAdd_constantCoeff H (gp_cc (C := C) (κ := κ) (0 : Fin 2)) (gp_cc 1)) n
    unfold cob
    rw [← e0, ← e1, ← e2, sub_sub, neg_sub]
    rfl
  · rw [jet_subst bij_three hγ0 (a := MvPowerSeries.X) (fun _ => constantCoeff_X _) hb (fun _ => rfl) (fun _ => rfl),
      subst_self, id]
    ext μ
    rw [coeff_slice, coeff_one_subst hγ0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_row, Finsupp.mapDomain_single, add_comm]

theorem cocycle_pow_coboundary : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V (c2 X fun i => PowerSeries.coeff 1 (γ i)) ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ ((c2 X fun i => PowerSeries.coeff 1 (γ i)) ^ V.l + cob X ((V.l : C) • hCoef X γ V.l))) := by
  intro C _ V d _ I _ κ _ X H γ hγ _
  haveI := H.charZero
  obtain ⟨F, hc, hF, he, h1⟩ := exists_series H hγ
  have h0 : PowerSeries.constantCoeff (optionEquivLeft _ C F) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he, hCoef_zero H fun i => (hγ i).1,
      ← zero_smul C (0 : MvPowerSeries κ C), cob_smul H, zero_smul, neg_zero]
  obtain ⟨a, s, hs, e⟩ := exp_low (C := C) (Ig (GaugeCocycle.valRing V) C (Fin 2 × κ)) V.l_prime (by
    intro u hu x hx
    rw [← GaugeCocycle.intS_iff_ig] at hx ⊢
    intro μ
    have hu0 : (u : C) ≠ 0 := by
      rw [Nat.cast_ne_zero]; rintro rfl; exact hu (dvd_zero _)
    refine PlaceProj.ge_of_unit_mul (v_nat V hu) ?_
    rw [map_smul, smul_eq_mul, mul_inv_cancel_left₀ hu0]
    exact hx μ) _ h0 (by
    intro n
    rw [← coeff_option_exp hc h0, ← GaugeCocycle.intS_iff_ig]
    intro μ
    rw [coeff_coeff_optionEquivLeft]
    exact hF _)
  rw [h1] at a e
  rw [he, smul_neg, sub_neg_eq_add, ← cob_smul H] at e
  refine ⟨(GaugeCocycle.intS_iff_ig V _).2 a, fun μ => ?_⟩
  rw [e, map_smul, smul_eq_mul]
  exact PlaceProj.mm_l_mul ((GaugeCocycle.intS_iff_ig V _).2 hs μ)

end GlobalTheory.CocyclePow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupCocycleLthPowerCoboundaryModMaximalStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupCocycle_lthPower_coboundary_mod_maximal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ γ : κ → PowerSeries C, IsCv V γ → (∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0) → IntS V (c2 X fun i => PowerSeries.coeff 1 (γ i)) ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ ((c2 X fun i => PowerSeries.coeff 1 (γ i)) ^ V.l + cob X ((V.l : C) • hCoef X γ V.l))) := by
  first | exact @GlobalTheory.CocyclePow.cocycle_pow_coboundary | exact GlobalTheory.CocyclePow.cocycle_pow_coboundary | (intros; apply GlobalTheory.CocyclePow.cocycle_pow_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerate
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

noncomputable section

namespace GlobalTheory.RowAt.GoodInj

open GlobalTheory.RowLaw.CvEnd
open GlobalTheory.PlaceProj hiding mm_add mm_zero

variable {C : Type} [Field C] {V : VF C}

theorem mm_sum' {ι : Type} (s : Finset ι) (f : ι → C) (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f V.MM (fun _ _ => mm_add) mm_zero h

def ordIdeal (C : Type) [Field C] {τ : Type} (w : τ → ℕ) (n : ℕ) : Ideal (MvPowerSeries τ C) where
  carrier := {F | F ∈ ordGe C w n}
  add_mem' := fun ha hb => (ordGe C w n).add_mem ha hb
  zero_mem' := (ordGe C w n).zero_mem
  smul_mem' := fun c a ha => by
    have := ordGe_mul (ordGe_zero (w := w) c) ha
    rwa [zero_add] at this

theorem mem_ordIdeal {τ : Type} {w : τ → ℕ} {n : ℕ} {F : MvPowerSeries τ C} : F ∈ ordIdeal C w n ↔ F ∈ ordGe C w n :=
  Iff.rfl

theorem subst_congr_ord {σ τ : Type} {w : τ → ℕ} {n : ℕ} {a b : σ → MvPowerSeries τ C}
    (ha : MvPowerSeries.HasSubst a) (hb : MvPowerSeries.HasSubst b) (h : ∀ s, a s - b s ∈ ordGe C w n)
    (f : MvPowerSeries σ C) : MvPowerSeries.subst a f - MvPowerSeries.subst b f ∈ ordGe C w n := by
  intro e he
  rw [map_sub, MvPowerSeries.coeff_subst ha, MvPowerSeries.coeff_subst hb, sub_eq_zero]
  refine finsum_congr fun μ => ?_
  congr 1
  have h1 : (μ.prod fun s k => a s ^ k) - (μ.prod fun s k => b s ^ k) ∈ ordIdeal C w n := by
    rw [← Ideal.Quotient.eq]
    unfold Finsupp.prod
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, map_pow, Ideal.Quotient.eq.2 (mem_ordIdeal.2 (h s))]
  have h2 := mem_ordIdeal.1 h1 e he
  rwa [map_sub, sub_eq_zero] at h2

theorem mm_subst {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : MvPowerSeries.HasSubst a) (hi : ∀ s, IntS V (a s))
    {F : MvPowerSeries σ C} (hF : ∀ μ, V.MM (MvPowerSeries.coeff μ F)) (e : τ →₀ ℕ) :
    V.MM (MvPowerSeries.coeff e (MvPowerSeries.subst a F)) := by
  rw [MvPowerSeries.coeff_subst ha]
  refine finsum_induction (fun x => V.MM x) mm_zero (fun _ _ => mm_add) fun μ => ?_
  rw [smul_eq_mul, mul_comm]
  refine mm_mul ?_ (hF μ)
  revert e
  show IntS V _
  refine Finset.prod_induction _ (IntS V) (fun _ _ => intS_mul) intS_one fun s _ => ?_
  show IntS V (a s ^ μ s)
  induction μ s with
  | zero => rw [pow_zero]; exact intS_one
  | succ k ih => rw [pow_succ]; exact intS_mul ih (hi s)

theorem intS_X' {τ : Type} (s : τ) : IntS V (MvPowerSeries.X s : MvPowerSeries τ C) := by
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intS_add' {τ : Type} {F G : MvPowerSeries τ C} (hF : IntS V F) (hG : IntS V G) : IntS V (F + G) := fun e => by
  rw [map_add (f := _)]; exact (hF e).add (hG e)

theorem intS_sub' {τ : Type} {F G : MvPowerSeries τ C} (hF : IntS V F) (hG : IntS V G) : IntS V (F - G) := fun e => by
  rw [map_sub]; exact (hF e).sub (hG e)

theorem intS_neg' {τ : Type} {F : MvPowerSeries τ C} (hF : IntS V F) : IntS V (-F) := fun e => by
  rw [map_neg]; exact (hF e).neg

section Chart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

theorem formalAdd_const (H : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (i : κ) :
    MvPowerSeries.constantCoeff (addP Y a b i) = 0 :=
  constantCoeff_subst_zero (fun x => by
    rw [map_add (f := _), constantCoeff_subst_zero ha (lg_const H x), constantCoeff_subst_zero hb (lg_const H x), add_zero])
    (H.exc i)

theorem cob_root (H : RLaw Y V) {c : MvPowerSeries (Fin 2 × κ) C} (hc : IntS V c) {b : MvPowerSeries κ C}
    (hb : IntS V b) (hd : ∀ i μ, V.MM (MvPowerSeries.coeff μ (MvPowerSeries.pderiv (R := C) i b)))
    (h : ∀ μ, V.MM (MvPowerSeries.coeff μ (c ^ V.l + cob Y b))) :
    ∃ b' : MvPowerSeries κ C, IntS V b' ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (c - cob Y b')) := by
  haveI := H.closed
  obtain ⟨b', hb', hbb⟩ := (GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal C V κ).1 b hb hd
  obtain ⟨-, hroot, hfr⟩ := GlobalTheory.T.mvPowerSeries_lthPower_of_pderiv_vanish_mod_maximal C V (Fin 2 × κ)
  have s0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (gp_const (C := C) (κ := κ) (0 : Fin 2))
  have s1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (gp_const (C := C) (κ := κ) (1 : Fin 2))
  have sa := MvPowerSeries.hasSubst_of_constantCoeff_zero
    (formalAdd_const H (gp_const (C := C) (κ := κ) (0 : Fin 2)) (gp_const (1 : Fin 2)))
  have i0 : ∀ s, IntS V (gp C κ (0 : Fin 2) s) := fun s => intS_X' _
  have i1 : ∀ s, IntS V (gp C κ (1 : Fin 2) s) := fun s => intS_X' _
  have hA := intS_subst sa H.addInt hb'
  have hB := intS_subst s0 i0 hb'
  have hD := intS_subst s1 i1 hb'
  have mA := mm_subst sa H.addInt hbb
  have mB := mm_subst s0 i0 hbb
  have mD := mm_subst s1 i1 hbb
  rw [MvPowerSeries.subst_sub sa, MvPowerSeries.subst_pow sa] at mA
  rw [MvPowerSeries.subst_sub s0, MvPowerSeries.subst_pow s0] at mB
  rw [MvPowerSeries.subst_sub s1, MvPowerSeries.subst_pow s1] at mD
  have e : cob Y (-b') = MvPowerSeries.subst (gp C κ (0 : Fin 2)) b' + MvPowerSeries.subst (gp C κ (1 : Fin 2)) b' -
      MvPowerSeries.subst (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1)) b' := by
    unfold cob
    rw [← MvPowerSeries.coe_substAlgHom sa, ← MvPowerSeries.coe_substAlgHom s0, ← MvPowerSeries.coe_substAlgHom s1,
      map_neg, map_neg, map_neg]
    ring
  refine ⟨-b', intS_neg' hb', ?_⟩
  rw [e]
  refine hroot _ _ hc (intS_sub' (intS_add' hB hD) hA) fun μ => ?_
  have k1 := (hfr _ _ (intS_add' hB hD) hA μ).2
  have k2 := (hfr _ _ hB hD μ).1
  have := mm_add (mm_add (mm_sub (mm_sub (mm_sub (h μ) k1) k2) (mA μ)) (mB μ)) (mD μ)
  convert this using 1
  simp only [cob, map_sub, map_add (f := _)]
  ring

theorem ex_along (H : RLaw Y V) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : κ) :
    MvPowerSeries.subst (fun x => MvPowerSeries.subst a (Y.lg x)) (Y.ex i) = a i := by
  have hA := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have := MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (lg_const H)) hA (Y.ex i)
  rw [H.exlg, MvPowerSeries.subst_X hA] at this
  exact this.symm

theorem cvAt_const {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {f : PowerSeries C}
    (hf : PowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (cvAt s f) = 0 :=
  constantCoeff_subst_zero (σ := Unit) (fun _ => hs) hf

theorem subst_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (f : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun j => cvAt s (γ j)) f = cvAt s (alongCv γ f) :=
  (MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (τ := Unit) hγ)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs) f).symm

theorem cvAt_lin {N : ℕ} {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {f : PowerSeries C}
    (hf : PowerSeries.constantCoeff f = 0) (h : ∀ n, 2 ≤ n → n < N → PowerSeries.coeff n f = 0) :
    cvAt s f - PowerSeries.coeff 1 f • s ∈ ordGe C (fun _ => 1) N := by
  have hS : MvPowerSeries.HasSubst (fun _ : Unit => s) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs
  have h1 : (f - PowerSeries.coeff 1 f • PowerSeries.X : MvPowerSeries Unit C) ∈ ordGe C (fun _ => 1) N := by
    intro e he
    have h2 : e = Finsupp.single () (e ()) := Finsupp.unique_single e
    rw [h2, Finsupp.weight_single, smul_eq_mul, mul_one] at he
    rw [h2]
    show PowerSeries.coeff (e ()) (f - PowerSeries.coeff 1 f • PowerSeries.X) = 0
    rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_X]
    rcases Nat.lt_trichotomy (e ()) 1 with h3 | h3 | h3
    · have : e () = 0 := by omega
      rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]; simp
    · rw [h3]; simp
    · rw [h _ h3 he, if_neg (by omega)]; simp
  have := ordGe_subst hS (fun _ => ordGe_one_of_const hs) h1
  rw [MvPowerSeries.subst_sub hS, MvPowerSeries.subst_smul hS] at this
  rwa [show MvPowerSeries.subst (fun _ : Unit => s) (PowerSeries.X : PowerSeries C) = s from
    MvPowerSeries.subst_X hS ()] at this

theorem additive_low (H : RLaw Y V) {N : ℕ} {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (h : ∀ i n, 2 ≤ n → n < N → PowerSeries.coeff n (alongCv γ (Y.lg i)) = 0) (i : κ) :
    addP Y (fun j => cvAt (MvPowerSeries.X 0) (γ j)) (fun j => cvAt (MvPowerSeries.X 1) (γ j)) i -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i) ∈ ordGe C (fun _ => 1) N := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) C) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have cs : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 := by
    rw [map_add (f := _), c0, c1, add_zero]
  have hL : ∀ x, PowerSeries.constantCoeff (alongCv γ (Y.lg x)) = 0 := fun x =>
    constantCoeff_subst_zero (τ := Unit) hγ (lg_const H x)
  rw [← ex_along H (a := fun j => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j))
    (fun j => cvAt_const cs (hγ j)) i]
  unfold RowLaw.addP
  simp only [subst_cvAt c0 hγ, subst_cvAt c1 hγ, subst_cvAt cs hγ]
  refine subst_congr_ord (MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => ?_)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => cvAt_const cs (hL x)) (fun x => ?_) _
  · rw [map_add (f := _), cvAt_const c0 (hL x), cvAt_const c1 (hL x), add_zero]
  · have := Submodule.sub_mem _ (Submodule.add_mem _ (cvAt_lin c0 (hL x) (h x)) (cvAt_lin c1 (hL x) (h x)))
      (cvAt_lin cs (hL x) (h x))
    convert this using 1
    rw [smul_add]
    ring

theorem end_entry_int (H : RLaw Y V) {M : Matrix κ κ C}
    (hM : ∀ i, IntS V (endP Y M (MvPowerSeries.X : κ → MvPowerSeries κ C) i)) (i j : κ) : V.Ge 0 (M i j) := by
  have h := matrixEnd_two (w := fun _ => 1) H M (b := (MvPowerSeries.X : κ → MvPowerSeries κ C))
    (fun i => MvPowerSeries.constantCoeff_X i) (fun i => ordGe_X (w := fun _ => 1) i) i (Finsupp.single j 1)
    (by simp [Finsupp.weight_single])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_eq_zero, map_sum] at h
  have h2 := hM i (Finsupp.single j 1)
  rw [h] at h2
  simpa [MvPowerSeries.coeff_X, Finsupp.single_left_inj] using h2

theorem sg_sum (Y : RawChart C d I κ) {ι : Type} [Fintype ι] (b : ι → C) (v : ι → κ → C) :
    Y.sg (∑ c, b c • v c) = ∑ c, b c • Y.sg (v c) := by
  simp only [sg_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, smul_neg, Finset.smul_sum,
    smul_smul, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

theorem coord_of_sat {g : Fin 2} {ww : κ → I g → C}
    (hw : ∀ c c' : I g, (c = c' → ∑ x, Y.u g c x * ww x c' = 1) ∧ (c ≠ c' → ∑ x, Y.u g c x * ww x c' = 0))
    (b : I g → C) (c' : I g) : ∑ x, (∑ c, b c * Y.u g c x) * ww x c' = b c' := by
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single c']
  · rw [(hw c' c').1 rfl, mul_one]
  · intro c _ hc
    rw [(hw c c').2 hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sg_all (H : RLaw Y V) (hP : HasProj Y V) {g : Fin 2} {γ : κ → PowerSeries C} (hγ : IsCv V γ)
    {A : I g → PowerSeries C} (hA : ∀ i, alongCv γ (Y.lg i) = ∑ c, Y.u g c i • A c)
    (h : ∀ q : I (1 - g), V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (Y.sg (Y.u (1 - g) q)))))
    (v : κ → C) (hv : ∀ i, V.Ge 0 (v i)) : V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (Y.sg v))) := by
  obtain ⟨M, h01, h10, hfix, -, hspan⟩ := hP
  have hE : IsEnd Y V (M g) (M (1 - g)) := by
    fin_cases g
    · exact h01
    · exact h10
  have hX : ∀ i : κ, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries κ C) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i : MvPowerSeries Unit C) = 0 := fun i => (hγ i).1
  have hΓ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (matrixEnd_const H (M g) hX)
  have hsg := Y.constantCoeff_sg (H.axes 0)
  have hK := (isCv_along hγ (f := fun _ : Unit =>
      MvPowerSeries.subst (endP Y (M g) (MvPowerSeries.X : κ → MvPowerSeries κ C)) (Y.sg v) -
        Y.sg ((M (1 - g)).mulVec v))
    (fun q => by rw [map_sub, constantCoeff_subst_zero (matrixEnd_const H (M g) hX) (hsg _), hsg, sub_self])
    (fun q => defect_int H hE hv) ()).2 V.l
  have hfixγ : ∀ i, endP Y (M g) (τ := Unit) γ i = γ i := by
    intro i
    rw [← ex_along H hγ0 i]
    unfold endP
    congr 1
    funext x
    have hA' : ∀ i, MvPowerSeries.subst γ (Y.lg i) = ∑ c, Y.u g c i • (A c : MvPowerSeries Unit C) := hA
    simp only [hA', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    exact congrFun (hfix g c) x
  obtain ⟨b, hb⟩ := hspan (1 - g) v
  obtain ⟨ww, hwi, hw⟩ := H.sat (1 - g)
  have hbi : ∀ c, V.Ge 0 (b c) := by
    intro c
    rw [← coord_of_sat hw b c]
    refine VF.Ge.sum fun x _ => VF.Ge.mul_int ?_ (hwi x c)
    have := congrFun hb x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    exact VF.Ge.sum fun y _ => (end_entry_int H hE.2.1 x y).mul_int (hv y)
  have e : alongCv γ (MvPowerSeries.subst (endP Y (M g) (MvPowerSeries.X : κ → MvPowerSeries κ C)) (Y.sg v) -
        Y.sg ((M (1 - g)).mulVec v)) =
      alongCv γ (Y.sg v) - ∑ c, b c • alongCv γ (Y.sg (Y.u (1 - g) c)) := by
    unfold alongCv
    rw [MvPowerSeries.subst_sub hΓ, MvPowerSeries.subst_comp_subst_apply hS hΓ, hb, sg_sum, subst_sum_smul hΓ]
    simp only [subst_endP H (M g) hγ0, hfixγ]
  beta_reduce at hK
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sub, map_sum] at hK
  have := mm_add (mm_l_mul hK) (mm_sum' Finset.univ _ fun c _ => mm_mul (hbi c) (h c))
  convert this using 1
  simp only [PowerSeries.coeff_smul, smul_eq_mul, mul_sub, Finset.mul_sum]
  rw [sub_add, ← Finset.sum_sub_distrib, Finset.sum_eq_zero, sub_zero]
  intro c _
  ring

end Chart

theorem tangent_mm_of_nonDeg : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → NonDeg X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H := by
  intro C _ V d _ I _ κ _ Y H hP hN Hc _ g a _ w x hx hc0
  obtain ⟨⟨hT, hx0, -⟩, hx1⟩ := hx
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ : x ∈ Y.TySet V g := hT
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have tl : ∀ s : ℕ → C, PowerSeries.coeff V.l (tyS V.l s) = s 1 := fun s => by
    simpa using coeff_tyS_pow hl s 1
  have t1 : ∀ s : ℕ → C, PowerSeries.coeff 1 (tyS V.l s) = s 0 := fun s => by
    simpa using coeff_tyS_pow hl s 0
  have hlow : ∀ i n, 2 ≤ n → n < V.l ^ 2 → PowerSeries.coeff n (alongCv γ (Y.lg i)) = 0 := by
    intro i n hn hn'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [PowerSeries.coeff_smul]
    by_cases hs : ∃ s, V.l ^ s = n
    · obtain ⟨s, rfl⟩ := hs
      have hs2 : s < 2 := (Nat.pow_lt_pow_iff_right (by omega)).1 hn'
      have hs0 : s ≠ 0 := by
        rintro rfl
        simp at hn
      have : s = 1 := by omega
      rw [coeff_tyS_pow hl, this, hx1 c, smul_zero]
    · push Not at hs
      rw [coeff_tyS_of_ne _ _ hs, smul_zero]
  have hq : ∀ q : I (1 - g), V.MM ((V.l : C) * PowerSeries.coeff V.l (alongCv γ (Y.sg (Y.u (1 - g) q)))) := by
    intro q
    have e := congrArg (PowerSeries.coeff V.l) (h2 q)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [tl, map_add (f := _), map_sub, map_sum, Finset.sum_eq_zero, add_zero] at e
    · have := mm_sub (mm_l_mul ((hlam q).2 V.l)) (hc0 q)
      convert this using 1
      unfold Cart.c0'
      rw [e]
      ring
    · intro c _
      split_ifs
      · rw [PowerSeries.coeff_smul, tl, hx1 c, smul_zero]
      · exact map_zero _
  obtain ⟨hbi, hbd⟩ := GlobalTheory.T.integral_smul_curveCoeffSeriesOfChartH_of_linear_log C V d I κ Y H γ hγ hlow
  obtain ⟨hci, hcb⟩ := GlobalTheory.T.formalGroupCocycle_lthPower_coboundary_mod_maximal C V d I κ Y H γ hγ hlow
  have hcob := cob_root H hci hbi (hbd (sg_all H hP hγ h1 hq)) hcb
  have htan : ∀ i, V.MM (PowerSeries.coeff 1 (γ i)) := by
    by_contra hne
    push Not at hne
    refine hN γ hγ hne (fun i μ hμ0 hμ1 => ?_) hcob
    rw [additive_low H hγ0 hlow i μ]
    · exact mm_zero
    · rw [weight_one, Finsupp.degree_eq_sum, Fin.sum_univ_two]
      nlinarith
  have hco : ∀ i, PowerSeries.coeff 1 (γ i) = ∑ c, w c * Y.u g c i := by
    intro i
    have := lg_two (τ := Unit) (w := fun _ => 1) H (b := γ) hγ0 (fun i => ordGe_one_of_const (hγ0 i)) i
      (Finsupp.single () 1) (by simp [Finsupp.weight_single])
    have e : PowerSeries.coeff 1 (alongCv γ (Y.lg i) - γ i) = 0 := this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, h1, map_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [PowerSeries.coeff_smul, t1, hx0, smul_eq_mul, mul_comm]
    rfl
  obtain ⟨ww, hwi, hw⟩ := H.sat g
  intro c
  rw [← coord_of_sat hw w c]
  refine mm_sum' _ _ fun i _ => ?_
  rw [← hco, mul_comm]
  exact mm_mul (hwi i c) (htan i)

end GlobalTheory.RowAt.GoodInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RawChartTangentMaximalIdealOfNonDegenerateStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → NonDeg X V → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H := by
  first | exact @GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | exact GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg | (intros; apply GlobalTheory.RowAt.GoodInj.tangent_mm_of_nonDeg <;> assumption)
end
