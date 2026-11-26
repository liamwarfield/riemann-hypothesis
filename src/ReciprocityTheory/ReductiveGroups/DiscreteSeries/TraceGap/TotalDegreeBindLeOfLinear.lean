module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DiracSquareMemLayer
noncomputable section

open MvPolynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

def entVar (g : Matrix (Fin n) (Fin n) ℂ) : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

abbrev EntIdx (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

theorem totalDegree_bind_le_of_linear {ι : Type*} (f : ι → MvPolynomial ι ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (Q : MvPolynomial ι ℂ) : (bind₁ f Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (m i) (hf i)

def trF (g : Matrix (Fin n) (Fin n) ℂ) : EntIdx n → MvPolynomial (EntIdx n) ℂ :=
  Sum.elim (fun x => ∑ l, C (g x.1 l) * X (Sum.inl (l, x.2)))
    (fun x => ∑ l, C (star (g x.1 l)) * X (Sum.inr (l, x.2)))

theorem trF_totalDegree (g : Matrix (Fin n) (Fin n) ℂ) (i : EntIdx n) : (trF g i).totalDegree ≤ 1 := by
  classical
  rcases i with x | x <;>
  · simp only [trF, Sum.elim_inl, Sum.elim_inr]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]

theorem eval_trF (g h : Matrix (Fin n) (Fin n) ℂ) (i : EntIdx n) :
    eval (entVar h) (trF g i) = entVar (g * h) i := by
  rcases i with x | x
  · simp [trF, entVar, Matrix.mul_apply]
  · simp [trF, entVar, Matrix.mul_apply, star_sum]

theorem eval_mul_eq_bind₁ (g h : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (EntIdx n) ℂ) :
    eval (entVar (g * h)) P = eval (entVar h) (bind₁ (trF g) P) := by
  have := eval₂Hom_bind₁ (RingHom.id ℂ) (entVar h) (trF g) P
  simp only [coe_eval₂Hom] at this
  rw [show eval (entVar h) (bind₁ (trF g) P) = eval₂ (RingHom.id ℂ) (entVar h) (bind₁ (trF g) P) from rfl, this]
  show eval₂ (RingHom.id ℂ) _ P = eval₂ (RingHom.id ℂ) _ P
  congr 1
  funext i
  exact (eval_trF g h i).symm

def wtM (m : EntIdx n →₀ ℕ) : Fin n → ℝ := fun a =>
  ∑ j, (((m (Sum.inr (a, j)) : ℕ) : ℝ) - ((m (Sum.inl (a, j)) : ℕ) : ℝ))

def dTor (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem eval_monomial_tor (θ : Fin n → ℝ) (h : Matrix (Fin n) (Fin n) ℂ) (m : EntIdx n →₀ ℕ) :
    eval (entVar (star (dTor θ) * h)) (monomial m 1) =
      Complex.exp (((∑ a, wtM m a * θ a : ℝ) : ℂ) * Complex.I) * eval (entVar h) (monomial m 1) := by
  classical
  set s : EntIdx n → ℝ := Sum.elim (fun x => -θ x.1) (fun x => θ x.1) with hs
  have hst : ∀ t : ℝ, star (Complex.exp ((t : ℂ) * Complex.I)) = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [← starRingEnd_apply, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
  have hent : ∀ i, entVar (star (dTor θ) * h) i = Complex.exp ((s i : ℂ) * Complex.I) * entVar h i := by
    intro i
    rcases i with x | x
    · simp only [entVar, Sum.elim_inl, hs, dTor, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Pi.star_apply]
      rw [hst]
    · simp only [entVar, Sum.elim_inr, hs, dTor, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul, Pi.star_apply, star_mul', star_star]
  simp only [eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [hent, mul_pow, Finset.prod_mul_distrib]
  congr 1
  simp only [← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [wtM, hs, Sum.elim_inl, Sum.elim_inr]
  push_cast
  rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

noncomputable section

open MeasureTheory MvPolynomial

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

theorem finite_monomials_of_degree_le (d : ℕ) : {m : EntIdx n →₀ ℕ | (m.sum fun _ e => e) ≤ d}.Finite := by
  have h1 : {f : EntIdx n →₀ ℕ | ∀ a, f a ≤ d}.Finite :=
    (Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn
  exact h1.subset fun m hm i ↦ (eq_or_ne (m i) 0).elim
    (fun h ↦ h.trans_le d.zero_le) fun h ↦
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) <| Finsupp.mem_support_iff.mpr h).trans hm

theorem range_one_layer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
    (hstd : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hdense : closGen E V = ⊤)
    {Kg : Type*} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μK : Measure Kg) [IsFiniteMeasure μK] [μK.IsMulLeftInvariant]
    (φ : Kg → Matrix (Fin n) (Fin n) ℂ) (hφc : Continuous φ) (hφ1 : φ 1 = 1)
    (hφm : ∀ a b, φ (a * b) = φ a * φ b) (hφK : ∀ g, φ g ∈ Kset ε) (hφs : ∀ m ∈ Kset ε, ∃ g, φ g = m)
    (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    ∃ j : ℕ, ∀ u : H,
      ∫ k, MvPolynomial.eval (entVar (φ k)) P • σ (φ k) u ∂μK ∈ (layer ε E V j).map D.subtype := by
  classical
  have hE := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hinUJ : ∀ g, φ g ∈ UJset ε := fun g => smd_inUJ_of_Kset (hφK g)
  have horb : ∀ u : H, Continuous fun k => σ (φ k) u := fun u => (hσ.2.2 u).comp_continuous hφc hinUJ
  have hentc : Continuous fun k => entVar (φ k) := by
    refine continuous_pi fun i => ?_
    rcases i with x | x
    · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
  have hpolyc : ∀ Q : MvPolynomial (EntIdx n) ℂ, Continuous fun k => eval (entVar (φ k)) Q :=
    fun Q => (MvPolynomial.continuous_eval Q).comp hentc
  have hint : ∀ (Q : MvPolynomial (EntIdx n) ℂ) (u : H),
      Integrable (fun k => eval (entVar (φ k)) Q • σ (φ k) u) μK := fun Q u =>
    ((hpolyc Q).smul (horb u)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Xu : H → MvPolynomial (EntIdx n) ℂ →ₗ[ℂ] H := fun u =>
    { toFun := fun Q => ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂μK
      map_add' := fun Q R => by
        simp only [map_add (f := _), add_smul]
        exact integral_add (hint Q u) (hint R u)
      map_smul' := fun c Q => by
        simp only [smul_eval, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have hXu : ∀ u Q, Xu u Q = ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂μK := fun _ _ => rfl
  have htr : ∀ u Q g, σ (φ g) (Xu u Q) = Xu u (bind₁ (trF (φ g⁻¹)) Q) := by
    intro u Q g
    rw [hXu, hXu, ← (σ (φ g)).integral_comp_comm (hint Q u)]
    have e2 : ∫ k, σ (φ g) (eval (entVar (φ k)) Q • σ (φ k) u) ∂μK =
        ∫ k, eval (entVar (φ (g⁻¹ * (g * k)))) Q • σ (φ (g * k)) u ∂μK := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_smul, inv_mul_cancel_left]
      rw [hφm g k, hσ.1.2 _ (hinUJ g) _ (hinUJ k)]
      rfl
    rw [e2, integral_mul_left_eq_self (fun k => eval (entVar (φ (g⁻¹ * k))) Q • σ (φ k) u) g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hφm, eval_mul_eq_bind₁]

  have hmono : ∀ (u : H) (m : EntIdx n →₀ ℕ),
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (wtM m) (Xu u (monomial m 1)) := by
    intro u m θ hθ
    rw [mir_Kset_eq] at hθ
    obtain ⟨g, hg⟩ := hφs _ hθ
    have hginv : φ g⁻¹ = star (φ g) := by
      have h1 : φ g * star (φ g) = 1 := Unitary.mul_star_self_of_mem (hφK g).1
      calc φ g⁻¹ = φ g⁻¹ * (φ g * star (φ g)) := by rw [h1, Matrix.mul_one]
        _ = star (φ g) := by rw [← Matrix.mul_assoc, ← hφm, inv_mul_cancel, hφ1, Matrix.one_mul]
    rw [← hg, htr, hXu, hXu, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← eval_mul_eq_bind₁, hginv, hg, show Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
      dTor θ from rfl, eval_monomial_tor, mul_smul]
  set d := P.totalDegree
  set Wm : Set (Fin n → ℝ) := wtM '' {m : EntIdx n →₀ ℕ | (m.sum fun _ e => e) ≤ d}
  have hWfin : Wm.Finite := (finite_monomials_of_degree_le d).image _
  let Sd : H → Submodule ℂ H := fun u => (restrictTotalDegree (EntIdx n) ℂ d).map (Xu u)
  have hSdfd : ∀ u, FiniteDimensional ℂ (Sd u) := fun u => Module.Finite.map _ _
  have hSK : ∀ u, ∀ k ∈ Kset ε, ∀ x ∈ Sd u, σ k x ∈ Sd u := by
    intro u k hk x hx
    obtain ⟨g, rfl⟩ := hφs k hk
    obtain ⟨Q, hQ, rfl⟩ := hx
    rw [htr]
    refine Submodule.mem_map_of_mem ?_
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    rw [mem_restrictTotalDegree]
    exact (totalDegree_bind_le_of_linear _ (trF_totalDegree _) Q).trans hQ
  have hWS : ∀ u μ, (∃ s ∈ Sd u, s ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s) → μ ∈ Wm := by
    rintro u μ ⟨s, ⟨Q, hQ, rfl⟩, hs0, hsw⟩
    by_contra hμ
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    have hsum : Xu u Q = ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m • Xu u (monomial m 1) := by
      conv_lhs => rw [Q.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    have horth : ∀ m ∈ Q.support, inner ℂ (Xu u Q) (Xu u (monomial m 1)) = 0 := by
      intro m hm
      refine kfin_wt_orth hσ hsw (hmono u m) fun h => hμ ?_
      exact ⟨m, (le_totalDegree hm).trans hQ, h.symm⟩
    apply hs0
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    calc inner ℂ (Xu u Q) (Xu u Q) = inner ℂ (Xu u Q) (∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m • Xu u (monomial m 1)) := by
          rw [← hsum]
      _ = 0 := by
          rw [inner_sum]
          exact Finset.sum_eq_zero fun m hm => by rw [inner_smul_right, horth m hm, mul_zero]
  choose kf hkf using fun μ => khw_mem_layer hE hU hV hc hstd μ
  refine ⟨hWfin.toFinset.sup kf, fun u => ?_⟩
  have := hSdfd u
  have hle := kfin_key hσ hD hV.1 hV.2.1 (Sd u) (by rw [hdense]; exact le_top) (hSK u) (hWfin.toFinset.sup kf)
    (fun μ w hw hwk hμS => layer_mono (Finset.le_sup ((hWfin.mem_toFinset).2 (hWS u μ hμS))) (hkf μ w hw hwk))
  exact hle (Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ P).2 le_rfl))

end ReciprocityTheory.ChartRestriction.DS.TRGap
