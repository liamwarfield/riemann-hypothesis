module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasFiniteAdelicDoubleCosetsOfBlockDiagPartImage
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorStabiliserClosedSLOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosurePointsIsGroupStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteIntegralClassesClosedOrbit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducible
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpecialLinearClassNumberOneAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpecialLinearClassNumberOneAdelic
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_matrix_span_of_smul_mem {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) (N : ℤ)
    (hN : N ≠ 0) (hL : ∀ v : ι → ℤ, N • v ∈ L) :
    ∃ H : Matrix ι ι ℤ, (∀ j, (fun i => H i j) ∈ L) ∧ ∀ v ∈ L, ∃ c : ι → ℤ, v = H *ᵥ c := by
  have hr : Module.finrank ℤ L = Fintype.card ι := by
    apply le_antisymm
    · simpa using Submodule.finrank_le L
    · let f : (ι → ℤ) →ₗ[ℤ] L := LinearMap.codRestrict L (N • LinearMap.id) hL
      have hf : Function.Injective f := by
        intro a b hab
        have : N • a = N • b := congrArg Subtype.val hab
        exact smul_right_injective _ hN this
      simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b : Module.Basis ι ℤ L := (Module.finBasisOfFinrankEq ℤ L hr).reindex (Fintype.equivFin ι).symm
  refine ⟨Matrix.of fun i j => (b j : ι → ℤ) i, fun j => (b j).2, fun v hv => ⟨b.repr ⟨v, hv⟩, ?_⟩⟩
  have := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
  funext i
  have h2 := congrFun this i
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem exists_matrix_basis_of_lattice {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℚ)) (M : ℕ)
    (hM : 0 < M) (h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z)
    (h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L) :
    ∃ h g : Matrix ι ι ℚ, h * g = 1 ∧ (∀ j, (fun i => h i j) ∈ L) ∧ ∀ v ∈ L, ∀ i, ∃ z : ℤ, (g *ᵥ v) i = z := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  let φ : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
    { toFun := fun z i => (M : ℚ)⁻¹ * z i
      map_add' := fun a b => by funext i; simp [mul_add]
      map_smul' := fun a b => by funext i; simp; ring }
  obtain ⟨H, hH, hc⟩ := exists_matrix_span_of_smul_mem (L.comap φ) ((M : ℤ) * M)
    (by have := hM.ne'; positivity) (fun v => by
      have : φ (((M : ℤ) * M) • v) = fun i => (M : ℚ) * v i := by
        funext i
        simp [φ]
        field_simp
      simp only [Submodule.mem_comap, this]
      exact h2 v)
  let h : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * H i j
  have key : ∀ v ∈ L, ∃ c : ι → ℤ, v = h *ᵥ fun i => (c i : ℚ) := by
    intro v hv
    choose z hz using h1 v hv
    have hφ : φ z = v := by
      funext i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ← hz]
      field_simp
    obtain ⟨c, hc'⟩ := hc z (by simpa [hφ] using hv)
    refine ⟨c, ?_⟩
    rw [← hφ, hc']
    funext i
    simp [φ, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  choose C hC using fun j => key _ (h2 (Pi.single j 1))
  let g : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * C j i
  have hg : h * g = 1 := by
    ext i j
    have := congrFun (hC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    have e : (h * g) i j = (M : ℚ)⁻¹ * ∑ k, h i k * (C j k : ℚ) := by
      simp only [Matrix.mul_apply, g, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, ← this]
    by_cases hij : i = j
    · subst hij; simp [hM']
    · simp [hij]
  refine ⟨h, g, hg, fun j => hH j, fun v hv i => ?_⟩
  obtain ⟨c, rfl⟩ := key v hv
  refine ⟨c i, ?_⟩
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hg, Matrix.one_mulVec]

theorem det_mem_subring_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] (R₀ : Subring R)
    (k : Matrix ι ι R) (hk : ∀ i j, k i j ∈ R₀) : k.det ∈ R₀ := by
  rw [Matrix.det_apply']
  exact R₀.sum_mem fun σ _ => R₀.mul_mem (intCast_mem R₀ _) (R₀.prod_mem fun i _ => hk _ _)

theorem sl_class_number_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  intro ι _ _ R _ _ R₀ hp x hx
  obtain ⟨-, hden, hinj⟩ := adelicPair_elementary R R₀ hp
  set y := x.adjugate with hy
  have hxy : x * y = 1 := by rw [hy, Matrix.mul_adjugate, hx, one_smul]
  have hyx : y * x = 1 := mul_eq_one_comm.mp hxy
  obtain ⟨M, hM, hMr⟩ := hden ((ι × ι) ⊕ (ι × ι)) (Sum.elim (fun p => x p.1 p.2) (fun p => y p.1 p.2))
  have hMx : ∀ i j, (M : R) * x i j ∈ R₀ := fun i j => hMr (Sum.inl (i, j))
  have hMy : ∀ i j, (M : R) * y i j ∈ R₀ := fun i j => hMr (Sum.inr (i, j))
  let L : Submodule ℤ (ι → ℚ) := AddSubgroup.toIntSubmodule
    { carrier := {v | ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀}
      add_mem' := fun {a b} ha hb i => by
        simpa [mul_add, Finset.sum_add_distrib] using R₀.add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      neg_mem' := fun {a} ha i => by simpa using R₀.neg_mem (ha i) }
  have hLm : ∀ v, v ∈ L ↔ ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀ := fun v => Iff.rfl
  have h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L := by
    intro z
    rw [hLm]
    intro i
    refine R₀.sum_mem fun k _ => ?_
    have : y i k * algebraMap ℚ R ((M : ℚ) * z k) = (M : R) * y i k * z k := by simp; ring
    rw [this]
    exact R₀.mul_mem (hMy _ _) (intCast_mem R₀ _)
  have h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z := by
    intro v hv i
    apply hp.int_of_mem
    have e : (fun k => algebraMap ℚ R (v k)) = x *ᵥ (y *ᵥ fun k => algebraMap ℚ R (v k)) := by
      rw [Matrix.mulVec_mulVec, hxy, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [map_mul, map_natCast, e']
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine R₀.sum_mem fun k _ => ?_
    rw [← mul_assoc]
    exact R₀.mul_mem (hMx _ _) ((hLm v).1 hv k)
  obtain ⟨h, g, hg, hh, hgL⟩ := exists_matrix_basis_of_lattice L M hM h1 h2
  have hMg : ∀ i j, (M : R) * algebraMap ℚ R (g i j) ∈ R₀ := by
    intro i j
    obtain ⟨z, hz⟩ := hgL _ (h2 (Pi.single j 1)) i
    have : (M : ℚ) * g i j = z := by
      rw [← hz]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j]
      · simp [mul_comm]
      · intro b _ hb; simp [hb]
      · simp
    have e : (M : R) * algebraMap ℚ R (g i j) = (z : R) := by
      rw [← map_natCast (algebraMap ℚ R), ← map_mul, this, map_intCast]
    rw [e]
    exact intCast_mem R₀ _
  have hk : ∀ i j, (g.map (algebraMap ℚ R) * x) i j ∈ R₀ := by
    intro i j
    choose q a ha hqa using fun k => hp.approx M hM (x k j)
    have hq : q ∈ L := by
      rw [hLm]
      intro l
      have e : ∑ k, y l k * algebraMap ℚ R (q k) = (y * x) l j - ∑ k, (M : R) * y l k * a k := by
        rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
      rw [e, hyx]
      refine R₀.sub_mem ?_ (R₀.sum_mem fun k _ => R₀.mul_mem (hMy _ _) (ha k))
      rw [Matrix.one_apply]
      split_ifs
      exacts [R₀.one_mem, R₀.zero_mem]
    obtain ⟨z, hz⟩ := hgL q hq i
    have e : (g.map (algebraMap ℚ R) * x) i j =
        algebraMap ℚ R ((g *ᵥ q) i) + ∑ k, (M : R) * algebraMap ℚ R (g i k) * a k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, map_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
    rw [e, hz, map_intCast]
    exact R₀.add_mem (intCast_mem R₀ _) (R₀.sum_mem fun k _ => R₀.mul_mem (hMg _ _) (ha k))
  have hk' : ∀ i j, (y * h.map (algebraMap ℚ R)) i j ∈ R₀ := fun i j => (hLm _).1 (hh j) i
  have hmd : ∀ t : Matrix ι ι ℚ, (t.map (algebraMap ℚ R)).det = algebraMap ℚ R t.det := fun t =>
    ((algebraMap ℚ R).map_det t).symm
  have hdy : y.det = 1 := by
    have := congrArg Matrix.det hxy
    rwa [Matrix.det_mul, hx, one_mul, Matrix.det_one] at this
  obtain ⟨zg, hzg⟩ := hp.int_of_mem g.det (by
    have := det_mem_subring_of_entries R₀ _ hk
    rwa [Matrix.det_mul, hx, mul_one, hmd] at this)
  obtain ⟨zh, hzh⟩ := hp.int_of_mem h.det (by
    have := det_mem_subring_of_entries R₀ _ hk'
    rwa [Matrix.det_mul, hdy, one_mul, hmd] at this)
  have hdd : h.det * g.det = 1 := by rw [← Matrix.det_mul, hg, Matrix.det_one]
  have hz : zh * zg = 1 := by
    rw [hzg, hzh] at hdd
    exact_mod_cast hdd
  have hxe : x = h.map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hg]
    simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hz with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨h, _, by simp [hzh, e1], ?_, hk, hxe⟩
    rw [Matrix.det_mul, hx, hmd, hzg, e2]
    simp
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · rw [Matrix.det_isEmpty, e1] at hzh
      norm_num at hzh
    · let d : ι → ℚ := fun i => if i = i₀ then -1 else 1
      have hd : (Matrix.diagonal d).det = -1 := by simp [d]
      have hdd2 : Matrix.diagonal d * Matrix.diagonal d = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        by_cases hi : i = i₀ <;> simp [d, hi]
      refine ⟨h * Matrix.diagonal d, (Matrix.diagonal d).map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x),
        ?_, ?_, ?_, ?_⟩
      · rw [Matrix.det_mul, hd, hzh, e1]
        simp
      · rw [Matrix.det_mul, Matrix.det_mul, hx, hmd, hmd, hd, hzg, e2]
        simp
      · intro i j
        rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
        refine R₀.mul_mem ?_ (hk i j)
        by_cases hi : i = i₀
        · simpa [d, hi] using R₀.neg_mem R₀.one_mem
        · simpa [d, hi] using R₀.one_mem
      · rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_assoc h, hdd2, Matrix.mul_one]
        exact hxe

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpecialLinearClassNumberOneAdelicStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialLinear_classNumber_one_adelic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  first | exact @GlobalTheory.ClassFin.sl_class_number_one | exact GlobalTheory.ClassFin.sl_class_number_one | (intros; apply GlobalTheory.ClassFin.sl_class_number_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducible
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mul_entry_mem_subring {ι : Type} [Fintype ι] {R : Type} [CommRing R]
    (S : Subring R) (k l : Matrix ι ι R) (hk : ∀ i j, k i j ∈ S) (hl : ∀ i j, l i j ∈ S) :
    ∀ i j, (k * l) i j ∈ S := by
  intro i j
  rw [Matrix.mul_apply]
  exact S.sum_mem fun a _ => S.mul_mem (hk _ _) (hl _ _)

theorem cf_of_ss : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _ Γ R _ _ R₀ hΓ hss hA
  classical
  obtain ⟨m, d, t, hfix, hstab, hcl⟩ := GlobalTheory.T.exists_tensor_stabiliser_closed_SL_orbit ι Γ hΓ hss
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction ι m d t
  obtain ⟨-, hmul, hadj, hdet⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι Γ hΓ.toIsPre R
  obtain ⟨hrat, hratR⟩ := GlobalTheory.T.rat_mem_ratZariskiClosurePoints ι Γ
  obtain ⟨D, hD, hDt⟩ := (adelicPair_elementary R R₀ hA).2.1 (TIdx ι d) (fun k => algebraMap ℚ R (t k))
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.finite_integral_classes_closedOrbit ι m d t hcl D hD
  have hone : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S), act d s 1 = s :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).1
  have hact : ∀ (S : Type) [CommRing S] (s : TIdx ι d → S) (y z : Matrix ι ι S),
      act d s (y * z) = act d (act d s y) z :=
    fun S _ s => ((tpow_act_algebra ι S).2 m d s).2.1
  have hmap : ∀ (S : Type) [CommRing S] [Algebra ℚ S] (s : TIdx ι d → ℚ) (y : Matrix ι ι ℚ),
      act d (fun k => algebraMap ℚ S (s k)) (y.map (algebraMap ℚ S)) = fun k => algebraMap ℚ S (act d s y k) :=
    fun S _ _ s y => ((tpow_act_algebra ι ℚ).2 m d s).2.2.2.2.2 S (algebraMap ℚ S) y

  have hfixR : ∀ x ∈ pts Γ R, act d (fun k => algebraMap ℚ R (t k)) x = fun k => algebraMap ℚ R (t k) := by
    intro x hx
    funext k
    have hv : Φ k - MvPolynomial.C (t k) ∈ vanI Γ := by
      intro g hg
      have h1 := hΦ ℂ g k
      have h2 := congrFun (hfix g hg) k
      simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 ⊢
      rw [h1, sub_eq_zero]
      exact h2
    have h3 := hx _ hv
    have h1 := hΦ R x k
    simp only [ev, map_sub, MvPolynomial.aeval_C] at h1 h3
    rw [← h1]
    exact sub_eq_zero.1 h3
  let P : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R → Prop := fun z p =>
    p.1.det = 1 ∧ p.2.det = 1 ∧ (∀ i j, p.2 i j ∈ R₀) ∧ p.1.map (algebraMap ℚ R) * p.2 ∈ pts Γ R ∧
      act d t p.1 = z
  have key : ∀ x ∈ pts Γ R, ∃ z ∈ Z, ∃ p, P z p ∧ x = p.1.map (algebraMap ℚ R) * p.2 := by
    intro x hx
    obtain ⟨h, k, hh, hk, hkint, rfl⟩ := GlobalTheory.T.specialLinear_classNumber_one_adelic ι R R₀ hA x (hdet x hx)
    have hkk : k * k.adjugate = 1 := by rw [Matrix.mul_adjugate, hk, one_smul]
    have e1 : act d (fun k => algebraMap ℚ R (t k)) k.adjugate = fun k => algebraMap ℚ R (act d t h k) := by
      rw [← hmap]
      conv_lhs => rw [← hfixR _ hx, ← hact, Matrix.mul_assoc, hkk, Matrix.mul_one]
    have e2 : ∀ j, ∃ z : ℤ, (D : ℚ) * act d t h j = z := by
      intro j
      apply hA.int_of_mem
      have h1 := ((tpow_act_algebra ι R).2 m d ((D : R) • fun k => algebraMap ℚ R (t k))).2.2.2.1 R₀
        k.adjugate (fun k => hDt k) (adjugate_entry_mem_subring R₀ k hkint) j
      rw [((tpow_act_algebra ι R).2 m d (fun k => algebraMap ℚ R (t k))).2.2.2.2.1, e1] at h1
      rw [map_mul, map_natCast]
      exact h1
    obtain ⟨γ, hγ, hγZ⟩ := hZ h hh e2
    have hγγ : γ * γ.adjugate = 1 := by rw [Matrix.mul_adjugate, hγ, one_smul]
    have hγR : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * γ.adjugate.map (Int.castRingHom R) = 1 := by
      have : (γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) = γ.map (Int.castRingHom R) := by
        ext i j; simp
      rw [this, ← Matrix.map_mul, hγγ, Matrix.map_one _ (map_zero _) (map_one _)]
    have e3 : (h * γ.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ R) * (γ.adjugate.map (Int.castRingHom R) * k)
        = h.map (algebraMap ℚ R) * k := by
      rw [Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ k, hγR, Matrix.one_mul]
    refine ⟨_, hγZ, (h * γ.map (Int.cast : ℤ → ℚ), γ.adjugate.map (Int.castRingHom R) * k),
      ⟨?_, ?_, ?_, ?_, rfl⟩, e3.symm⟩
    · have : (γ.map (Int.cast : ℤ → ℚ)).det = 1 := by
        have h1 := (Int.castRingHom ℚ).map_det γ
        rw [hγ, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hh, this, one_mul]
    · have : (γ.adjugate.map (Int.castRingHom R)).det = 1 := by
        have h1 := (Int.castRingHom R).map_det γ.adjugate
        rw [Matrix.det_adjugate, hγ, one_pow, map_one] at h1
        exact h1.symm
      simp only [Matrix.det_mul, hk, this, one_mul]
    · exact mul_entry_mem_subring R₀ _ _ (fun i j => intCast_mem R₀ _) hkint
    · simp only
      rw [e3]; exact hx
  let c : (TIdx ι d → ℚ) → Matrix ι ι ℚ × Matrix ι ι R := fun z =>
    if hz : ∃ p, P z p then hz.choose else (1, 1)
  have hc : ∀ z, (∃ p, P z p) → P z (c z) := by
    intro z hz
    simp only [c, dif_pos hz]
    exact hz.choose_spec
  refine ⟨(Z.filter fun z => ∃ p, P z p).image fun z => (c z).1.map (algebraMap ℚ R) * (c z).2, ?_, ?_⟩
  · intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hs
    exact (hc z (Finset.mem_filter.1 hz).2).2.2.2.1
  · intro x hx
    obtain ⟨z, hz, ⟨h, k⟩, hp, rfl⟩ := key x hx
    have hz' : z ∈ Z.filter fun z => ∃ p, P z p := Finset.mem_filter.2 ⟨hz, _, hp⟩
    have hq := hc z ⟨_, hp⟩
    have hs := Finset.mem_image_of_mem (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) hz'
    generalize (Z.filter fun z => ∃ p, P z p).image (fun z => (c z).1.map (algebraMap ℚ R) * (c z).2) = T at hs ⊢
    generalize c z = q at hq hs
    obtain ⟨h', k'⟩ := q
    obtain ⟨hh, hk, hkint, hxx, hhz⟩ := hp
    obtain ⟨hh', hk', hkint', hxx', hhz'⟩ := hq
    simp only at hh hk hkint hxx hhz hh' hk' hkint' hxx' hhz' hs ⊢
    have a1 : h' * h'.adjugate = 1 := by rw [Matrix.mul_adjugate, hh', one_smul]
    have a2 : h'.adjugate * h' = 1 := by rw [Matrix.adjugate_mul, hh', one_smul]
    have a3 : k' * k'.adjugate = 1 := by rw [Matrix.mul_adjugate, hk', one_smul]
    have g1 : act d t (h * h'.adjugate) = t := by
      rw [hact, hhz, ← hhz', ← hact, a1, hone]
    have g2 : h * h'.adjugate ∈ pts Γ ℚ := by
      apply hrat
      apply hstab
      · have h1 := (algebraMap ℚ ℂ).map_det (h * h'.adjugate)
        rw [Matrix.det_mul, Matrix.det_adjugate, hh, hh', one_pow, one_mul, map_one] at h1
        exact h1.symm
      · have h1 := hmap ℂ t (h * h'.adjugate)
        rw [g1] at h1
        exact h1
    have g3 := hratR R _ g2
    have e : h.map (algebraMap ℚ R) * k = (h * h'.adjugate).map (algebraMap ℚ R) *
        (h'.map (algebraMap ℚ R) * k') * (k'.adjugate * k) := by
      rw [← Matrix.mul_assoc _ _ k', ← Matrix.map_mul, Matrix.mul_assoc h, a2, Matrix.mul_one,
        Matrix.mul_assoc, ← Matrix.mul_assoc k', a3, Matrix.one_mul]
    refine ⟨_, g2, _, hs, k'.adjugate * k, ?_,
      mul_entry_mem_subring R₀ _ _ (adjugate_entry_mem_subring R₀ k' hkint') hkint, e⟩
    have g4 := hmul _ g3 _ hxx'
    have g5 := hmul _ (hadj _ g4) _ hxx
    rw [e, ← Matrix.mul_assoc, Matrix.adjugate_mul, hdet _ g4, one_smul, Matrix.one_mul] at g5
    exact g5

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassFinitenessCompletelyReducibleStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFiniteness_completelyReducible : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → SS Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_ss | exact GlobalTheory.ClassFin.cf_of_ss | (intros; apply GlobalTheory.ClassFin.cf_of_ss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosureOfAutStableSLGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosureOfAutStableSLGroup
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatClosure

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem subset_pts (Γ : Set (Matrix ι ι ℂ)) : Γ ⊆ pts Γ ℂ := fun g hg _ hf => hf g hg

omit [Fintype ι] [DecidableEq ι] in
theorem vanI_pts (Γ : Set (Matrix ι ι ℂ)) : vanI (pts Γ ℂ) = vanI Γ := by
  ext f
  exact ⟨fun h g hg => h g (subset_pts Γ hg), fun h g hg => hg f h⟩

omit [Fintype ι] [DecidableEq ι] in
theorem ev_map_aut (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    ev f (g.map σ) = σ (ev f g) := by
  unfold ev
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Matrix.map_apply]

theorem exists_poly_of_dual (φ : Module.Dual ℂ (Matrix ι ι ℂ)) :
    ∃ f : MvPolynomial (ι × ι) ℂ, ∀ g, evC f g = φ g := by
  refine ⟨∑ ij : ι × ι, MvPolynomial.C (φ (Matrix.single ij.1 ij.2 1)) * MvPolynomial.X ij, fun g => ?_⟩
  conv_rhs => rw [Matrix.matrix_eq_sum_single g]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [evC, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : Matrix.single i j (g i j) = g i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

theorem ratClosure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  intro ι _ _ Γ h
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.ratZariskiClosurePoints_isGroup ι Γ h ℂ
  refine ⟨⟨⟨h1, h2, h3, h4, ?_⟩, ?_⟩, vanI_pts Γ, ?_⟩
  · intro σ g hg f hf
    rw [ev_map_aut, hg f hf, map_zero]
  · intro g hg f hf
    exact hg f (by rw [vanI_pts]; exact hf)
  · refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) (Submodule.span_mono (subset_pts Γ))
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (Submodule.span ℂ Γ) y).1 fun φ hφ => ?_
    obtain ⟨f, hf⟩ := exists_poly_of_dual φ
    rw [← hf]
    refine GlobalTheory.T.evalComplexPoly_eq_zero_on_ratZariskiClosure ι Γ h.aut_mem f (fun g hg => ?_) y hy
    rw [hf]
    exact (Submodule.mem_dualAnnihilator φ).1 hφ g (Submodule.subset_span hg)

end GlobalTheory.ClassFin.RatClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatZariskiClosureOfAutStableSLGroupStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → IsQGroup (pts Γ ℂ) ∧ vanI (pts Γ ℂ) = vanI Γ ∧ Submodule.span ℂ (pts Γ ℂ) = Submodule.span ℂ Γ := by
  first | exact @GlobalTheory.ClassFin.RatClosure.ratClosure | exact GlobalTheory.ClassFin.RatClosure.ratClosure | (intros; apply GlobalTheory.ClassFin.RatClosure.ratClosure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentBlockDiagPartKillsSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspace
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_of_stable (ι : Type) [Fintype ι] [DecidableEq ι]
    (W : Submodule ℂ (ι → ℂ))
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) :
    ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  classical

  obtain ⟨Wq, hWq⟩ : ∃ Wq : Submodule ℚ (ι → ℚ),
      ∀ q, q ∈ Wq ↔ (fun i => algebraMap ℚ ℂ (q i)) ∈ W := by
    refine ⟨{ carrier := {q | (fun i => algebraMap ℚ ℂ (q i)) ∈ W}
              add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun q => Iff.rfl⟩
    · intro a b ha hb
      have h : (fun i => algebraMap ℚ ℂ ((a + b) i))
          = (fun i => algebraMap ℚ ℂ (a i)) + (fun i => algebraMap ℚ ℂ (b i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((a + b) i)) ∈ W
      rw [h]; exact W.add_mem ha hb
    · show (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) ∈ W
      have h : (fun i => algebraMap ℚ ℂ ((0 : ι → ℚ) i)) = 0 := by ext i; simp
      rw [h]; exact W.zero_mem
    · intro c q hq
      have h : (fun i => algebraMap ℚ ℂ ((c • q) i))
          = algebraMap ℚ ℂ c • (fun i => algebraMap ℚ ℂ (q i)) := by
        ext i; simp
      show (fun i => algebraMap ℚ ℂ ((c • q) i)) ∈ W
      rw [h]; exact W.smul_mem _ hq

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl Wq
  obtain ⟨f, hf1, hf2⟩ : ∃ f : (ι → ℚ) →ₗ[ℚ] (ι → ℚ), (∀ q, f q ∈ Wq) ∧ (∀ q ∈ Wq, f q = q) :=
    ⟨Wq.subtype ∘ₗ Wq.projectionOnto C hC, fun q => (Wq.projectionOnto C hC q).2,
      fun q hq => congrArg Subtype.val (Submodule.projectionOnto_apply_left hC ⟨q, hq⟩)⟩
  have hff : f ∘ₗ f = f := LinearMap.ext fun q => hf2 _ (hf1 q)

  have hstable := GlobalTheory.T.galoisStable_submodule_le_span_rational (ι → ℂ) ι (Pi.basisFun ℂ ι) W
    (fun σ w hw => ⟨fun i => σ (w i), hW σ w hw, fun k => by simp⟩)
  refine ⟨LinearMap.toMatrix' f, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hff]

  have hA : ∀ q : ι → ℚ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => algebraMap ℚ ℂ (q i)) = fun i => algebraMap ℚ ℂ (f q i) := by
    intro q
    ext i
    rw [← LinearMap.toMatrix'_mulVec f q]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

  have hB : ∀ v : ι → ℂ, (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v ∈ W := by
    intro v
    have hcol : ∀ j, (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) ∈ W := by
      intro j
      simp only [LinearMap.toMatrix'_apply]
      exact (hWq _).1 (hf1 _)
    have h : (LinearMap.toMatrix' f).map (algebraMap ℚ ℂ) *ᵥ v
        = ∑ j, v j • (fun i => algebraMap ℚ ℂ (LinearMap.toMatrix' f i j)) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h]
    exact W.sum_mem fun j _ => W.smul_mem _ (hcol j)
  intro v
  constructor
  · intro hv
    have hspan := hstable hv
    clear hv
    induction hspan using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨hwW, hq⟩ := hw
      choose q hq using hq
      have hw : w = fun i => algebraMap ℚ ℂ (q i) := by
        ext k
        rw [← Pi.basisFun_repr ℂ ι w k, hq k]
        exact (eq_ratCast (algebraMap ℚ ℂ) (q k)).symm
      have hqW : q ∈ Wq := (hWq q).2 (by rw [← hw]; exact hwW)
      rw [hw, hA, hf2 q hqW]
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  · intro hv
    rw [← hv]
    exact hB v

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentOfAutStableSubspaceStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) → ∃ e : Matrix ι ι ℚ, e * e = e ∧ ∀ v, v ∈ W ↔ e.map (algebraMap ℚ ℂ) *ᵥ v = v := by
  first | exact @GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | exact GlobalTheory.ClassFin.exists_rat_idempotent_of_stable | (intros; apply GlobalTheory.ClassFin.exists_rat_idempotent_of_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantSubspaceNotSemisimple
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantSubspaceNotSemisimple
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mem_mul_eq_zero_of_isNilpotent {R : Type*} [Ring R] (J : Ideal R) [J.IsTwoSided]
    (hJ : IsNilpotent J) (h0 : J ≠ ⊥) : ∃ a ∈ J, a ≠ 0 ∧ ∀ b ∈ J, b * a = 0 := by
  obtain ⟨n, hn⟩ := hJ
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, J ^ (k + 1) ≠ ⊥ := by
    intro k
    induction k with
    | zero => simpa [Submodule.pow_one] using h0
    | succ k ih =>
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
      obtain ⟨b, hb, hba⟩ := hcon a (Ideal.pow_le_self (Nat.succ_ne_zero k) ha) ha0
      intro h
      apply hba
      have : b * a ∈ J ^ (k + 1 + 1) := by
        rw [Ideal.IsTwoSided.pow_succ]
        exact Ideal.mul_mem_mul hb ha
      rw [h] at this
      simpa using this
  apply key n
  rw [Submodule.pow_succ, hn]
  simp

theorem map_mem_jacobson_of_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) {b : R} (hb : b ∈ Ring.jacobson R) : f b ∈ Ring.jacobson S := by
  have : RingHomSurjective f := ⟨hf⟩
  exact Ring.le_comap_jacobson (f := f) hb

noncomputable def spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ) :
    Subalgebra ℂ (Matrix ι ι ℂ) :=
  (Submodule.span ℂ Γ).toSubalgebra (Submodule.subset_span h.one_mem) (by
    intro x y hx hy
    have h1 := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact h.mul_mem a ha b hb)

theorem map_mem_spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) {x : Matrix ι ι ℂ} (hx : x ∈ spanAlg h) : x.map σ ∈ spanAlg h := by
  change x ∈ Submodule.span ℂ Γ at hx
  change Matrix.map x (⇑σ : ℂ → ℂ) ∈ Submodule.span ℂ Γ
  induction hx using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span (h.aut_mem σ g hg)
  | zero =>
    have e : Matrix.map (0 : Matrix ι ι ℂ) (⇑σ : ℂ → ℂ) = 0 := by
      ext i j; simp
    rw [e]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have e : Matrix.map (a + b) (⇑σ : ℂ → ℂ) = Matrix.map a (⇑σ : ℂ → ℂ) + Matrix.map b (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have e : Matrix.map (c • a) (⇑σ : ℂ → ℂ) = σ c • Matrix.map a (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.smul_mem _ _ ha

noncomputable def spanAlgMap {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : spanAlg h →+* spanAlg h :=
  RingHom.codRestrict ((σ : ℂ →+* ℂ).mapMatrix.comp (spanAlg h).val.toRingHom) (spanAlg h)
    (fun x => map_mem_spanAlg h σ x.2)

theorem spanAlgMap_surjective {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : Function.Surjective (spanAlgMap h σ) := by
  intro y
  refine ⟨⟨y.1.map σ.symm, map_mem_spanAlg h σ.symm y.2⟩, ?_⟩
  apply Subtype.ext
  ext i j
  simp [spanAlgMap]

theorem ss_of_isSemisimpleRing {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    [IsSemisimpleRing (spanAlg h)] : SS Γ := by
  intro W hW
  have hW' : ∀ x ∈ Submodule.span ℂ Γ, ∀ v ∈ W, x *ᵥ v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => exact hW x hx v hv
    | zero => simp
    | add x y _ _ hx hy => rw [add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [smul_mulVec]; exact W.smul_mem _ hx
  let U : Submodule (spanAlg h) (ι → ℂ) :=
    { W.toAddSubmonoid with smul_mem' := fun c v hv => hW' c.1 c.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  have hsm : ∀ (x : Matrix ι ι ℂ), x ∈ spanAlg h → ∀ v ∈ U', x *ᵥ v ∈ U' :=
    fun x hx v hv => U'.smul_mem ⟨x, hx⟩ hv
  let W' : Submodule ℂ (ι → ℂ) :=
    { U'.toAddSubmonoid with
      smul_mem' := fun c v hv => by
        have := hsm (c • 1) ((spanAlg h).smul_mem (spanAlg h).one_mem c) v hv
        rwa [smul_mulVec, one_mulVec] at this }
  refine ⟨W', fun g hg v hv => hsm g (Submodule.subset_span hg) v hv, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact Submodule.disjoint_def.1 hU.disjoint x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have : x ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hy hz

theorem exists_socle_radical_of_not_ss :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  intro ι _ _ Γ h hss
  have : IsArtinianRing (spanAlg h) := IsArtinianRing.of_finite ℂ _
  have h0 : Ring.jacobson (spanAlg h) ≠ ⊥ := by
    intro h0
    have := IsArtinianRing.isSemisimpleRing_iff_jacobson.2 h0
    exact hss (ss_of_isSemisimpleRing h)
  obtain ⟨a, ha, ha0, hba⟩ := exists_mem_mul_eq_zero_of_isNilpotent (Ring.jacobson (spanAlg h))
    IsSemiprimaryRing.isNilpotent h0
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := {v | ∀ b ∈ Ring.jacobson (spanAlg h), b.1 *ᵥ v = 0}
      add_mem' := fun {x y} hx hy b hb => by rw [mulVec_add, hx b hb, hy b hb, add_zero]
      zero_mem' := fun b _ => mulVec_zero _
      smul_mem' := fun c v hv b hb => by rw [mulVec_smul, hv b hb, smul_zero] }
  refine ⟨W, ?_, ?_, a.1, a.2, fun h1 => ha0 (Subtype.ext h1), ?_, fun v hv => hv a ha⟩
  · intro g hg v hv b hb
    have hg' : g ∈ spanAlg h := Submodule.subset_span hg
    have h1 : b * (⟨g, hg'⟩ : spanAlg h) ∈ Ring.jacobson (spanAlg h) := Ideal.mul_mem_right _ _ hb
    have h2 := hv _ h1
    rw [MulMemClass.coe_mul, ← mulVec_mulVec] at h2
    exact h2
  · intro σ v hv b hb
    have h1 : spanAlgMap h σ.symm b ∈ Ring.jacobson (spanAlg h) :=
      map_mem_jacobson_of_surjective _ (spanAlgMap_surjective h σ.symm) hb
    have h2 := hv _ h1
    funext i
    have h3 := congrArg σ (congrFun h2 i)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [spanAlgMap, mulVec, dotProduct, map_sum] using h3
  · intro v b hb
    rw [mulVec_mulVec]
    have := congrArg Subtype.val (hba b hb)
    change b.1 * a.1 = 0 at this
    rw [this, zero_mulVec]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.InvariantSubspaceNotSemisimpleStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_subspace_not_semisimple : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  first | exact @GlobalTheory.ClassFin.exists_socle_radical_of_not_ss | exact GlobalTheory.ClassFin.exists_socle_radical_of_not_ss | (intros; apply GlobalTheory.ClassFin.exists_socle_radical_of_not_ss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentBlockDiagPartKillsSpan
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_blk_eq_zero : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨W, hWinv, hWσ, a, ha_span, ha0, ha_into, ha_kill⟩ := GlobalTheory.T.invariant_subspace_not_semisimple ι Γ hΓ hss
  obtain ⟨e, hee, hW⟩ := GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace ι W hWσ

  have hEE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, hee]
  have hEmem : ∀ v, e.map (algebraMap ℚ ℂ) *ᵥ v ∈ W := fun v => by
    rw [hW, Matrix.mulVec_mulVec, hEE]
  have hfix : ∀ w ∈ W, e.map (algebraMap ℚ ℂ) *ᵥ w = w := fun w hw => (hW w).1 hw
  refine ⟨e, hee, ?_, a, ha_span, ha0, ?_⟩
  ·
    intro g hg
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hfix _ (hWinv g hg _ (hEmem v)), sub_self, Matrix.zero_mulVec]
  ·
    rw [Matrix.ext_iff_mulVec]
    intro v
    unfold blk
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha_kill _ (hEmem v),
      Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (ha_into _), sub_self, Matrix.zero_mulVec]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatIdempotentBlockDiagPartKillsSpanStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  first | exact @GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero | exact GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero | (intros; apply GlobalTheory.ClassFin.exists_rat_idempotent_blk_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSpanBlockDiagPartImageLt
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSpanBlockDiagPartImageLt
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem finrank_span_blk_image_lt :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  intro ι _ _ Γ e a ha ha0 hblk

  let L : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun x => blk e x
      map_add' := fun x y => by
        simp only [blk, Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c x => by
        simp only [blk, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add] }
  have himg : Submodule.span ℂ (blk e '' Γ) = (Submodule.span ℂ Γ).map L := by
    rw [Submodule.map_span]
    rfl
  rw [himg]

  set S := Submodule.span ℂ Γ with hS
  let f := L.domRestrict S
  have hrange : LinearMap.range f = S.map L := LinearMap.range_domRestrict S L
  have hker : (⟨a, ha⟩ : S) ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, f, LinearMap.domRestrict_apply]
    exact hblk
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hker
    exact ha0 (congrArg Subtype.val hker)
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker f) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  omega

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSpanBlockDiagPartImageLtStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_span_blockDiagPart_image_lt : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  first | exact @GlobalTheory.ClassFin.finrank_span_blk_image_lt | exact GlobalTheory.ClassFin.finrank_span_blk_image_lt | (intros; apply GlobalTheory.ClassFin.finrank_span_blk_image_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroup
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem cf_congr_of_vanI_eq {ι : Type} [Fintype ι] [DecidableEq ι] {Γ Δ : Set (Matrix ι ι ℂ)}
    (h : vanI Γ = vanI Δ) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) :
    CF Γ R R₀ ↔ CF Δ R R₀ := by

  have key : ∀ (S : Type) [CommRing S] [Algebra ℚ S], pts Γ S = pts Δ S := by
    intro S _ _
    simp only [pts, h]
  simp only [CF, key]

theorem cf_of_isQGroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  intro ι _ _

  suffices H : ∀ n : ℕ, ∀ (Γ : Set (Matrix ι ι ℂ)), Module.finrank ℂ (Submodule.span ℂ Γ) = n →
      ∀ (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ by
    intro Γ R _ _ R₀ hQ hA
    exact H _ Γ rfl R R₀ hQ hA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Γ hn R _ _ R₀ hQ hA
    by_cases hS : SS Γ
    · exact GlobalTheory.T.classFiniteness_completelyReducible ι Γ R R₀ hQ hS hA
    · obtain ⟨e, he, hup, a, ha, ha0, hblk⟩ := GlobalTheory.T.exists_rat_idempotent_blockDiagPart_kills_span ι Γ hQ.toIsPre hS

      have hPre : IsPre (blk e '' Γ) := GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart ι Γ e hQ.toIsPre he hup
      obtain ⟨hQ', hvan, hspan⟩ := GlobalTheory.T.ratZariskiClosure_of_autStable_SL_group ι (blk e '' Γ) hPre
      have hlt := GlobalTheory.T.finrank_span_blockDiagPart_image_lt ι Γ e a ha ha0 hblk
      have hcl : CF (pts (blk e '' Γ) ℂ) R R₀ :=
        ih _ (by rw [← hn, hspan]; exact hlt) _ rfl R R₀ hQ' hA
      have hblkCF : CF (blk e '' Γ) R R₀ := (cf_congr_of_vanI_eq hvan R R₀).mp hcl
      exact GlobalTheory.T.hasFiniteAdelicDoubleCosets_of_blockDiagPart_image ι Γ e R R₀ hQ he hup hA hblkCF

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteAdelicDoubleCosetsOfRationalSLSubgroupStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicDoubleCosets_of_rational_SL_subgroup : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), IsQGroup Γ → AdelicPair R R₀ → CF Γ R R₀ := by
  first | exact @GlobalTheory.ClassFin.cf_of_isQGroup | exact GlobalTheory.ClassFin.cf_of_isQGroup | (intros; apply GlobalTheory.ClassFin.cf_of_isQGroup <;> assumption)
end
