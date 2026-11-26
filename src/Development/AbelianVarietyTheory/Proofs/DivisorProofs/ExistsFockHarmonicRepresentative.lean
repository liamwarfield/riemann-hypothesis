module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial GlobalTheory.FockDeg

namespace GlobalTheory.FockAlg.HarmLift

variable {p q r s : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem plusPart_eq_sub {Z : Mat p q} (hZ : IsPC Z) (Q : Pol p q r s) :
    plusPart (fockAct1 p q r s Z) Q = fockAct1 p q r s Z Q - minusPart (fockAct1 p q r s Z) Q := by
  rw [fockAct1_eq, omAct_eq_parts (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ) Q, add_sub_cancel_right]

theorem minusPart_mem {Z : Mat p q} (hZ : IsPC Z) {d : ℕ} {Q : Pol p q r s}
    (hQ : Q ∈ homog (Ix p q × Ix r s) d) :
    minusPart (fockAct1 p q r s Z) Q ∈ homog (Ix p q × Ix r s) (d - 2) := by
  rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ)]
  exact downOp_mem _ d Q hQ

theorem minusPart_low {Z : Mat p q} (hZ : IsPC Z) {d : ℕ} (hd : d < 2) {Q : Pol p q r s}
    (hQ : Q ∈ homog (Ix p q × Ix r s) d) : minusPart (fockAct1 p q r s Z) Q = 0 := by
  rw [fockAct1_eq, minusPart_omAct (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ)]
  exact downOp_low _ d Q hd hQ

theorem span_harm2 : Submodule.span ℂ (harm2 p q r s) = HarmStable.sub2 p q r s := by
  rw [← HarmStable.coe_fockHarmonicsSecondMemberSubmodule, Submodule.span_eq]

theorem homog_le (pr : Pol p q r s →ₗ[ℂ] W)
    (hpr : ∀ Z : Mat p q, IsPC Z → ∀ f, pr (fockAct1 p q r s Z f) = 0) (d : ℕ) :
    homog (Ix p q × Ix r s) d ≤ HarmStable.sub2 p q r s ⊔ LinearMap.ker pr := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases Nat.lt_or_ge d 2 with hd | hd
    · intro f hf
      refine Submodule.mem_sup_left ?_
      rw [← SetLike.mem_coe, HarmStable.coe_fockHarmonicsSecondMemberSubmodule]
      exact fun Z hZ => minusPart_low hZ hd hf
    · obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
      rw [(GlobalTheory.FischerParts.fischer_parts p q r s n).1, span_harm2]
      refine sup_le (inf_le_right.trans le_sup_left) (Submodule.span_le.2 ?_)
      rintro _ ⟨Q, hQ, Z, hZ, rfl⟩
      rw [SetLike.mem_coe, plusPart_eq_sub hZ]
      refine Submodule.sub_mem _ (Submodule.mem_sup_right (hpr Z hZ Q)) ?_
      exact ih (n - 2) (by omega) (minusPart_mem hZ hQ)

theorem exists_harm2_rep : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) →
    ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  intro P Q R S W _ _ pr hpr f
  have hf : f ∈ HarmStable.sub2 P Q R S ⊔ LinearMap.ker pr := by
    rw [← sum_homogeneousComponent f]
    exact Submodule.sum_mem _ fun i _ => homog_le pr hpr i (homogeneousComponent_mem i f)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
  refine ⟨y, ?_, ?_⟩
  · rw [← HarmStable.coe_fockHarmonicsSecondMemberSubmodule]; exact hy
  · rw [map_add (f := _), LinearMap.mem_ker.1 hz, add_zero]

end GlobalTheory.FockAlg.HarmLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentativeStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockHarmonic_representative : ∀ (P Q R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (pr : Pol P Q R S →ₗ[ℂ] W), (∀ Z : Mat P Q, IsPC Z → ∀ f, pr (fockAct1 P Q R S Z f) = 0) → ∀ f, ∃ h ∈ harm2 P Q R S, pr h = pr f := by
  first | exact @GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | exact GlobalTheory.FockAlg.HarmLift.exists_harm2_rep | (intros; apply GlobalTheory.FockAlg.HarmLift.exists_harm2_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSubValueEqSumSqZeroVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSubValueEqSumSqZeroVector
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFamily

theorem taylor_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  intro I _ _ g R _ _ J N hJ r
  induction r with
  | zero =>
    intro m _ _ τ _
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun a => ?_⟩
    have h := (taylor_formal_properties N (fun i ↦ ∑ j : Fin 0, m j i)).2.2.2.2.2 (fun z ↦ τ z a)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    have : Set.range (fun _ : I => (0 : R)) ⊆ {0} := by
      rintro _ ⟨_, rfl⟩; rfl
    have hb : Ideal.span (Set.range (fun _ : I => (0 : R))) = ⊥ := by
      rw [Ideal.span_eq_bot]; rintro _ ⟨_, rfl⟩; rfl
    rw [hb, Ideal.mem_bot] at h
    exact h
  | succ r ih =>
    intro m hmJ hm τ hτ
    obtain ⟨n', hn'J, hn', hn'eq⟩ := ih (fun j => m (Fin.castSucc j)) (fun j i => hmJ _ i)
      (fun j i i' => hm _ i i') τ hτ
    set t : I → R := fun i => ∑ j : Fin r, m (Fin.castSucc j) i with ht
    set l : I → R := fun i => m (Fin.last r) i with hl
    let v : Fin g → R := fun a => ∑ i, taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i 1)) * l i
    have htJ : ∀ i, t i ∈ J := fun i => J.sum_mem fun j _ => hmJ _ i
    have hlJ : ∀ i, l i ∈ J := fun i => hmJ _ i
    have hspan : Ideal.span (Set.range t ∪ Set.range l) ≤ J := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact htJ i
      · exact hlJ i
    have hvJ : ∀ a, v a ∈ J := fun a => J.sum_mem fun i _ => J.mul_mem_left _ (hlJ i)
    have hv : ∀ a b, v a * v b = 0 := by
      intro a b
      simp only [v, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => ?_
      have := hm (Fin.last r) i' i
      calc _ = (taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z b) z (Pi.single i 1)) *
              taylor N t (fun z ↦ fderiv ℂ (fun z ↦ τ z a) z (Pi.single i' 1))) * (l i' * l i) := by ring
        _ = 0 := by simp only [hl, this, mul_zero]
    refine ⟨Fin.snoc (α := fun _ => Fin g → R) n' v, ?_, ?_, ?_⟩
    · intro j a
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hvJ a
      · simpa using hn'J j a
    · intro j a b
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hv a b
      · simpa using hn' j a b
    · intro a
      have hfa : AnalyticAt ℂ (fun z ↦ τ z a) 0 :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) a).analyticAt (τ 0)).comp hτ
      have hsum : (fun i ↦ ∑ j : Fin (r + 1), m j i) = fun i => t i + l i := by
        funext i; simp only [ht, hl, Fin.sum_univ_castSucc]
      have hstep := taylor_add_of_mul_eq_zero N t l
        (fun s hs => hJ s fun a => hspan (hs a)) (fun i j => hm (Fin.last r) i j) _ hfa
      rw [hsum, hstep, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hn'eq a]
      simp only [v, t]
      ring

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSubValueEqSumSqZeroVectorStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_sub_value_eq_sum_sqZero_vector : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  first | exact @GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero | exact GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero | (intros; apply GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShift
open Filter Topology TopologicalSpace TensorProduct
open GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer

theorem evT_map_shA {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
    {R : Type} [CommRing R] [Algebra ℂ R] {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k')
    (y : R ⊗[ℂ] Hol (K.W k)) :
    evT R p hp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h) y) =
      evT R (F.shift l p) (K.maps h p hp) y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.comp_apply, AlgHom.comp_apply, Hol.ev_apply, Hol.ev_apply, Charts.shA_apply, Charts.fn_sh h y hp]
    rfl

theorem close_taylor_shift : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  intro I _ _ g Λ _ F F₀ K K₀ R _ _ J N hJ r m hm hmm hτ l k k' k₀ k₀' h h₀ hW ρ ρ' hρ hρ'
  rcases Classical.em (∃ p, p ∈ K₀.W k₀') with ⟨p₀, hp₀⟩ | hne
  swap
  · have e : ρ'.comp (Charts.sh h) =
        (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ :=
      RingHom.ext fun f ↦ GlobalTheory.tensor_hol_ext_of_values _ _ _ _ fun p hp ↦ (hne ⟨p, hp⟩).elim
    rw [e]
    exact Relation.ReflTransGen.refl
  have h0 : (0 : I → ℂ) ∈ F.V := K.base k' _ (hW p₀ hp₀)
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l _ h0
  obtain ⟨n, hn, hnn, hd⟩ := GlobalTheory.T.taylor_sub_value_eq_sum_sqZero_vector J N hJ r m hm hmm (F.τ l) hτa
  have ht : ∀ i, (fun i ↦ ∑ j, m j i) i ∈ J := fun i ↦ J.sum_mem fun j _ ↦ hm j i
  have htN : ∀ s : Fin (N + 1) → I, ∏ a, (fun i ↦ ∑ j, m j i) (s a) = 0 :=
    fun s ↦ hJ _ fun a ↦ ht (s a)
  have hin : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k :=
    fun p hp ↦ K.maps h _ (hW p hp)
  obtain ⟨-, -, hconst, hgerm, -, -⟩ := taylor_formal_properties N (fun i ↦ ∑ j, m j i)
  refine close_of_sliceTaylor J N hJ _ ht r n hn hnn (K.W k) (K₀.W k₀') (fun p ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hin _ _ ?_ ?_
  · intro f p hp
    refine (hρ' (Charts.sh h f) p hp).trans ?_
    have hc : ContinuousAt (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) 0 := by fun_prop
    have e : (fun z ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      filter_upwards [hc.preimage_mem_nhds ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
      exact Charts.fn_sh h f hz
    rw [hgerm _ _ e, taylor_shear N _ htN f.fn (F.τ l) p.2 hτa (f.analytic _ (hin p hp))]
    simp only [hd]
  · intro f p hp
    refine (evT_map_shA h₀ p hp (ρ f)).trans ?_
    refine (hρ f _ _).trans ?_
    have e : (F₀.shift l p).2 = p.2 + F.τ l 0 := by
      change p.2 + F₀.τ l p.1 = _
      rw [hτ]
    rw [e]
    refine (taylor_shear N _ htN f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hin p hp))).trans ?_
    simp only [hconst, sub_self]

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShiftStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_taylor_shift_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  first | exact @GlobalTheory.AnPer.close_taylor_shift | exact GlobalTheory.AnPer.close_taylor_shift | (intros; apply GlobalTheory.AnPer.close_taylor_shift <;> assumption)
end
end
