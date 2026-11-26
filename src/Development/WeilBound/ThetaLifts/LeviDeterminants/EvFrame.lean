module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.EvModel
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {κ₀ : Type} [Fintype κ₀]
  (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n₁ × Fin d₁)

theorem exists_isEvS (B : Base F E) (Ma : Model σ X W) (M₁ : Model σ X₁ W₁)
    (p q : Matrix (Fin n) (Fin d) (AE F E) → κ₀ → AF F) (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hco : ∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2))
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, p (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, p u = 0 ∧ π u = 0) (hvac : ∀ v b, Ma.vac v (glue ε 0 b) = M₁.vac v b) :
    ∃ e, IsEv B Ma M₁ ι ι' I e ∧ ∃ T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  classical
  obtain ⟨T, hT⟩ := exists_slice ε (0 : κ₀ → mixedEmbedding.mixedSpace F)
  suffices h : _ ∧ _ ∧ _ ∧ T ≠ 0 ∧ _ from
    ⟨LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b, ⟨h.1, h.2.1, h.2.2.1, T, fun v => LinearMap.funLeft ℂ ℂ fun b => glue ε 0 b,
      h.2.2.2.1, h.2.2.2.2⟩, T, hT, _, h.2.2.2.2⟩
  refine ⟨fun Φ hΦ => slice_mem_schA ε 0 hΦ, fun z Φ _ => ?_, fun u hu Φ _ => ?_, ?_⟩
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hj z).1, (hj z).2, glue_dot, glue_add, zero_dotProduct,
      zero_add]
  · funext b
    simp only [LinearMap.funLeft_apply, Darboux.rho, schr, hco, (hI u hu).1, (hI u hu).2, glue_dot, glue_add,
      zero_dotProduct, map_zero, Prod.fst_zero, Prod.snd_zero, add_zero, dotProduct_zero, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · refine ⟨fun h => ?_, fun v => ⟨funext (hvac v), ?_⟩,
      fun f φ _ _ => ?_⟩
    · obtain ⟨f, hf⟩ := exists_schwartz_ne (Fin n × Fin d → mixedEmbedding.mixedSpace F)
      have := hT f 0
      rw [h, glue_zero] at this
      exact hf this.symm
    · refine le_antisymm ?_ fun φ hφ => ?_
      · rintro _ ⟨g, hg, rfl⟩
        exact slice_mem_SB ε 0 hg
      · have h1 : IsOpen (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
        have h2 : IsCompact (Set.univ.pi fun _ : κ₀ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
          isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
        refine ⟨_, box_mem_SB ε h1 h2 hφ, funext fun b => ?_⟩
        rw [LinearMap.funLeft_apply, box_glue, Set.indicator_of_mem (by exact fun _ _ => zero_mem _), Pi.one_apply, one_mul]
    · funext b
      simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hT]
      rw [glue_map ε (evI F)]
      congr 1
      · congr 2
        funext k
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      · refine finprod_congr fun v => ?_
        rw [glue_map ε (evFin F v)]
        simp only [Pi.zero_apply, map_zero]
        rfl

theorem exists_modelS {B : Base F E} {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    {M : Model σ X W} (hM : M.IsGood B.ψ) {M₁ : Model σ X₁ W₁} (hM₁ : M₁.IsGood B.ψ) {κ : Type} [Fintype κ]
    (hcard : n * d = Fintype.card κ * 2 + n₁ * d₁) (b D : Matrix (Fin n) (Fin d) (AE F E) → κ → AE F E)
    (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E)) (hb : IsLinearMap (AF F) b)
    (hD : IsLinearMap (AF F) D) (hπ : IsLinearMap (AF F) π)
    (hH : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z z' =
      b z ⬝ᵥ D z' - cA σ (b z' ⬝ᵥ D z) + hTens (cA σ) (incM F X₁.J) (incM F W₁.J) (π z) (π z'))
    (hrat : ∀ x, (∃ y : κ → E, b (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧
      (∃ y : κ → E, D (incM F x) = fun k => inclR (F := F) (AF F) (y k)) ∧ ∃ x₁, π (incM F x) = incM F x₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (hj : ∀ z, b (incM F ι * z * (incM F ι')ᵀ) = 0 ∧ π (incM F ι * z * (incM F ι')ᵀ) = z)
    (hI : ∀ u ∈ I, b u = 0 ∧ π u = 0)
    (hlat : ∀ v, ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X₁ W₁ v ∧ ∃ δ ∈ latAtV X W v, b δ = 0 ∧ π δ = 0 ∧ D δ = D γ) :
    ∃ (ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁) (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
      (p q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F), Ma.IsGood B.ψ ∧
      (∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)) ∧ (∀ z, b z = 0 → p z = 0) ∧
      (∀ z, D z = 0 → q z = 0) ∧ IsEv B Ma M₁ ι ι' I e ∧
      ∃ T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁), (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  classical
  let ε : Fin n × Fin d ≃ (κ × Fin 2) ⊕ Fin n₁ × Fin d₁ := Fintype.equivOfCardEq (by simp [hcard])
  let β := Module.finBasisOfFinrankEq F E hB.cm.2.2.1
  let βA := Algebra.TensorProduct.basis (AF F) β
  let Tr := Algebra.trace (AF F) (AE F E)
  let p : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => βA.repr (b z k.1) k.2
  let q : Matrix (Fin n) (Fin d) (AE F E) → κ × Fin 2 → AF F := fun z k => -Tr (βA k.2 * D z k.1)
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z') := fun z z' => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  let Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)
      map_add' := fun z z' => by
        rw [Prod.mk_add_mk, glue_add, glue_add, hπ.map_add (f := _), map_add (f := _)]
        congr 2 <;> funext k <;> simp [p, q, hb.map_add (f := _), hD.map_add (f := _), mul_add, add_comm]
      map_smul' := fun c z => by
        rw [Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]
        congr 2 <;> funext k <;> simp [p, q, hb.map_smul, hD.map_smul] }
  have hΦ : ∀ z z', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' =
      (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by
    have h1 := M₁.co.form (π z) (π z')
    show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _
    change Tr _ = _ at h1
    rw [glue_dot, glue_dot, hpq, hpq, hH, mul_add, map_add (f := _), h1, neg_one_mul, map_neg, map_sub, hTr]
    ring
  have hbij : Function.Bijective Φ := by
    have := (bijective_of_symp (Φ ∘ₗ M.co.e.symm.toLinearMap) fun u w => by
      have h1 := M.co.form (M.co.e.symm u) (M.co.e.symm w)
      rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1).comp M.co.e.bijective
    convert this using 1
    funext x
    simp
  let co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
    ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩
  have hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) := fun z => rfl
  have hr : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩, x₁, hx₁⟩ := hrat x
    obtain ⟨u, w, huw⟩ := hM₁.rat x₁
    refine ⟨glue ε (fun k => β.repr (y k.1) k.2) u, glue ε (fun k => -Algebra.trace F E (β k.2 * y' k.1)) w, ?_⟩
    rw [hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]
    congr 2 <;> funext k
    · simp only [p, hy]
      show βA.repr ((1 : AF F) ⊗ₜ[F] y k.1) k.2 = _
      simp [βA, Algebra.TensorProduct.basis_repr_tmul]
    · simp only [q, hy']
      rw [map_neg, ← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), Algebra.TensorProduct.basis_apply]
      rfl
  have hδ : ∀ v, ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, ∀ θ : 𝓞 E,
      B.ψ (Tr (inclR (F := F) (AF F) (θ : E) * (b γ' ⬝ᵥ D γ))) = 1 := fun v γ hγ γ' hγ' θ => by
    obtain ⟨-, δ, h0, h1, h2, h3⟩ := hlat v γ hγ
    have := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v θ 1 (by rw [map_one]; exact one_mem _) γ' hγ' δ h0
    rw [one_mul, symp, hH, h1, h2, h3] at this
    simpa [hTens] using this
  have hv : ∀ v, ∃ φa, Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v φa ∧ ∀ c, φa (glue ε 0 c) = M₁.vac v c := by
    intro v
    refine exists_isVac ε hX hW _ M₁ hr p q π hco v (fun γ hγ => (hlat v γ hγ).1) (fun γ hγ γ' hγ' => ?_)
      (fun θ hθ γ hγ => ?_) (hM₁.vac v)
    · have := hδ v γ hγ γ' hγ' (-1)
      rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one, neg_one_mul, map_neg] at this
      rw [hpq, this]
    · rw [← one_mul (B.ψ _ * B.ψ _), ← hδ v γ hγ γ hγ θ]
      simp only [← AddChar.map_add_eq_mul]
      congr 1
      have h1 : inclR (F := F) (AF F) (θ : E) + cA σ (inclR (F := F) (AF F) (θ : E)) = 1 := by
        rw [GlobalTheory.VacIndic.cA_inclR, ← map_add (f := _), hθ, map_one]
      have h2 : Tr (inclR (F := F) (AF F) (θ : E) * cA σ (b γ ⬝ᵥ D γ)) =
          Tr (b γ ⬝ᵥ D γ) - Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ)) := by
        rw [← hTr, map_mul, cA_cA hB, ← map_sub, eq_sub_of_add_eq' h1, sub_mul, one_mul]
      have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
      show _ * Tr _ = _ + (_ + _ * Tr _)
      rw [hpq, hH, mul_add (inclR (F := F) (AF F) (θ : E)), mul_sub, map_add (f := _), map_sub, h2]
      generalize (⅟(2 : AF F)) = t at h3 ⊢
      linear_combination (Tr (inclR (F := F) (AF F) (θ : E) * (b γ ⬝ᵥ D γ))) * h3
  choose φa hφa hφb using hv
  let S : ∀ v : Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ := fun v => Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let G : Pl (F := F) → Prop := fun v => Model.IsVac (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W) B.ψ v (S v) ∧
    M₁.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let Ma : Model σ X W := ⟨co, fun v => if G v then S v else φa v, M.μ, M.dom⟩
  obtain ⟨e, he⟩ := exists_isEvS ε B Ma M₁ p q π hco ι ι' I
    (fun z => ⟨funext fun k => by simp [p, (hj z).1], (hj z).2⟩)
    (fun u hu => ⟨funext fun k => by simp [p, (hI u hu).1], (hI u hu).2⟩) fun v c => by
      by_cases h : G v
      · show (if G v then S v else φa v) _ = _
        rw [if_pos h, h.2]
        refine Set.indicator_eq_indicator ⟨fun hx i => ?_, fun hx i => ?_⟩ rfl
        · simpa using hx (ε.symm (.inr i))
        · obtain ⟨i, rfl⟩ := ε.symm.surjective i
          rcases i with i | i
          · rw [glue_inl]; exact zero_mem _
          · rw [glue_inr]; exact hx i
      · show (if G v then S v else φa v) _ = _
        rw [if_neg h, hφb]
  refine ⟨ε, Ma, e, p, q, ⟨hr, fun v => ?_, ?_, hM.haar, hM.dom⟩, hco, fun z h => funext fun k => by simp [p, h],
    fun z h => funext fun k => by simp [q, h], he⟩
  · show Model.IsVac _ _ _ (if G v then S v else φa v)
    split_ifs with h
    · exact h.1
    · exact hφa v
  · filter_upwards [GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hr, hM₁.std] with v h1 h2
    exact if_pos ⟨h1, h2⟩

end PositivityTheory.ThKF0
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {α β : Type} [Fintype α] [Fintype β]

def DR (J : Matrix α α S) (z : Matrix α (β ⊕ Fin 2) S) : α → S := fun i => -∑ k, J i k * c (z k (.inr 0))

def DL (J : Matrix β β S) (z : Matrix (α ⊕ Fin 2) β S) : β → S := fun j => ∑ l, J j l * c (z (.inr 0) l)

theorem splitR (hc : ∀ z, c (c z) = z) {J : Matrix α α S} (hJ : ∀ i j, c (J j i) = 1 * J i j) (J' : Matrix β β S)
    (z z' : Matrix α (β ⊕ Fin 2) S) : hTens c J (Matrix.fromBlocks J' 0 0 !![0, 1; -1, 0]) z z' =
      (fun i => z i (.inr 1)) ⬝ᵥ DR c J z' - c ((fun i => z' i (.inr 1)) ⬝ᵥ DR c J z) +
        hTens c J J' (z.submatrix id .inl) (z'.submatrix id .inl) := by
  have e : ∀ z z' : Matrix α (β ⊕ Fin 2) S, (fun i => z i (.inr 1)) ⬝ᵥ DR c J z' =
      -∑ i, ∑ k, z i (.inr 1) * J i k * c (z' k (.inr 0)) := fun z z' => by
    simp only [dotProduct, DR, mul_neg, Finset.mul_sum, mul_assoc, Finset.sum_neg_distrib]
  rw [hTens_plane_right, e, e, map_neg, conj_pair c hc hJ]
  ring

theorem splitL (hc : ∀ z, c (c z) = z) (J : Matrix α α S) {J' : Matrix β β S} (hJ : ∀ i j, c (J' j i) = -1 * J' i j)
    (z z' : Matrix (α ⊕ Fin 2) β S) : hTens c (Matrix.fromBlocks J 0 0 !![0, 1; 1, 0]) J' z z' =
      z (.inr 1) ⬝ᵥ DL c J' z' - c (z' (.inr 1) ⬝ᵥ DL c J' z) + hTens c J J' (z.submatrix .inl id) (z'.submatrix .inl id) := by
  have e : ∀ z z' : Matrix (α ⊕ Fin 2) β S, z (.inr 1) ⬝ᵥ DL c J' z' =
      ∑ i, ∑ k, z (.inr 1) i * J' i k * c (z' (.inr 0) k) := fun z z' => by
    simp only [dotProduct, DL, Finset.mul_sum, mul_assoc]
  rw [hTens_plane_left, e, e, conj_pair c hc hJ]
  ring

theorem gram_herm (hc : ∀ z, c (c z) = z) {J : Matrix α α S} {η : S} (hJ : ∀ i j, c (J j i) = η * J i j) (A : Matrix α β S)
    (i j : β) : c ((Aᵀ * J * A.map c) j i) = η * (Aᵀ * J * A.map c) i j := by
  have e : ∀ i j, (Aᵀ * J * A.map c) i j = ∑ a, ∑ b, A a i * J a b * c (A b j) := fun i j => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [e, e, conj_pair c hc hJ]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem incM_one' {α : Type} [DecidableEq α] : incM F (1 : Matrix α α E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem inc_herm {α : Type} {J : Matrix α α E} {η : ℤ} (hJ : ∀ i j, σ (J j i) = η * J i j) (i j : α) :
    cA σ (incM F J j i) = η * incM F J i j := by
  show cA σ (inclR (F := F) (AF F) _) = _ * inclR (F := F) (AF F) _
  rw [GlobalTheory.VacIndic.cA_inclR, hJ, map_mul, map_intCast]

structure FrOK (σ : E →ₐ[F] E) {m m₁ : ℕ} (Y : Spc F E m) (Y₁ : Spc F E m₁) (H : Plane E m m₁) (η : ℤ)
    (Q : Matrix (Fin m₁ ⊕ Fin 2) (Fin m) E) : Prop where
  pq : incM F (frame H) * incM F Q = 1
  gram : (incM F (frame H))ᵀ * incM F Y.J * (incM F (frame H)).map (cA σ) =
    Matrix.fromBlocks (incM F Y₁.J) 0 0 !![0, 1; (η : AE F E), 0]
  herm : ∀ i j, cA σ (incM F Y.J j i) = η * incM F Y.J i j
  herm₁ : ∀ i j, cA σ (incM F Y₁.J j i) = η * incM F Y₁.J i j
  qx : incM F Q *ᵥ incV F H.x = Pi.single (.inr 0) 1
  qy : incM F Q *ᵥ incV F H.y = Pi.single (.inr 1) 1
  qi : incM F Q * incM F H.ι = Matrix.fromRows 1 0
  low : ∀ u ∈ Y.L, Q.submatrix .inl id *ᵥ u ∈ Y₁.L
  msk : ∀ c s t : ℤ, ∃ A : Matrix (Fin m) (Fin m) E, (∀ u ∈ Y.L, A *ᵥ u ∈ Y.L) ∧
    incM F Q * incM F A = mask (AE F E) m₁ c s t * incM F Q

theorem exists_frOK (hB : B.IsGood σ) {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsFullLattice E) {η : ℤ} (hη : η * η = 1)
    (hJ : ∀ i j, σ (Y.J j i) = η * Y.J i j) : ∃ Q, FrOK σ Y Y₁ H η Q := by
  obtain ⟨Q, hPQ, hQP, hQ⟩ := exists_frame_inv hH hL
  have hA : incM F Q * incM F (frame H) = 1 := by rw [← incM_mul, hQP, incM_one']
  refine ⟨Q, by rw [← incM_mul, hPQ, incM_one'], ?_, inc_herm hJ, inc_herm fun i j => ?_, ?_, ?_, ?_,
    fun u hu => (hQ u hu).1, fun c s t => ⟨_, mask_mem hH hQ c s t, ?_⟩⟩
  · have h := congrArg (incM F) (frame_gram hB hH (η := η) (by exact_mod_cast congrArg (Int.cast : ℤ → E) hη) hJ)
    rw [incM_mul, incM_mul] at h
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · ext (i | i) (j | j)
      · rfl
      · simp [incM]
      · simp [incM]
      · fin_cases i <;> fin_cases j <;> simp [incM]
  · rw [← hH.gram]
    exact gram_herm σ (conj_conj hB) hJ _ _ _
  · funext i
    have := congrFun (congrFun hA i) (.inr 0)
    rw [Matrix.one_apply, ← Pi.single_apply (Sum.inr 0) (1 : AE F E) i] at this
    exact this
  · funext i
    have := congrFun (congrFun hA i) (.inr 1)
    rw [Matrix.one_apply, ← Pi.single_apply (Sum.inr 1) (1 : AE F E) i] at this
    exact this
  · ext i j
    refine (congrFun (congrFun hA i) (.inl j)).trans ?_
    rcases i with i | i <;> simp [Matrix.one_apply]
  · rw [incM_mul, incM_mul, incM_mask, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.one_mul]

theorem frOK_herm (hB : B.IsGood σ) {m m₁ i₀ i₁ r s : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsHerm σ B r s) : ∃ Q, FrOK σ Y Y₁ H 1 Q :=
  exists_frOK hB hH hY.lat rfl fun i j => by simp [hY.herm]

theorem frOK_skew (hB : B.IsGood σ) {m m₁ i₀ i₁ r s : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hY : Y.IsSkew σ B r s) : ∃ Q, FrOK σ Y Y₁ H (-1) Q :=
  exists_frOK hB hH hY.lat rfl fun i j => by simp [hY.skew]

theorem hTens_fr {α β α' β' : Type} [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq α] [DecidableEq β]
    (J : Matrix α α (AE F E)) (J' : Matrix β β (AE F E)) {P : Matrix α α' (AE F E)} {Q : Matrix α' α (AE F E)} (h : P * Q = 1)
    {P' : Matrix β β' (AE F E)} {Q' : Matrix β' β (AE F E)} (h' : P' * Q' = 1) (z z' : Matrix α β (AE F E)) :
    hTens (cA σ) J J' z z' = hTens (cA σ) (Pᵀ * J * P.map (cA σ)) (P'ᵀ * J' * P'.map (cA σ)) (Q * z * Q'ᵀ) (Q * z' * Q'ᵀ) := by
  have e : ∀ z : Matrix α β (AE F E), P * (Q * z * Q'ᵀ) * P'ᵀ = z := fun z => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h',
      Matrix.transpose_one, Matrix.mul_one]
  rw [← hTens_mul, e, e]

theorem w_vec {α β α' β' S : Type} [CommRing S] [Fintype α] [Fintype β] (Q : Matrix α' α S) (Q' : Matrix β' β S) (x : α → S)
    (y : β → S) : Q * Matrix.vecMulVec x y * Q'ᵀ = Matrix.vecMulVec (Q *ᵥ x) (Q' *ᵥ y) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem w_mul {α β α' β' a b S : Type} [CommRing S] [Fintype α] [Fintype β] [Fintype a] [Fintype b] (Q : Matrix α' α S)
    (Q' : Matrix β' β S) (A : Matrix α a S) (A' : Matrix β b S) (z : Matrix a b S) :
    Q * (A * z * A'ᵀ) * Q'ᵀ = Q * A * z * (Q' * A')ᵀ := by
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem w_msk {α β α' β' S : Type} [CommRing S] [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] {Q : Matrix α' α S}
    {Q' : Matrix β' β S} {A : Matrix α α S} {A' : Matrix β β S} {m : Matrix α' α' S} {m' : Matrix β' β' S}
    (h : Q * A = m * Q) (h' : Q' * A' = m' * Q')
    (z : Matrix α β S) : Q * (A * z * A'ᵀ) * Q'ᵀ = m * (Q * z * Q'ᵀ) * m'ᵀ := by
  rw [w_mul, h, h']
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem w_inc {α β α' β' : Type} [Fintype α] [Fintype β] (Q : Matrix α' α E) (Q' : Matrix β' β E) (x : Matrix α β E) :
    incM F Q * incM F x * (incM F Q')ᵀ = incM F (Q * x * Q'ᵀ) := by
  rw [incM_mul, incM_mul]
  rfl

theorem DR_inc {α β : Type} [Fintype α] (J : Matrix α α E) (x : Matrix α (β ⊕ Fin 2) E) :
    DR (cA σ) (incM F J) (incM F x) = fun k => inclR (F := F) (AF F) (DR σ J x k) := by
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [DR, map_neg, map_sum, map_mul]
  rfl

theorem DL_inc {α β : Type} [Fintype β] (J : Matrix β β E) (x : Matrix (α ⊕ Fin 2) β E) :
    DL (cA σ) (incM F J) (incM F x) = fun k => inclR (F := F) (AF F) (DL σ J x k) := by
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [DL, map_sum, map_mul]
  rfl

end PositivityTheory.ThKF0
