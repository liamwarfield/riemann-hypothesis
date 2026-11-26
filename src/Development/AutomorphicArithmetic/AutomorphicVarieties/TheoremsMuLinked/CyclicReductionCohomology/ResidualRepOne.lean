module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualNO

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmegaConstruction
@[reducible] noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.Om :
    (O : Type) → [inst : CommRing O] → [IsLocalRing O] → ℕ → Type :=
    fun (O : Type) [CommRing O] [IsLocalRing O] (m : ℕ) ↦ O ⧸ IsLocalRing.maximalIdeal O ^ m

noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.red :
    {O : Type} →
      [inst : CommRing O] →
        [inst_1 : IsLocalRing O] →
          {n : ℕ} → (m : ℕ) → Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.OmegaConstruction.Om O m) :=
    fun {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (Z : Matrix (Fin n) (Fin n) O) ↦
      Z.map (⇑(Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) : O → O ⧸ IsLocalRing.maximalIdeal O ^ m)

theorem UpperTheory.Reformulated.B.OmegaConstruction.red_sub :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O),
      UpperTheory.Reformulated.B.OmegaConstruction.red m (A - B) = UpperTheory.Reformulated.B.OmegaConstruction.red m A - UpperTheory.Reformulated.B.OmegaConstruction.red m B := by
  intro O _ _ n m A B
  ext i j
  exact map_sub (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) (A i j) (B i j)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCyclic
open Matrix

private theorem eig_sum_zero {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O) (hal : Function.Injective al)
    (u : Fin n → Fin n → O) (hu : ∀ i, A.mulVec (u i) = al i • u i) (hs : ∑ i, u i = 0) :
    ∀ i, u i = 0 := by
  have hk : ∀ k : ℕ, ∑ i, al i ^ k • u i = 0 := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k ih =>
      have h := congrArg A.mulVec ih
      rw [Matrix.mulVec_zero, Matrix.mulVec_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hu, smul_smul, pow_succ]
  intro i
  funext j
  have h : (fun i => u i j) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hal
    intro k
    have := congrFun (hk k) j
    simpa [Finset.sum_apply, mul_comm] using this
  exact congrFun h i

theorem UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc :
    ∀ {O : Type} [inst : CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O),
      Function.Injective al →
        A.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : O → Polynomial O) (al i)) →
          ∃ (v : Fin n → O),
            ∀ (Y : Matrix (Fin n) (Fin n) O),
              A * Y = Y * A → Y.mulVec v = (0 : Fin n → O) → Y = (0 : Matrix (Fin n) (Fin n) O) := by
  intro O _ _ n A al hal hc
  have hw : ∀ i, ∃ w : Fin n → O, w ≠ 0 ∧ A.mulVec w = al i • w := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (al i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hc, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨w, hw0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hw
    rw [← hw]
    funext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose w hw0 hw using hw
  refine ⟨∑ i, w i, fun Y hY hv => ?_⟩
  have hYw : ∀ i, Y.mulVec (w i) = 0 := by
    apply eig_sum_zero A al hal (fun i => Y.mulVec (w i))
    · intro i
      rw [Matrix.mulVec_mulVec, hY, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
    · rw [← Matrix.mulVec_sum, hv]
  have hdet : (Matrix.of w).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have h := eig_sum_zero A al hal (fun i => c i • w i)
      (fun i => by rw [Matrix.mulVec_smul, hw, smul_comm])
      (by
        funext j
        have := congrFun hc j
        simpa [Matrix.vecMul, dotProduct, Finset.sum_apply] using this)
    funext i
    exact (smul_eq_zero.mp (h i)).resolve_right (hw0 i)
  ext r j
  have h : Y r = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    have := congrFun (hYw i) r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  exact congrFun h j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PsiCont
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OneCntO
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private def chRep {A D : Type} (M : Type) [CommRing A] [Group D] [AddCommGroup M] [Module A M] (χ : D →* Aˣ) :
    Representation A D M where
  toFun g := (χ g : A) • LinearMap.id
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp [smul_smul, mul_comm]

private theorem chRep_apply {A D M : Type} [CommRing A] [Group D] [AddCommGroup M] [Module A M] (χ : D →* Aˣ)
    (g : D) (y : M) : chRep M χ g y = (χ g : A) • y := rfl

private theorem ker_le {A : Type} [CommRing A] (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] (a : A)
    (h : J ≤ Ideal.span {a}) (S : Submodule A (A ⧸ I)) (hS : ∀ y ∈ S, a • y = 0) :
    Nat.card S ≤ Nat.card (A ⧸ J) := by
  let f : (A ⧸ I) →ₗ[A] (A ⧸ I) := a • LinearMap.id
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at h1
  have h3 : Nat.card (LinearMap.ker f) = Nat.card ((A ⧸ I) ⧸ LinearMap.range f) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := LinearMap.range f))
    rw [← h2, mul_comm, ← h1]
  have h4 : Nat.card S ≤ Nat.card (LinearMap.ker f) :=
    Nat.card_le_card_of_injective _ (Submodule.inclusion_injective (show S ≤ LinearMap.ker f from hS))
  let p : A →ₗ[A] ((A ⧸ I) ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.comp (Submodule.mkQ I)
  have hp : J ≤ LinearMap.ker p := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 (h hy)
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨Submodule.mkQ I c, ?_⟩
    exact (map_smul (Submodule.mkQ I) a c).symm
  have hs : Function.Surjective (Submodule.liftQ J p hp) := by
    intro y
    obtain ⟨c, rfl⟩ := ((Submodule.mkQ_surjective (LinearMap.range f)).comp (Submodule.mkQ_surjective I)) y
    exact ⟨Submodule.mkQ J c, rfl⟩
  exact h4.trans (h3.le.trans (Nat.card_le_card_of_surjective _ hs))

theorem UpperTheory.V.Th.oneCntO :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (ε : D →* ℤ_[l]ˣ) (d : ℕ) (χ : D →* Oˣ), LocCnt D ε d → AdicCont (maximalIdeal O) (fun g => (χ g : O)) → (∃ g, (χ g : O) ≠ algebraMap ℤ_[l] O (ε g : ℤ_[l])) → ∃ C : ℕ, ∀ m, {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.Finite ∧ {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.ncard ≤ Nat.card (ResidueField O) ^ (m * (1 + d) + C) := by
  intro l _ O _ _ _ _ _ D _ _ _ ε d χ hL hχ ⟨g₀, hg₀⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨C, hC⟩ := IsDiscreteValuationRing.associated_pow_irreducible (sub_ne_zero.2 hg₀) hϖ
  refine ⟨C, fun m => ?_⟩
  obtain ⟨hfin, hcard, -, -, hlc⟩ := (omFacts l O).2 m
  obtain ⟨hfinC, hcardC, -⟩ := (omFacts l O).2 C
  obtain ⟨k, τ, hk, hτ, hlin⟩ := pairO l O m
  let e : D →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp ε
  have he : ∀ g, (e g : O) = algebraMap ℤ_[l] O (ε g : ℤ_[l]) := fun _ => rfl
  let χ' : D →* Oˣ := e * χ⁻¹
  have hχ' : ∀ g, (χ g : O) * χ' g = e g := fun g => by
    rw [← Units.val_mul]
    congr 1
    simp [χ']
  let b : Om O m →+ Om O m →+ ZMod (l ^ k) := (AddMonoidHom.mul (R := Om O m)).compr₂ τ
  have hb : ∀ y z, b y z = τ (y * z) := fun _ _ => rfl
  have hLC : LC (chRep (Om O m) χ) := fun y =>
    (hlc D _ hχ).comp (fun u => u * y)
  have hD : DualPair k ε (chRep (Om O m) χ) (chRep (Om O m) χ') b :=
    { left := fun y h => hτ y h
      right := fun y h => hτ y fun z => by rw [mul_comm]; exact h z
      equiv := fun g y z => by
        rw [hb, hb, chRep_apply, chRep_apply, smul_mul_smul_comm, hχ', he, Algebra.smul_def, hlin] }
  obtain ⟨hf, hc⟩ := hL k hk O (Om O m) (Om O m) _ _ b hLC hD
  have hinv : Nat.card (chRep (Om O m) χ').invariants ≤ Nat.card (Om O C) := by
    refine ker_le _ _ ((χ g₀ : O) - algebraMap ℤ_[l] O (ε g₀ : ℤ_[l])) ?_ _ fun y hy => ?_
    · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_span_singleton.2 hC.dvd)
    · have h1 : (χ' g₀ : O) • y = y := hy g₀
      rw [← he, ← hχ', sub_smul, mul_smul, h1, sub_self]
  refine ⟨hf, ?_⟩
  have h2 : {z : D → Om O m | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + (χ g : O) • z h}.ncard =
      Nat.card (Zl (chRep (Om O m) χ)) := rfl
  rw [h2, hc, hcard, ← pow_mul, pow_add, ← hcardC]
  exact Nat.mul_le_mul_left _ hinv
end

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_lt' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  simpa using this

private theorem card_le' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 ≤ p.2} = n + n.choose 2 := by
  rw [← card_lt' n]
  have e : {p : Fin n × Fin n // p.1 ≤ p.2} ≃ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2} :=
    { toFun := fun p => if h : p.1.1 < p.1.2 then .inr ⟨p.1, h⟩ else .inl p.1.1
      invFun := Sum.elim (fun i => ⟨(i, i), le_rfl⟩) fun p => ⟨p.1, p.2.le⟩
      left_inv := fun p => by
        by_cases h : p.1.1 < p.1.2
        · simp [h]
        · simp only [h, dite_false, Sum.elim_inl]
          exact Subtype.ext (Prod.ext rfl (le_antisymm p.2 (not_lt.1 h)))
      right_inv := by
        rintro (i | p)
        · simp
        · simp [p.2] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
private theorem filt_ht {Z Y ι : Type} [AddCommGroup Z] [AddCommGroup Y] [Fintype ι] (ht : ι → ℕ) (f : ι → Z →+ Y)
    (P : ι → Set Y) (h0 : ∀ z, (∀ i, f i z = 0) → z = 0) (hP : ∀ i, (P i).Finite)
    (hf : ∀ i z, (∀ j, ht j < ht i → f j z = 0) → f i z ∈ P i) : Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  let e₀ := (Fintype.equivFin ι).symm
  let e := (Tuple.sort (ht ∘ e₀)).trans e₀
  have hm : Monotone (ht ∘ e) := Tuple.monotone_sort (ht ∘ e₀)
  rw [← e.prod_comp]
  refine filtCount Z Y _ (fun i => f (e i)) (fun i => P (e i)) (fun z hz => h0 z fun i => ?_) (fun i => hP _)
    fun i z hz => hf _ z fun j hj => ?_
  · obtain ⟨i, rfl⟩ := e.surjective i
    exact hz i
  · obtain ⟨j, rfl⟩ := e.surjective j
    exact hz j (hm.reflect_lt hj)

private theorem conj_entry {R : Type} [CommRing R] {n : ℕ} (T B T' : Matrix (Fin n) (Fin n) R)
    (hT : ∀ i j, j < i → T i j = 0) (hT' : ∀ i j, j < i → T' i j = 0) (i j : Fin n)
    (hB : ∀ p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → B p q = 0) : (T * B * T') i j = T i i * B i j * T' j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro p _ hp
    by_cases c : p < i
    · rw [hT i p c, zero_mul]
    · rw [hB p j (not_lt.1 c) le_rfl (.inl hp), mul_zero]
  · simp
  · intro q _ hq
    by_cases c : j < q
    · rw [hT' q j c, mul_zero]
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro p _
      by_cases c' : p < i
      · rw [hT i p c', zero_mul]
      · rw [hB p q (not_lt.1 c') (not_lt.1 c) (.inr hq), mul_zero]
  · simp

private theorem adic_mul {D R : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} {f f' : D → R}
    (h : AdicCont I f) (h' : AdicCont I f') : AdicCont I fun g => f g * f' g := fun N => by
  simp only [map_mul]
  exact (h N).mul (h' N)

private theorem adic_sum {D R ι : Type} [TopologicalSpace D] [CommRing R] {I : Ideal R} (s : Finset ι) {f : ι → D → R}
    (h : ∀ i, AdicCont I (f i)) : AdicCont I fun g => ∑ i ∈ s, f i g := fun N => by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsLocallyConstant.of_constant _ fun _ _ => rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, map_add (f := _)]
    exact (h i N).add ih

section

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  (y : Pt G0.frame O n) (v : L.Vl)

private theorem psi_cont (i : Fin n) : AdicCont (maximalIdeal O) fun g : L.Gv v => (y.ψ v i g : O) := by
  have e : (fun g : L.Gv v => (y.ψ v i g : O)) = fun g => ∑ q, (∑ p, (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) i p *
      mat y.ρ (G0.φ v g) p q) * (y.w v : Matrix (Fin n) (Fin n) O) q i := funext fun g => ((y.tri v g).2 i).symm
  rw [e]
  exact adic_sum _ fun q => adic_mul (adic_sum _ fun p => adic_mul (fun N => IsLocallyConstant.const _)
    fun N => (y.cont p q N).comp_continuous (G0.φ_cont v)) fun N => IsLocallyConstant.const _

private noncomputable def cj (m : ℕ) (Z : Mm O n m) : Mm O n m :=
  red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z * red m (y.w v : Matrix (Fin n) (Fin n) O)

private theorem i2 (m : ℕ) :
    red m (y.w v : Matrix (Fin n) (Fin n) O) * red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
  rw [← red_mul, Units.mul_inv, red_one]

private theorem cj_rho (m : ℕ) (g : L.Gv v) : (∀ i j, j < i → cj y v m (y.ρ0 m (G0.φ v g)) i j = 0) ∧
    ∀ i, cj y v m (y.ρ0 m (G0.φ v g)) i i = algebraMap O (Om O m) (y.ψ v i g : O) := by
  have e : cj y v m (y.ρ0 m (G0.φ v g)) =
      red m (((y.w v)⁻¹ * y.ρ (G0.φ v g) * y.w v : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    rw [Units.val_mul, Units.val_mul, red_mul, red_mul]; rfl
  rw [e]
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · exact (congrArg (Ideal.Quotient.mk _) ((y.tri v g).1 i j h)).trans (map_zero _)
  · exact congrArg (Ideal.Quotient.mk _) ((y.tri v g).2 i)

private noncomputable def crd (m : ℕ) (i j : Fin n) : Zbor y m v →+ (L.Gv v → Om O m) :=
  AddMonoidHom.mk' (fun β g => cj y v m (β.1 g) i j) fun β β' => funext fun g => by
    simp only [cj, AddSubgroup.coe_add, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]

private theorem crd_coc (m : ℕ) (i j : Fin n) (β : Zbor y m v)
    (hB : ∀ g p q, i ≤ p → q ≤ j → (p ≠ i ∨ q ≠ j) → cj y v m (β.1 g) p q = 0) :
    IsLocallyConstant (crd y v m i j β) ∧ ∀ g h, crd y v m i j β (g * h) =
      crd y v m i j β g + ((y.ψ v i g : O) * (y.ψ v j g⁻¹ : O)) • crd y v m i j β h := by
  refine ⟨β.2.1.comp fun Z : Mm O n m => cj y v m Z i j, fun g h => ?_⟩
  have e : cj y v m (β.1 (g * h)) = cj y v m (β.1 g) +
      cj y v m (y.ρ0 m (G0.φ v g)) * cj y v m (β.1 h) * cj y v m (y.ρ0 m (G0.φ v g⁻¹)) := by
    have i3 : ∀ M : Mm O n m, red m (y.w v : Matrix (Fin n) (Fin n) O) *
        (red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * M) = M := fun M => by
      rw [← mul_assoc, i2, one_mul]
    rw [β.2.2.1 g h, map_inv]
    simp only [cj, mul_add, add_mul, mul_assoc, i3]
  change cj y v m (β.1 (g * h)) i j = cj y v m (β.1 g) i j + _ • cj y v m (β.1 h) i j
  rw [e, Matrix.add_apply, conj_entry _ _ _ (cj_rho y v m g).1 (cj_rho y v m g⁻¹).1 i j (hB h), (cj_rho y v m g).2,
    (cj_rho y v m g⁻¹).2, Algebra.smul_def, map_mul]
  ring

end

theorem UpperTheory.V.Th.locVO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (v : L.Vl) (d : ℕ), LocCnt (L.Gv v) (G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v))) d → (∃ g, algebraMap ℤ_[l] O (G0.ε (G0.φ v g) : ℤ_[l]) ≠ 1) → ∃ C : ℕ, ∀ m, Finite (Zbor y m v) ∧ Nat.card (Zbor y m v) ≤ Nat.card (ResidueField O) ^ (m * ((n + n.choose 2) * (1 + d)) + C) := by
  intro l _ L G0 O _ _ _ _ _ n y v d hL hε
  let P : ∀ m, {p : Fin n × Fin n // p.1 ≤ p.2} → Set (L.Gv v → Om O m) := fun m t =>
    {z | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ((y.ψ v t.1.1 g : O) * (y.ψ v t.1.2 g⁻¹ : O)) • z h}
  have hP : ∀ t, ∃ C : ℕ, ∀ m, (P m t).Finite ∧ (P m t).ncard ≤ Nat.card (ResidueField O) ^ (m * (1 + d) + C) := by
    rintro ⟨⟨i, j⟩, hij⟩
    let χ : L.Gv v →* Oˣ := y.ψ v i * (y.ψ v j)⁻¹
    have e : ∀ g, ((χ g : Oˣ) : O) = (y.ψ v i g : O) * (y.ψ v j g⁻¹ : O) := fun g => by
      show ((y.ψ v i g * (y.ψ v j g)⁻¹ : Oˣ) : O) = _
      rw [map_inv, Units.val_mul]
    have h := oneCntO l O (L.Gv v) _ d χ hL ?_ ?_
    · simpa only [e] using h
    · simp only [e]
      exact adic_mul (psi_cont y v i) fun N => (psi_cont y v j N).comp_continuous continuous_inv
    · rcases hij.lt_or_eq with hlt | heq
      · by_contra c
        push Not at c
        refine y.N1 v i j hlt (MonoidHom.ext fun g => ?_)
        have c' : y.ψ v i g * (y.ψ v j g)⁻¹ = G0.frame.eps O O (G0.φ v g) := Units.ext (c g)
        show y.ψ v i g = y.ψ v j g * G0.frame.eps O O (G0.φ v g)
        rw [← c', mul_comm, inv_mul_cancel_right]
      · obtain ⟨g, hg⟩ := hε
        refine ⟨g, fun c => hg ?_⟩
        have hij' : i = j := heq
        subst hij'
        have c1 : χ g = 1 := mul_inv_cancel (y.ψ v i g)
        rw [c1] at c
        exact c.symm
  choose C hC using hP
  refine ⟨∑ t, C t, fun m => ?_⟩
  refine And.imp_right (fun h2 => ?_) <| filt_ht (fun t : {p : Fin n × Fin n // p.1 ≤ p.2} => (t.1.2 : ℕ) - t.1.1)
    (fun t => crd y v m t.1.1 t.1.2) (P m) (fun β h => ?_) (fun t => (hC t m).1) fun t β h => ?_
  · refine h2.trans ((Finset.prod_le_prod' fun t _ => (hC t m).2).trans (le_of_eq ?_))
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_le', smul_eq_mul]
    congr 1
    ring
  · refine Subtype.ext (funext fun g => ?_)
    have e0 : cj y v m (β.1 g) = 0 := Matrix.ext fun p q => by
      by_cases c : q < p
      · exact β.2.2.2 g p q c
      · exact congrFun (h ⟨(p, q), not_lt.1 c⟩) g
    have e1 := congrArg (fun M => red m (y.w v : Matrix (Fin n) (Fin n) O) * M *
      red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)) e0
    simp only [cj, ← mul_assoc, i2, one_mul, mul_zero, zero_mul] at e1
    rwa [mul_assoc, i2, mul_one] at e1
  · exact crd_coc y v m t.1.1 t.1.2 β fun g p q c1 c2 c3 => by
      by_cases c : q < p
      · exact β.2.2.2 g p q c
      · refine congrFun (h ⟨(p, q), not_lt.1 c⟩ ?_) g
        simp only [Fin.le_def, Fin.lt_def, ne_eq, Fin.ext_iff] at c c1 c2 c3 ⊢
        omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.ExistsCyc
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem exists_cyc {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (al : Fin n → O)
    (ha : Function.Injective al) (hc : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    ∃ v : Fin n → O, ∀ Y : Matrix (Fin n) (Fin n) O, A * Y = Y * A → Y *ᵥ v = 0 → Y = 0 :=
  _root_.UpperTheory.Reformulated.B.ExistsCyclic.exists_cyc A al ha hc

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B :=
  _root_.UpperTheory.Reformulated.B.OmegaConstruction.red_sub m A B

theorem UpperTheory.V.Th.h0qO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (σ : G0.G₀) (al : Fin n → O), Function.Injective al → (mat y.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ m, {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y}.ncard ≤ Nat.card (ResidueField O) ^ (m * n + C) := by
  intro l _ L G0 O _ _ _ hO _ n y σ al ha hc
  obtain ⟨v, hv⟩ := exists_cyc _ al ha hc
  let Φ : Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O :=
    (LinearMap.mulRight O (mat y.ρ σ⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ σ)) - LinearMap.id
  have hΦ : ∀ Y, Φ Y = mat y.ρ σ * Y * mat y.ρ σ⁻¹ - Y := fun _ => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n Unit (fun _ => Φ)
  have hinv : mat y.ρ σ⁻¹ * mat y.ρ σ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hr : Module.finrank O (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) ≤ n := by
    let f : (⨅ _ : Unit, LinearMap.ker Φ : Submodule O (Matrix (Fin n) (Fin n) O)) →ₗ[O] (Fin n → O) :=
      { toFun := fun Y => Y.1 *ᵥ v
        map_add' := fun a b => by simp [add_mulVec]
        map_smul' := fun c a => by simp [smul_mulVec] }
    have hf : Function.Injective f := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro Y e
      apply Subtype.ext
      refine hv Y.1 ?_ e
      have h1 : Φ Y.1 = 0 := (Submodule.mem_iInf _).mp Y.2 ()
      rw [hΦ, sub_eq_zero] at h1
      calc mat y.ρ σ * Y.1 = mat y.ρ σ * Y.1 * mat y.ρ σ⁻¹ * mat y.ρ σ := by
            rw [Matrix.mul_assoc _ _ (mat y.ρ σ), hinv, Matrix.mul_one]
        _ = _ := by rw [h1]
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  refine ⟨C, fun m => ?_⟩
  have hs : {Y : Mm O n m | y.ρ0 m σ * Y * y.ρ0 m σ⁻¹ = Y} =
      {Y : Mm O n m | ∃ Y', red m Y' = Y ∧ ∀ _ : Unit, red m (Φ Y') = 0} := by
    ext Y
    constructor
    · intro hY
      choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)
      have e : red m (Matrix.of Y') = Y := by
        ext i j
        exact hY' i j
      refine ⟨Matrix.of Y', e, fun _ => ?_⟩
      rw [hΦ, red_sub', red_mul', red_mul', e]
      exact sub_eq_zero.mpr hY
    · rintro ⟨Y', e, h⟩
      have h1 := h ()
      rw [hΦ, red_sub', red_mul', red_mul', e] at h1
      exact sub_eq_zero.mp h1
  rw [hs]
  refine (hC m).trans ?_
  obtain ⟨-, hfin, -⟩ := hO
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.add_le_add_right (Nat.mul_le_mul_left m hr) C)
end

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_inv_le {A M Γ : Type} [CommRing A] [AddCommGroup M] [Module A M] [Finite M] [Group Γ]
    (r : Representation A Γ M) (S : Set M)
    (h : ∀ y : M, (∀ g, r g y = y) → y ∈ S) : Nat.card r.invariants ≤ S.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective (fun y : r.invariants => (⟨y.1, h y.1 y.2⟩ : S))
    fun a b e => Subtype.ext (congrArg (fun z : S => z.1) e)

private theorem cancel_pow {s K u w : ℕ} (hK : 0 < K) (h : s * K ^ u ≤ K ^ (w + u)) : s ≤ K ^ w := by
  rw [pow_add] at h
  exact Nat.le_of_mul_le_mul_right h (pow_pos hK u)

private theorem sum_exp {V : Type} [Fintype V] (m n ν d q c₁ c₂ c₀ : ℕ) (dv C : V → ℕ) (Cq : Fin q → ℕ)
    (h2 : ∑ v, dv v = d) :
    c₁ + c₂ + ∑ v, (m * ((n + ν) * (1 + dv v)) + C v) +
      ∑ j : Option (Fin q), (j.elim c₀ fun i => m * n + Cq i) =
    (m * (n * d + n * q) + (c₁ + c₂ + c₀ + ∑ v, C v + ∑ j, Cq j)) + (m * (n + ν) * Fintype.card V + m * ν * d) := by
  rw [Fintype.sum_option]
  simp only [Option.elim, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  ring

private theorem residual_rep_one {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} (y : Pt G0.frame O n) (m : ℕ) : y.ρ0 m 1 = 1 := by
  simp [Pt.ρ0, red, mat]

private theorem residual_rep_mul {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} (y : Pt G0.frame O n) (m : ℕ) (g h : G0.G₀) :
    y.ρ0 m (g * h) = y.ρ0 m g * y.ρ0 m h := by
  simp [Pt.ρ0, red, mat, Matrix.map_mul]

theorem UpperTheory.V.Th.b1absO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (al : Fin T.q → Fin n → O) (d : ℕ) (D0 : Subgroup G0.G₀) (_ : Sys T d D0), l ≠ 2 → PhiCond G0.Γ l → (∀ v, ∃ g, algebraMap ℤ_[l] O (G0.ε (G0.φ v g) : ℤ_[l]) ≠ 1) → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → y.N4 D0 → Eig y T al → DetO y (Set.range T.sg) → B1 y T (n * d + n * T.q) := by
  intro l _ L G0 T O _ _ _ _ _ n y al d D0 S hl hΦ hε hPL hN4 hE hD
  classical
  have hloc : ∀ v : L.Vl, LocCnt (L.Gv v) (G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v))) (S.dv v) := fun v => by
    have h1 := (S.counts 0).locV v
    rw [S.dv_eq 0] at h1
    have h2 : (T.GN 0).ε.comp ((S.a 0).ι (.inl v)) = G0.ε.comp (G0.η.ker.subtype.comp (G0.φ v)) := by
      refine MonoidHom.ext fun g => ?_
      show (T.GN 0).ε ((T.GN 0).φ v g) = G0.ε (G0.φ v g)
      rw [← (T.h 0).φ v g, (T.h 0).ε]
    exact h2 ▸ h1
  have hc : G0.ε G0.c = -1 := by rw [← (T.h 0).c, (T.h 0).ε]; exact (S.a 0).c_ε
  choose Cv hCv using fun v : L.Vl => locVO l L G0 O n y v (S.dv v) (hloc v) (hε v)
  obtain ⟨c₁, hc₁⟩ := h0GO l L G0 O n y hl
  obtain ⟨c₀, hc₀⟩ := h0v0O l L G0 O n y D0 hN4
  choose Cq hCq using fun j : Fin T.q => h0qO l L G0 O n y (T.sg j) (al j) (hE j).1 (hE j).2
  obtain ⟨c₂, hc₂⟩ := dualNO l L G0 T O n y hl hc hΦ hPL hD
  refine ⟨c₁ + c₂ + c₀ + ∑ v, Cv v + ∑ j, Cq j, fun m => ?_⟩
  filter_upwards [hc₂ m, phEqO l L G0 T O n y m hΦ hPL] with N hN hP
  haveI : Finite (Om O m) := ((omFacts l O).2 m).1
  have hK : 0 < Nat.card (ResidueField O) := by
    have h1 := ((omFacts l O).2 1)
    haveI := h1.1
    have h2 := h1.2.1
    rw [pow_one] at h2
    rw [← h2]
    exact Nat.card_pos
  obtain ⟨⟨rep, hr⟩, ⟨rep', hr'⟩, -⟩ := adExP l L (T.GN N) G0 (T.h N) O n y m
  have hm : ∀ g, y.ρm (T.h N) m g = y.ρ0 m ((T.h N).p₀ g) := fun _ => rfl
  have he : ∀ g, epsm O (T.GN N) m g = epsm O G0 m ((T.h N).p g) := fun g => by
    simp only [epsm, (T.h N).ε]
  have key := oneLevelO l L (T.GN N) G0 (T.h N) O n y m T.q d (S.a N) rep rep'
    (fun v => m * ((n + n.choose 2) * (1 + S.dv v)) + Cv v)
    (fun j => j.elim c₀ fun i => m * n + Cq i) c₁ c₂ hl (S.counts N) hr hr' (fun v => hCv v m) ?_ ?_ ?_
  · have h2 : ∑ v, S.dv v = d := by rw [← S.dv_eq N]; exact (S.a N).sum_dv
    have k2 := key.2
    rw [sum_exp m n (n.choose 2) d T.q c₁ c₂ c₀ S.dv Cv Cq h2] at k2
    exact ⟨key.1, cancel_pow hK k2⟩
  · rintro (_ | j)
    · refine le_trans (card_inv_le _ _ ?_) (hc₀ m)
      intro Y hy g hg
      rw [← S.d0 N] at hg
      obtain ⟨γ, rfl⟩ := hg
      have e1 := hr'.1 ((S.a N).φq none γ) Y
      have e2 : rep' ((S.a N).φq none γ : (T.GN N).G₀) Y = Y := hy γ
      rw [e2, hm, hm, he, map_inv] at e1
      exact e1.symm
    · refine le_trans (card_inv_le _ _ ?_) (hCq j m)
      intro Y hy
      obtain ⟨γ, hγ⟩ := S.ph N j
      have e1 := hr'.1 (T.ph N j) Y
      have e2 : rep' (T.ph N j : (T.GN N).G₀) Y = Y := by rw [← hγ]; exact hy γ
      rw [e2, hm, hm, he, map_inv] at e1
      have e3 : y.ρ0 m ((T.h N).p₀ (T.ph N j))⁻¹ = y.ρ0 m (T.sg j)⁻¹ := by
        have a1 := residual_rep_mul y m ((T.h N).p₀ (T.ph N j))⁻¹ ((T.h N).p₀ (T.ph N j))
        have a2 := residual_rep_mul y m (T.sg j) (T.sg j)⁻¹
        rw [inv_mul_cancel, residual_rep_one, (hP j).1] at a1
        rw [mul_inv_cancel, residual_rep_one] at a2
        exact left_inv_eq_right_inv a1.symm a2.symm
      rw [(hP j).1, (hP j).2.1, one_smul, e3] at e1
      exact e1.symm
  · refine le_trans (card_inv_le _ _ ?_) (hc₁ m)
    intro Y hy
    refine ⟨?_, fun g => ?_⟩
    · have e1 := hr.2 Y
      have e2 : rep (T.GN N).frame.c Y = Y := hy _
      rw [e2, one_smul] at e1
      exact e1
    · obtain ⟨γ, hγ⟩ := (T.h N).surj g
      have hγm : γ ∈ (T.GN N).η.ker := by
        rw [MonoidHom.mem_ker, ← (T.h N).η, hγ]; exact g.2
      have e0 : (T.h N).p₀ ⟨γ, hγm⟩ = g := Subtype.ext hγ
      have e1 := hr.1 ⟨γ, hγm⟩ Y
      have e2 : rep ((⟨γ, hγm⟩ : (T.GN N).G₀) : (T.GN N).Γ) Y = Y := hy _
      rw [e2, hm, hm, map_inv, e0, one_smul] at e1
      exact e1.symm
  · intro hF
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (hN rep' hr' hF)
    · rintro z ⟨h1, h2⟩
      refine ⟨h1, fun j => ?_⟩
      obtain ⟨Y, hY⟩ := (mem_Bl _).1 (h2 j)
      obtain ⟨γ, hγ⟩ := S.ph N j
      obtain ⟨δ, hδ⟩ := S.ta N j
      exact ⟨Y, by rw [← hγ]; exact hY γ, by rw [← hδ]; exact hY δ⟩
    · exact (Set.toFinite ((Zl rep' : Set _))).subset fun z hz => hz.1
