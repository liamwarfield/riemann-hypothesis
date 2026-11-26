module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DiffTranslate
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpGenPi
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem exp_map_coord {ι : Type} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) := by
  classical
  have hc : Continuous fun M : Matrix (Fin a) (Fin a) (ι → ℂ) => M.map fun x => x w :=
    continuous_id.matrix_map (continuous_apply w)
  have key := open scoped Norms.Operator in
    NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix :
      Matrix (Fin a) (Fin a) (ι → ℂ) →+* Matrix (Fin a) (Fin a) ℂ) hc X
  exact key

private theorem gen_prod {ι : Type} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : (ι → Matrix (Fin a) (Fin a) ℂ) → Matrix (Fin a) (Fin a) (ι → ℂ),
      J = fun g => Matrix.of fun i j v => g v i j := ⟨_, rfl⟩
  have Jmap : ∀ g v, (J g).map (fun x => x v) = g v := by
    intro g v
    subst hJ
    ext i j
    rfl
  have Jmul : ∀ g h, J (g * h) = J g * J h := by
    intro g h
    subst hJ
    ext i j v
    simp [Matrix.mul_apply, Finset.sum_apply]
  have Jone : J 1 = 1 := by
    subst hJ
    ext i j v
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply, hij]
  have Jext : ∀ M N : Matrix (Fin a) (Fin a) (ι → ℂ),
      (∀ v, M.map (fun x => x v) = N.map (fun x => x v)) → M = N := by
    intro M N h
    ext i j v
    exact congrFun (congrFun (h v) i) j
  have single : ∀ (w : ι) (m : Matrix (Fin a) (Fin a) ℂ), m.det ≠ 0 →
      J (Function.update 1 w m) ∈ H := by
    intro w m hm
    let K : Submonoid (Matrix (Fin a) (Fin a) ℂ) :=
      { carrier := {p | J (Function.update 1 w p) ∈ H}
        one_mem' := by
          show J (Function.update 1 w 1) ∈ H
          have : Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w 1 = 1 := by
            funext v
            by_cases hv : v = w
            · subst hv
              simp
            · simp [hv]
          rw [this, Jone]
          exact H.one_mem
        mul_mem' := by
          intro p q hp hq
          show J (Function.update 1 w (p * q)) ∈ H
          have : Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w (p * q) =
              Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w p *
                Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) w q := by
            funext v
            by_cases hv : v = w
            · subst hv
              simp
            · simp [hv]
          rw [this, Jmul]
          exact H.mul_mem hp hq }
    have hK : ∀ X, NormedSpace.exp X ∈ K := by
      intro X
      show J (Function.update 1 w (NormedSpace.exp X)) ∈ H
      have : J (Function.update 1 w (NormedSpace.exp X)) =
          NormedSpace.exp (J (Function.update 0 w X)) := by
        apply Jext
        intro v
        rw [Jmap, exp_map_coord, Jmap]
        by_cases hv : v = w
        · subst hv
          simp
        · simp [hv, NormedSpace.exp_zero]
      rw [this]
      exact hH _
    exact UpperTheory.V.AlgRepEndIrreducible.expGenC a K hK m hm
  have hdet : ∀ v, (y.map fun x => x v).det ≠ 0 := by
    intro v
    have h1 := hy.map (Pi.evalRingHom (fun _ : ι => ℂ) v).mapMatrix
    rw [Matrix.isUnit_iff_isUnit_det] at h1
    exact h1.ne_zero
  have all : ∀ s : Finset ι,
      J (fun v => if v ∈ s then y.map (fun x => x v) else 1) ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun v => if v ∈ (∅ : Finset ι) then y.map (fun x => x v) else 1) = 1 := by
        funext v
        simp
      rw [this, Jone]
      exact H.one_mem
    | insert b s hb ih =>
      have : (fun v => if v ∈ insert b s then y.map (fun x => x v) else 1) =
          Function.update (1 : ι → Matrix (Fin a) (Fin a) ℂ) b (y.map fun x => x b) *
            (fun v => if v ∈ s then y.map (fun x => x v) else 1) := by
        funext v
        by_cases hv : v = b
        · subst hv
          simp [hb]
        · simp [hv]
      rw [this, Jmul]
      exact H.mul_mem (single b _ (hdet b)) ih
  have hy' : y = J (fun v => if v ∈ (Finset.univ : Finset ι) then y.map (fun x => x v) else 1) := by
    apply Jext
    intro v
    rw [Jmap]
    simp
  rw [hy']
  exact all _

theorem UpperTheory.V.Lit.Bor.expGenPi :
    UpperTheory.V.Lit.Bor.ExpGenPi := by
  intro T _ a H hH y
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_prod (ι := T) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp X
    exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h
  have : u = y := Units.ext h'
  exact this ▸ hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolIdExp
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem emb_split {E : Type} [Field E] [_root_.NumberField.IsTotallyComplex E] (z : (E →+* ℂ) → ℂ) :
    ∃ u v : Cinf E, z = emb E u + Complex.I • emb E v := by
  refine ⟨fun w => (z w.embedding + starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2,
    fun w => -Complex.I * (z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2, ?_⟩
  funext τ
  change z τ = coord τ _ + Complex.I * coord τ _
  have key : ∃ w : InfinitePlace E, τ = w.embedding ∨ τ = ComplexEmbedding.conjugate w.embedding := by
    refine ⟨InfinitePlace.mk τ, ?_⟩
    have h' : InfinitePlace.mk (InfinitePlace.mk τ).embedding = InfinitePlace.mk τ := InfinitePlace.mk_embedding _
    exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
  obtain ⟨w, rfl | rfl⟩ := key
  · rw [UpperTheory.V.FieldIso.coord_embedding, UpperTheory.V.FieldIso.coord_embedding]
    linear_combination ((z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2) * Complex.I_mul_I
  · rw [UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding,
      UpperTheory.V.FieldIso.coord_embedding]
    simp only [map_div₀, map_add (f := _), map_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ (z w.embedding) - z (ComplexEmbedding.conjugate w.embedding)) / 2) * Complex.I_mul_I

private theorem emb_cont {E : Type} [Field E] : Continuous (emb E) := by
  refine continuous_pi fun τ => ?_
  change Continuous (coord τ)
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

open scoped Matrix.Norms.Operator in
private theorem exp_map_emb {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    (NormedSpace.exp Y).map (emb E) = NormedSpace.exp (Y.map (emb E)) :=
  NormedSpace.map_exp (RingHom.mapMatrix (m := Fin a) (emb E)) (continuous_id.matrix_map emb_cont) Y

open scoped Matrix.Norms.Operator in
private theorem exp_diff {T : Type} [Fintype T] {a : ℕ} (P Q : Matrix (Fin a) (Fin a) (T → ℂ)) :
    Differentiable ℂ fun s : ℂ => (fun i j => NormedSpace.exp (P + s • Q) i j : Fin a → Fin a → T → ℂ) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h : Differentiable ℂ fun s : ℂ => NormedSpace.exp (P + s • Q) := fun s =>
    (NormedSpace.exp_analytic (𝕂 := ℂ) (P + s • Q)).differentiableAt.comp s
      (f := fun s : ℂ => P + s • Q) ((differentiableAt_const P).add (differentiableAt_id.smul_const Q))
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  let l : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] (T → ℂ) := Matrix.entryLinearMap ℂ (T → ℂ) i j
  exact (LinearMap.toContinuousLinearMap l).differentiable.comp h

theorem UpperTheory.V.Lit.Bor.holIdExp :
    UpperTheory.V.Lit.Bor.HolIdExp := by
  intro E _ _ _ a Φ hΦ h0 X
  choose A B hAB using fun i j => emb_split (X i j)
  let P := (Matrix.of A).map (emb E)
  let Q := (Matrix.of B).map (emb E)
  have hX : X = P + Complex.I • Q := by
    exact Matrix.ext fun i j => hAB i j
  have hd : Differentiable ℂ fun s : ℂ => Φ fun i j => NormedSpace.exp (P + s • Q) i j :=
    differentiableOn_univ.1 (hΦ.comp (exp_diff P Q).differentiableOn fun s _ => Matrix.isUnit_exp (P + s • Q))
  have hr : ∀ t : ℝ, (Φ fun i j => NormedSpace.exp (P + (t : ℂ) • Q) i j) = 0 := fun t => by
    have e : P + (t : ℂ) • Q = (Matrix.of A + t • Matrix.of B).map (emb E) := by
      ext i j τ
      change coord τ (A i j) + (t : ℂ) * coord τ (B i j) = coord τ (A i j + t • B i j)
      rw [map_add (f := _), UpperTheory.V.FieldIso.coord_smul, Complex.real_smul]
    rw [e, ← exp_map_emb]
    exact h0 (Matrix.isUnit_exp (Matrix.of A + t • Matrix.of B)).unit
  have hf : ∃ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, (Φ fun i j => NormedSpace.exp (P + s • Q) i j) = (fun _ => 0) s := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hr)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun s _ => hd.analyticAt s) analyticOnNhd_const hf
  rw [hX]
  exact congrFun this Complex.I
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem diff_translate {T : Type} [Fintype T] {a : ℕ} (Φ : (Fin a → Fin a → T → ℂ) → ℂ)
    (hΦ : DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)}) (A B : GL (Fin a) (T → ℂ)) :
    DifferentiableOn ℂ (fun x : Fin a → Fin a → T → ℂ => Φ (fun i j => (A.val * Matrix.of x * B.val) i j))
      {x | IsUnit (Matrix.of x)} := by
  have hd : Differentiable ℂ
      (fun x : Fin a → Fin a → T → ℂ => (fun i j => (A.val * Matrix.of x * B.val) i j : Fin a → Fin a → T → ℂ)) := by
    refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => differentiable_pi.2 fun t => ?_
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply]
    fun_prop
  refine hΦ.comp hd.differentiableOn fun x hx => ?_
  exact (A.isUnit.mul hx).mul B.isUnit

theorem UpperTheory.V.Lit.Bor.holId :
    UpperTheory.V.Lit.Bor.HolId := by
  intro E _ _ _ a
  have hv : ∀ y : GL (Fin a) (Cinf E),
      (GeneralLinearGroup.map (emb E) y).val = Matrix.of (fun i j => emb E (y.val i j)) := fun y => rfl
  let S : Submonoid (GL (Fin a) ((E →+* ℂ) → ℂ)) :=
    { carrier := {g | ∀ Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ,
        DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} →
        (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = 0) → Φ (fun i j => g.val i j) = 0}
      one_mem' := fun Φ _ h0 => by
        have h := h0 1
        have e : (fun i j => emb E ((1 : GL (Fin a) (Cinf E)).val i j)) =
            fun i j => (1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val i j := by
          have := hv 1
          rw [map_one] at this
          exact this.symm
        rwa [e] at h
      mul_mem' := fun {g h} hg hh Φ hΦ h0 => by
        have h1 : ∀ y : GL (Fin a) (Cinf E),
            Φ (fun i j => ((GeneralLinearGroup.map (emb E) y).val * h.val) i j) = 0 := fun y => by
          have := hh _ (diff_translate Φ hΦ (GeneralLinearGroup.map (emb E) y) 1) fun z => by
            have h2 := h0 (y * z)
            have h3 := hv (y * z)
            rw [map_mul, Units.val_mul, hv z] at h3
            simp only [Units.val_one, mul_one, h3]
            exact h2
          simp only [Units.val_one, mul_one] at this
          exact this
        have := hg _ (diff_translate Φ hΦ 1 h) fun z => by
          simp only [Units.val_one, one_mul]
          exact h1 z
        simp only [Units.val_one, one_mul] at this
        exact this }
  intro Φ hΦ h0 g
  refine expGenPi _ a S (fun X y hy Ψ hΨ h1 => ?_) g Φ hΦ h0
  rw [hy]
  exact holIdExp E a Ψ hΨ h1 X
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolExt
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.holExt :
    UpperTheory.V.Lit.Bor.HolExt := by
  intro E _ _ _ a f hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · exact ⟨fun x => x i j τ, by fun_prop, fun _ => rfl⟩
    · refine ⟨fun x => ((Matrix.of x).det τ)⁻¹, DifferentiableOn.inv ?_ fun x hx => ?_, fun y => ?_⟩
      · simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
        exact Differentiable.differentiableOn (Differentiable.fun_sum fun σ _ =>
          (differentiable_const _).mul (by fun_prop))
      · exact (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) τ)).ne_zero
      · exact congrArg (fun z : (E →+* ℂ) → ℂ => (z τ)⁻¹) ((emb E).map_det y.val).symm
  | algebraMap c => exact ⟨fun _ => c, differentiableOn_const c, fun _ => rfl⟩
  | add f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ + Ψ, hΦ.add hΨ, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | mul f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ * Ψ, hΦ.mul hΨ, fun y => by rw [Pi.mul_apply, Pi.mul_apply, e1, e2]⟩
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cxGrp_comp {T : Type} [Fintype T] {a : ℕ} {Φ : (Fin a → Fin a → T → ℂ) → ℂ}
    (hΦ : DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)}) (g h : GL (Fin a) (T → ℂ)) :
    DifferentiableOn ℂ (fun x : Fin a → Fin a → T → ℂ => Φ (fun i j => (g.val * Matrix.of x * h.val) i j))
      {x | IsUnit (Matrix.of x)} := by
  have hd : Differentiable ℂ (fun x : Fin a → Fin a → T → ℂ => fun i j => (g.val * Matrix.of x * h.val) i j) := by
    refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => differentiable_pi.2 fun t => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply]
    fun_prop
  refine hΦ.comp hd.differentiableOn fun x hx => ?_
  have hx' : IsUnit (Matrix.of x) := hx
  exact (g.isUnit.mul hx').mul h.isUnit

theorem UpperTheory.V.Lit.Bor.cxGrp :
    UpperTheory.V.Lit.Bor.CxGrp := by
  intro E _ _ _ a Ξ
  choose Φ hΦ hv using fun k l => UpperTheory.V.Lit.Bor.holExt E a _ (Ξ.reg k l)
  have hv' : ∀ k l (y : GL (Fin a) (Cinf E)),
      Φ k l (fun i j => (GeneralLinearGroup.map (emb E) y).val i j) = Ξ.mat y k l := fun k l y => hv k l y
  have h1 : ∀ k l (y : GL (Fin a) (Cinf E)) (g : GL (Fin a) ((E →+* ℂ) → ℂ)),
      Φ k l (fun i j => (GeneralLinearGroup.map (emb E) y * g).val i j) =
        ∑ m, Ξ.mat y k m * Φ m l (fun i j => g.val i j) := by
    intro k l y g
    have key := UpperTheory.V.Lit.Bor.holId E a (fun x =>
      Φ k l (fun i j => ((GeneralLinearGroup.map (emb E) y).val * Matrix.of x *
        (1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val) i j) - ∑ m, Ξ.mat y k m * Φ m l x)
      ((cxGrp_comp (hΦ k l) _ _).sub
        (DifferentiableOn.fun_sum fun m _ => (hΦ m l).const_mul _)) (fun z => by
          have e := hv' k l (y * z)
          rw [map_mul, map_mul, Matrix.mul_apply] at e
          simp only [hv]
          rw [← e, sub_eq_zero, Units.val_one, mul_one]
          rfl) g
    rw [sub_eq_zero, Units.val_one, mul_one] at key
    exact key
  have h2 : ∀ k l (g h : GL (Fin a) ((E →+* ℂ) → ℂ)),
      Φ k l (fun i j => (g * h).val i j) =
        ∑ m, Φ k m (fun i j => g.val i j) * Φ m l (fun i j => h.val i j) := by
    intro k l g h
    have key := UpperTheory.V.Lit.Bor.holId E a (fun x =>
      Φ k l (fun i j => ((1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val * Matrix.of x * h.val) i j) -
        ∑ m, Φ k m x * Φ m l (fun i j => h.val i j))
      ((cxGrp_comp (hΦ k l) _ _).sub
        (DifferentiableOn.fun_sum fun m _ => (hΦ k m).mul_const _)) (fun z => by
          have e := h1 k l z h
          simp only [hv]
          rw [← e, sub_eq_zero, Units.val_one, one_mul]
          rfl) g
    rw [sub_eq_zero, Units.val_one, one_mul] at key
    exact key
  refine ⟨{ toFun := fun g => Matrix.of fun k l => Φ k l (fun i j => g.val i j)
            map_one' := ?_
            map_mul' := fun g h => ?_ }, Φ, hΦ, fun _ _ _ => rfl, fun y => ?_⟩
  · ext k l
    have e := hv' k l 1
    rw [map_one, map_one] at e
    exact e
  · ext k l
    rw [Matrix.mul_apply]
    exact h2 k l g h
  · ext k l
    exact hv' k l y
