module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewCayleyInertPlaceStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrIntRhoInv
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev dC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) R).submatrix finSumFinEquiv.symm id)

theorem dC_mul_inl {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inl p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_inr {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (finSumFinEquiv (Sum.inr p)) j = a p j := by
  simp only [dC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  simp [diagCols, Matrix.one_apply]

theorem dC_mul_castAdd {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (Fin.castAdd n p) j = a p j := by
  simpa using dC_mul_inl a p j

theorem dC_mul_addNat {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) (p : Fin n) (j : Fin m) :
    (dC R n * a) (p.addNat n) j = a p j := by
  simpa using dC_mul_inr a p j

theorem dC_mul_eq {R : Type} [CommRing R] {n m : ℕ} (a : Matrix (Fin n) (Fin m) R) :
    dC R n * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p
  · rw [dC_mul_inl, Matrix.of_apply, Equiv.symm_apply_apply]; rfl
  · rw [dC_mul_inr, Matrix.of_apply, Equiv.symm_apply_apply]; rfl

theorem dblG_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i k : Fin n ⊕ Fin n) :
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG J (finSumFinEquiv i) (finSumFinEquiv k) = dbl J i k := by
  simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem hTens_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB) (dC (AF F ⊗[F] E) nT * a) (dC (AF F ⊗[F] E) nT * b) = 0 := by
  unfold hTens
  have ha : dC (AF F ⊗[F] E) nT * a = Matrix.of fun i j => a (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq a
  have hb : dC (AF F ⊗[F] E) nT * b = Matrix.of fun i j => b (Sum.elim id id (finSumFinEquiv.symm i)) j :=
    dC_mul_eq b
  rw [ha, hb]
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, incM, Matrix.map_apply,
    Matrix.transpose_apply, dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, Finset.sum_neg_distrib, dC_mul_castAdd, dC_mul_addNat]

end GlobalTheory.LagrThetaInv

namespace GlobalTheory.LagrThetaInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem schr_dC (σ : E →ₐ[F] E) {nS nT : ℕ} (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ)
    (ψ : AddChar (AF F) ℂ) (a b : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ) :
    schr ψ (co.e (dC (AF F ⊗[F] E) nT * a)) (schr ψ (co.e (dC (AF F ⊗[F] E) nT * b)) φ) =
      schr ψ (co.e (dC (AF F ⊗[F] E) nT * (a + b))) φ := by
  rw [GlobalTheory.ThetaQuasiRat.schr_schr, ← co.form, symp, hTens_dC, mul_zero, map_zero, mul_zero,
    AddChar.map_zero_eq_one, one_smul, ← map_add, Matrix.mul_add]

theorem dC_map {n : ℕ} : (dC E n).map (incAF F E) = dC (AF F ⊗[F] E) n := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p <;>
    simp only [dC, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, diagCols,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply] <;> split_ifs <;> simp

theorem dC_mul_rat {nS nT : ℕ} (γ : Matrix (Fin nT) (Fin nS) E) :
    dC (AF F ⊗[F] E) nT * γ.map (incAF F E) = incM F (dC E nT * γ) := by
  rw [← dC_map, ← Matrix.map_mul]
  rfl

end GlobalTheory.LagrThetaInv


open scoped Pointwise in
open GlobalTheory.LagrThetaInv in
theorem GlobalTheory.LagrThetaInv.lagrInt_rho_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ)) = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 _ h𝓕 u φ hφ
  change GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)) =
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ)
  set g : WOF F E nS nT → ℂ := fun v => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)
      (dC (AF F ⊗[F] E) nT * v) = g (v + u) := by
    intro v
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [schr_dC]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    obtain ⟨y, z, hyz⟩ := hco (dC E nT * γ)
    have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = γ.map (incAF F E) := rfl
    show GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * (_ + v)) = _
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [← schr_dC, hr, dC_mul_rat, hyz, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hB.std.2.1 y z]
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlane
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvUniq.LocFin

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

abbrev ind (w : Pl (F := F)) : (κ → Fv F w) → ℂ := Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

def archPt (a : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), 0)

theorem evFin_archPt (a : κ → mixedEmbedding.mixedSpace F) (w : Pl (F := F)) (i : κ) : evFin F w (archPt a i) = 0 := by
  change (evalV F w) (0 : Af F) = 0
  exact map_zero _

theorem evI_archPt (a : κ → mixedEmbedding.mixedSpace F) (i : κ) : evI F (archPt a i) = a i := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)

theorem cancel (v : Pl (F := F)) (g : SInf F κ) (hg : g ≠ 0) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
    (hrt : ∀ ψ₀ : (κ → Fv F v) → ℂ, tens (evFin F v) ψ₀ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update ind v ψ₀))
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  obtain ⟨a, ha⟩ : ∃ a, g a ≠ 0 := by
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hg
    exact ⟨a, by simpa using ha⟩
  have hx0 : r (archPt a) = g a := by
    have e := congrFun (hrt (fun _ => 1)) (archPt a)
    simp only [tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i => evI F (archPt a i)) = a := funext fun i => evI_archPt a i
    have hP : (∏ᶠ w, Function.update (ind (κ := κ)) v (fun _ => 1) w fun i => evFin F w (archPt a i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [evFin_archPt, ind]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrz : r (archPt a + z) = g a := by rw [hr _ z hz, hx0]
  have hev : (fun i => evFin F v ((archPt a + z) i)) = y := by
    funext i
    rw [Pi.add_apply, map_add (f := _), evFin_archPt, zero_add]
    exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun h (archPt a + z)
  simp only [tens, hev, hrz] at e
  exact mul_right_cancel₀ ha e

end GlobalTheory.ThK.EvUniq.LocFin


open scoped Classical in
theorem GlobalTheory.ThK.EvUniq.finRel_of_ev : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ (e : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → ∀ v, GlobalTheory.ThK.EvUniq.FinRel B M M₁ H' v (ev v) := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e he ei ev hei hvm hloc v
  have hpre : ∀ w, ∃ ψ ∈ SB (Fin n × Fin d → Fv F w), ev w ψ = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := Fin n × Fin d₁) w
    rw [← (hvm w).2] at h
    obtain ⟨ψ, hψ, e⟩ := Submodule.mem_map.mp h
    exact ⟨ψ, hψ, e⟩
  let ψs : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ := fun w =>
    if M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w then M.vac w else (hpre w).choose
  have hψSB : ∀ w, ψs w ∈ SB _ := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; exact (hM.vac w).1
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.1
  have hψev : ∀ w, ev w (ψs w) = GlobalTheory.ThK.EvUniq.LocFin.ind w := fun w => by
    by_cases h : M₁.vac w = GlobalTheory.ThK.EvUniq.LocFin.ind w
    · simp only [ψs, if_pos h]; rw [(hvm w).1, h]
    · simp only [ψs, if_neg h]; exact (hpre w).choose_spec.2
  have hψM : ∀ᶠ w in cofinite, ψs w = M.vac w := by
    filter_upwards [hM₁.std] with w hw
    simp only [ψs, if_pos hw]
  have hψind : ∀ᶠ w in cofinite, ψs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hψM, hM.std] with w h1 h2
    rw [h1, h2]
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hei
    exact ⟨f, by simpa using hf⟩
  have hind : ∀ᶠ w in cofinite, (GlobalTheory.ThK.EvUniq.LocFin.ind (κ := Fin n × Fin d₁) w) =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := Eventually.of_forall fun _ => rfl
  obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f ψs hψind
  obtain ⟨ρ₁, hρ₁, hρt₁⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) _ hind
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ ρ := fun φ hφ => by
    refine ⟨hρ, ?_⟩
    rw [hρt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually ψs v φ hψind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact hψSB w
  have hRest₁ : ∀ φ ∈ SB (Fin n × Fin d₁ → Fv F v), Rest (evFin F v) φ ρ₁ := fun φ hφ => by
    refine ⟨hρ₁, ?_⟩
    rw [hρt₁ φ]
    refine GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v φ hind)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have key : ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) φ ρ) = tens (evFin F v) (ev v φ) ρ₁ := fun φ hφ => by
    rw [hρt φ, hρt₁ (ev v φ)]
    have hSB : ∀ w, Function.update ψs v φ w ∈ SB _ := fun w => by
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hφ
      · rw [Function.update_of_ne hw]; exact hψSB w
    have hcof : ∀ᶠ w in cofinite, Function.update ψs v φ w = M.vac w := by
      filter_upwards [hψM, eventually_cofinite_ne v] with w h1 h2
      rw [Function.update_of_ne h2, h1]
    rw [hloc f _ hSB hcof]
    congr 1
    funext w
    by_cases hw : w = v
    · subst hw; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, hψev w]
  have canc := GlobalTheory.ThK.EvUniq.LocFin.cancel v (ei f) hf ρ₁ hρ₁ hρt₁
  refine ⟨?_, ?_⟩
  · intro z hz φ hφ φ₁ hφ₁ hA χ₁ hχ₁ hA₁
    have h1 := he.Heisenberg₂ z _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    have hevφ : ev v φ ∈ SB _ := by
      rw [← (hvm v).2]
      exact Submodule.mem_map_of_mem hφ
    rw [hA₁ ρ₁ (hRest₁ _ hevφ)] at h1
    exact canc _ _ h1
  · intro u hu hz φ hφ φ₁ hφ₁ hA
    have h1 := he.inv u hu _ (hRest φ hφ).2
    rw [hA ρ (hRest φ hφ), key φ₁ hφ₁, key φ hφ] at h1
    exact canc _ _ h1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagNonvan

open scoped Classical
open GlobalTheory.DiagForm GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eq_zero_of_psi_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (b : AF F) (h : ∀ y : AF F, ψ (b * y) = 1) :
    b = 0 := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have h1 : b.1 = 0 := by
    refine e.injective ?_
    rw [map_zero]
    refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun s => ?_
    by_contra hT
    set T := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e b.1 * s) with hTdef
    have h2 := h (pairA F (e.symm ((1 / (2 * T)) • s)) 0)
    have e1 : b * pairA F (e.symm ((1 / (2 * T)) • s)) 0 = pairA F (b.1 * e.symm ((1 / (2 * T)) • s)) 0 := by
      show ((b.1 * _, b.2 * 0) : Ainf F × Af F) = (_, 0)
      rw [mul_zero]
      rfl
    have e2 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e (b.1 * e.symm ((1 / (2 * T)) • s))) = 1 / 2 := by
      rw [map_mul, RingEquiv.apply_symm_apply, mul_smul_comm, map_smul, ← hTdef, smul_eq_mul]
      field_simp
    rw [e1, psi_pairA hψ] at h2
    change Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (e (b.1 * e.symm ((1 / (2 * T)) • s))) : ℝ) : ℂ)) = 1 at h2
    have e3 : -(2 * (Real.pi : ℂ) * Complex.I) * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) := by push_cast; ring
    rw [e2, e3, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
    norm_num at h2
  have h2 : b.2 = 0 := by
    refine af_ext fun v => ?_
    rw [map_zero]
    by_contra hv
    apply GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v
    ext t
    rw [GlobalTheory.VacAny.psiV_apply, AddChar.one_apply, ← h (pairA F 0 (singleFin v ((evalV F v b.2)⁻¹ * t)))]
    congr 1
    show ((0, singleFin v t) : Ainf F × Af F) = (b.1 * 0, b.2 * singleFin v ((evalV F v b.2)⁻¹ * t))
    rw [mul_zero]
    congr 1
    refine af_ext fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  exact Prod.ext h1 h2

theorem continuous_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) :=
  continuous_pi fun i =>
    (continuous_symm.comp ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
      ((continuous_apply i).comp continuous_snd)

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ (p.1 + q.1) i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ q.1 i)
  rw [map_add (f := _), Pi.add_apply, map_add (f := _)]

theorem glue_zero : glue (0 : Vi F κ × Vf F κ) = 0 := by
  have h := glue_add (0 : Vi F κ × Vf F κ) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem eq_zero_of_glue {p : Vi F κ × Vf F κ} (h : glue p = 0) : p = 0 := by
  refine Prod.ext ?_ (funext fun i => congrArg Prod.snd (congrFun h i))
  refine (eI F κ).injective ?_
  rw [Prod.fst_zero, map_zero]
  funext i
  refine (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.injective ?_
  rw [Pi.zero_apply, map_zero]
  exact congrArg Prod.fst (congrFun h i)

theorem continuous_resD {φ : (κ ⊕ κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) :
    Continuous (resD F κ φ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    have hd : Continuous fun v : Vf F κ => (Sum.elim v v : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
      continuous_pi fun i => by cases i <;> exact continuous_apply _
    rw [show resD F κ (pureA F f g) = fun p => compD F κ f p.1 * g (Sum.elim p.2 p.2) from funext (resD_pureA f g)]
    exact ((compD F κ f).continuous.comp continuous_fst).mul ((hg.1.continuous.comp hd).comp continuous_snd)
  | zero => rw [map_zero]; exact continuous_zero
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.const_smul c

instance mu_haar : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance

theorem dot_left (a c : κ → AF F) : Sum.elim a a ⬝ᵥ Sum.elim c (0 : κ → AF F) = a ⬝ᵥ c := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem exists_lDiag_schr_ne {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {f : (κ ⊕ κ → AF F) → ℂ}
    (hf : f ∈ schA F (κ ⊕ κ)) (hf0 : f ≠ 0) : ∃ w, lDiag F κ (schr ψ w f) ≠ 0 := by
  obtain ⟨p, hp⟩ := Function.ne_iff.1 hf0
  by_contra hcon
  push_neg at hcon
  have hmem := fun w => GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w f hf
  let N : Vi F κ × Vf F κ → ℂ := resD F κ (schr ψ (p, 0) f)
  have hN : ∀ q, N q = f (Sum.elim (glue q) (glue q) + p) := fun q => by
    show ψ (_ ⬝ᵥ 0 + _ * (p ⬝ᵥ 0)) * _ = _
    rw [dotProduct_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
  let χ : (κ → AF F) → Vi F κ × Vf F κ → ℂ := fun c q => ψ (glue q ⬝ᵥ c)
  have key : N = 0 := by
    refine GlobalTheory.CharFourierInj.eq_zero χ (fun c => hψ.1.comp (continuous_glue.dotProduct continuous_const))
      (fun c q q' => ?_) (fun c c' q => ?_) (fun q => ?_) (fun c q => norm_psi hψ _) (fun q hq => ?_) (mu F κ) N
      (continuous_resD (hmem _)) (integrable_resD (hmem _)) fun c => ?_
    · simp only [χ, glue_add, add_dotProduct, AddChar.map_add_eq_mul]
    · simp only [χ, dotProduct_add, AddChar.map_add_eq_mul]
    · simp only [χ, dotProduct_zero, AddChar.map_zero_eq_one]
    · refine eq_zero_of_glue (funext fun i => eq_zero_of_psi_mul hψ _ fun y => ?_)
      have := hq (Pi.single i y)
      simp only [χ] at this
      rwa [dotProduct_single] at this
    · have h1 := hcon (p, Sum.elim c 0)
      rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD (hmem _))] at h1
      have e : ∀ q, resD F κ (schr ψ (p, Sum.elim c 0) f) q =
          ψ (⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0)) * (χ c q * N q) := fun q => by
        rw [hN]
        show ψ (Sum.elim (glue q) (glue q) ⬝ᵥ Sum.elim c 0 + ⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0)) *
          f (Sum.elim (glue q) (glue q) + p) = _
        rw [dot_left, AddChar.map_add_eq_mul]
        simp only [χ]
        ring
      simp only [e] at h1
      rw [integral_const_mul] at h1
      refine (mul_eq_zero.1 h1).resolve_left fun h0 => ?_
      have := norm_psi hψ (⅟(2 : AF F) * (p ⬝ᵥ Sum.elim c 0))
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  have h0 := hN 0
  rw [key, glue_zero, Sum.elim_zero_zero, zero_add] at h0
  exact hp h0.symm

theorem exists_invForm_rho_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)),
    IsStd ψ → IsDblCoord (cA σ) (-1) JA JB d dd →
    ∀ f ∈ schA F (κ ⊕ κ), f ≠ 0 →
    ∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ schA F (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ w : Matrix α (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), l (dd.rho ψ w f) ≠ 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d dd hψ hdd f hf hf0
  refine ⟨lDiag F κ, lDiag_adm, fun z φ hφ => ?_, ?_⟩
  · have hz : z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one]
    rw [hz, Darboux.rho, hdd z z, lDiag_schr ψ _ _ hφ]
  · obtain ⟨w, hw⟩ := exists_lDiag_schr_ne hψ hf hf0
    exact ⟨dd.e.symm w, by rwa [Darboux.rho, LinearEquiv.apply_symm_apply]⟩

end GlobalTheory.DiagNonvan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformMemUnitaryLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformMemUnitaryLatticeStabilizer
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyStab

theorem cayley_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)) (Y : Matrix (Fin d) (Fin d) (AE F E)), At (evFin F v) Y →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∃ M : Matrix (Fin d) (Fin d) (AE F E), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ h ∈ GlobalTheory.InertSph.KAt σ W v, mat h * (1 + Y) = 1 - Y := by
  intro F E _ _ _ _ _ σ d W v Y hY hYL hskew ⟨Np, hP1, hP2, hPL⟩ ⟨Nm, hM1, hM2, hML⟩
  set J := incM F W.J with hJ
  have hmap : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (A * B).map (cA σ) = A.map (cA σ) * B.map (cA σ) :=
    fun A B => Matrix.map_mul (f := (cA σ).toRingHom)
  have hmap1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) = 1 :=
    Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))
  have hGP : (1 - Y) * Np * (1 + Y) = 1 - Y := by rw [Matrix.mul_assoc, hP2, Matrix.mul_one]
  have h1 : (1 - Y) * Np * ((1 + Y) * Nm) = 1 := by
    rw [← Matrix.mul_assoc, hGP, hM1]
  have h2 : (1 + Y) * Nm * ((1 - Y) * Np) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (1 + Y), hM2, Matrix.mul_one, hP1]

  have hQP : (1 - Y)ᵀ * J * (1 - Y).map (cA σ) = (1 + Y)ᵀ * J * (1 + Y).map (cA σ) := by
    rw [Matrix.map_sub _ (map_sub (cA σ)), Matrix.map_add _ (map_add (cA σ)), hmap1, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one]
    have e : ∀ A B : Matrix (Fin d) (Fin d) (AE F E), (1 - A) * J * (1 - B) = (1 + A) * J * (1 + B) - 2 * (A * J + J * B) := by
      intro A B; noncomm_ring
    rw [e, hskew, mul_zero, sub_zero]
  have hU : ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ) = J := by
    have eT : Npᵀ * (1 + Y)ᵀ = 1 := by rw [← Matrix.transpose_mul, hP1, Matrix.transpose_one]
    have eM : (1 + Y).map (cA σ) * Np.map (cA σ) = 1 := by rw [← hmap, hP1, hmap1]
    calc ((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)
        = (Npᵀ * (1 + Y)ᵀ) * (((1 - Y) * Np)ᵀ * J * ((1 - Y) * Np).map (cA σ)) * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by
          rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
      _ = Npᵀ * (((1 - Y) * Np * (1 + Y))ᵀ * J * ((1 - Y) * Np * (1 + Y)).map (cA σ)) * Np.map (cA σ) := by
          rw [hmap ((1 - Y) * Np), Matrix.transpose_mul ((1 - Y) * Np)]
          simp only [Matrix.mul_assoc]
      _ = Npᵀ * ((1 + Y)ᵀ * J * (1 + Y).map (cA σ)) * Np.map (cA σ) := by rw [hGP, hQP]
      _ = (Npᵀ * (1 + Y)ᵀ) * J * ((1 + Y).map (cA σ) * Np.map (cA σ)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [eT, eM, Matrix.one_mul, Matrix.mul_one]
  let g : GL (Fin d) (AE F E) := ⟨(1 - Y) * Np, (1 + Y) * Nm, h1, h2⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) := hU
  let h : UA σ W.J := ⟨g, hg⟩
  have hmat : mat h = (1 - Y) * Np := rfl
  have hmatinv : mat h⁻¹ = (1 + Y) * Nm := rfl
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · intro u hu
    have e : mat h - 1 = -(Y * Np) - Y * Np := by
      rw [hmat]
      calc (1 - Y) * Np - 1 = (1 - Y) * Np - (1 + Y) * Np := by rw [hP1]
        _ = -(Y * Np) - Y * Np := by noncomm_ring
    have hYu : u • Y = 0 := hY u hu
    rw [e, smul_sub, smul_neg, ← Matrix.smul_mul, hYu, Matrix.zero_mul, neg_zero, sub_zero]
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [hmat, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (hPL z hz) (hYL _ (hPL z hz))
    · rw [hmatinv, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
      exact add_mem (hML z hz) (hYL _ (hML z hz))
  · rw [hmat, hGP]

end GlobalTheory.CayleyStab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CayleyTransformMemUnitaryLatticeStabilizerStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) Y →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 →
    (∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + Y) * M = 1 ∧ M * (1 + Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 - Y) * M = 1 ∧ M * (1 - Y) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ h ∈ GlobalTheory.InertSph.KAt σ W v, mat h * (1 + Y) = 1 - Y := by
  first | exact @GlobalTheory.CayleyStab.cayley_mem_KAt | exact GlobalTheory.CayleyStab.cayley_mem_KAt | (intros; apply GlobalTheory.CayleyStab.cayley_mem_KAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecomposition
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertTwoFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UA σ W.J}
    (hg : g ∈ GlobalTheory.InertSph.KAt σ W v) (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : g * h ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e : mat (g * h) = mat g * mat h := rfl
  have e' : mat (g * h)⁻¹ = mat h⁻¹ * mat g⁻¹ := by rw [mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h1 : u • (mat g - 1) = 0 := hg.1 u hu
    have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by rw [e]; noncomm_ring
    rw [this, smul_add, ← Matrix.smul_mul, h1, h2, Matrix.zero_mul, add_zero]
  · rw [e, e', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem inv_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {h : UA σ W.J}
    (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : h⁻¹ ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e1 : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by rw [Matrix.mul_sub, e1]; noncomm_ring
    rw [this, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hh.2 z hz).2, (hh.2 z hz).1⟩

theorem twoFac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk
  obtain ⟨Y, hYat, hYint, hYskew, ⟨Np, hNp1, hNp2, hNpi⟩, hm, ⟨ND, hND1, hND2, hNDi⟩⟩ :=
    GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer F E σ B a a' G X om om' hT v w hin k hk
  obtain ⟨h, hh, hhY⟩ := GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer F E σ (a + a') G.W v Y hYat hYint hYskew ⟨Np, hNp1, hNp2, hNpi⟩ hm
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  have eH : mat h = (1 - Y) * Np := by rw [← hhY, Matrix.mul_assoc, hNp1, Matrix.mul_one]
  have eH' : (1 + Y) * mat h = 1 - Y := by
    rw [eH, ← Matrix.mul_assoc, show (1 + Y) * (1 - Y) = (1 - Y) * (1 + Y) by noncomm_ring, Matrix.mul_assoc, hNp1,
      Matrix.mul_one]
  have eI : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  have intY1 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 + Y) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]; exact add_mem hz (hYint z hz)
  refine ⟨k * h, mul_mem_KAt hk hh, h⁻¹, inv_mem_KAt hh, ?_, ?_, by group⟩
  · have e : mat (k * h) = mat k * mat h := rfl
    have h1 : (1 + mat (k * h)) * ((1 + Y) * ND) = 1 := by
      have : (1 + mat k * mat h) * (1 + Y) = 1 + Y + mat k * (1 - Y) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hhY]
      rw [e, ← Matrix.mul_assoc, this, hND1]
    refine ⟨(1 + Y) * ND, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [← Matrix.mulVec_mulVec]; exact intY1 _ (hNDi z hz)
  · have h1 : (1 + mat h⁻¹) * ((⅟(2 : AF F)) • ((1 + Y) * mat h)) = 1 := by
      rw [Matrix.mul_smul]
      have : (1 + mat h⁻¹) * ((1 + Y) * mat h) = (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
        have c : (1 + Y) * mat h = mat h * (1 + Y) := eH'.trans hhY.symm
        rw [Matrix.add_mul, Matrix.one_mul, c, ← Matrix.mul_assoc, eI, Matrix.one_mul, hhY, two_smul]
        abel
      rw [this, smul_smul, invOf_mul_self, one_smul]
    refine ⟨_, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace F E (a + a') G.W v h2 _ (intY1 _ (hh.2 z hz).1)

end GlobalTheory.InertTwoFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecompositionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stabilizer_two_factor_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.InertTwoFac.twoFac | exact GlobalTheory.InertTwoFac.twoFac | (intros; apply GlobalTheory.InertTwoFac.twoFac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.TraceAddStar

theorem trace_eq_add_star : ∀ {D : D7} (x : D.host.E), ((Algebra.trace D.host.F D.host.E x : D.host.F) : D.host.E) = x + star x := by
  intro D x
  exact Formalism.MainNotions.BridgeLemma.tie_trace D.sp.cm x

end GlobalTheory.TraceAddStar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTrace_eq_add_star : ∀ {D : D7} (x : D.host.E), ((Algebra.trace D.host.F D.host.E x : D.host.F) : D.host.E) = x + star x := by
  first | exact @GlobalTheory.TraceAddStar.trace_eq_add_star | exact GlobalTheory.TraceAddStar.trace_eq_add_star | (intros; apply GlobalTheory.TraceAddStar.trace_eq_add_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralNeZeroOfCocompact
open scoped TensorProduct Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.PeriodicPositiveIntegral

theorem integral_ne_zero_of_cocompact {G : Type} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (Γ : AddSubgroup G) [Countable Γ] {K : Set G}
    (hK : IsCompact K) (hKc : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    (I : G → ℂ) (hI : Continuous I) (hper : ∀ γ ∈ Γ, ∀ u, I (γ + u) = I u)
    (hnn : ∀ u, 0 ≤ (I u).re) (h0 : 0 < (I 0).re) (ν : Measure G) [ν.IsAddHaarMeasure] (𝓕 : Set G)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 ν) (hfin : ν 𝓕 < ⊤) : ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hI.continuousOn
  have hint : Integrable I (ν.restrict 𝓕) := by
    refine Integrable.of_bound hI.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hper γ hγ w]
    exact hC _ h
  have hcre : Continuous fun u => (I u).re := Complex.continuous_re.comp hI
  have hO : IsOpen (Function.support fun u => (I u).re) := hcre.isOpen_support
  have hpos : ν (Function.support fun u => (I u).re) ≠ 0 := hO.measure_ne_zero ν ⟨0, h0.ne'⟩
  intro hz
  have hre : ∫ u in 𝓕, (I u).re ∂ν = 0 := by
    have := integral_re (𝕜 := ℂ) hint
    rw [hz] at this
    simpa using this
  have hlt : 0 < ∫ u in 𝓕, (I u).re ∂ν := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hnn) hint.re,
      Measure.restrict_apply hO.measurableSet, pos_iff_ne_zero]
    intro hm
    refine hpos (h𝓕.measure_zero_of_invariant _ (fun g => ?_) hm)
    ext u
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    show (I (((-g : Γ) : G) + u)).re ≠ 0 ↔ (I u).re ≠ 0
    rw [hper _ (-g).2]
  exact hlt.ne' hre

theorem integral_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (I : WOF F E nS nT → ℂ), Continuous I → (∀ γ ∈ ratLF F E nS nT, ∀ u, I (γ + u) = I u) →
    (∀ u, 0 ≤ (I u).re) → 0 < (I 0).re →
    ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν → ∫ u in 𝓕, I u ∂ν ≠ 0 := by
  intro F E _ _ _ _ _ nS nT I hI hper hnn h0 ν 𝓕 hν h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  exact integral_ne_zero_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc I hI hper hnn h0 ν 𝓕 h𝓕
    (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕)

end GlobalTheory.PeriodicPositiveIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRational
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_cols_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E), (matHom _ σ J g).1 * adMat F C = adMat F C' → (matHom _ σ J g).1 * adMat F Z = adMat F Z' → (matHom _ σ J g).1 * adMat F D = adMat F D' → g ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g C' D' Z' hC hZ hD
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  dsimp only [adMat] at hC hZ hD
  set ι := inclR (F := F) (E := E) (AF F) with hι
  set x : Matrix (Fin n) (Fin n) E := C' * (cT (σ : E →+* E) D * J) + Z' * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
    D' * (cT (σ : E →+* E) C * J) with hx
  have hM : (matHom _ σ J g).1 = x.map ι := by
    calc (matHom _ σ J g).1
        = (matHom _ σ J g).1 * (C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
            D * (cT (σ : E →+* E) C * J)).map ι := by
          rw [hF.sum, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      _ = x.map ι := by
          rw [hx]
          simp only [Matrix.map_add _ (map_add ι), Matrix.map_mul, Matrix.mul_add, ← Matrix.mul_assoc]
          rw [hC, hZ, hD]
  have hdet : x.det ≠ 0 := by
    haveI : Nontrivial (AF F ⊗[F] E) := ⟨⟨ι 0, ι 1, fun e => zero_ne_one (hinj e)⟩⟩
    intro h0
    have hu : IsUnit (x.map ι).det := by
      rw [← hM]; exact Matrix.isUnits_det_units _
    have h1 := ι.map_det x
    rw [h0, map_zero, RingHom.mapMatrix_apply] at h1
    rw [← h1] at hu
    exact not_isUnit_zero hu
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet, ?_, Units.ext hM.symm⟩
  show cT (σ : E →+* E) x * J * x = J
  apply Matrix.map_injective hinj
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have hcT : cT (sigR (AF F) σ) (x.map ι) = (cT (σ : E →+* E) x).map ι := by
    ext a b; simp [Formalism.UG.cT, sigR, hι, inclR]
  rw [hM, hcT, JR, ← hι, ← Matrix.map_mul, ← Matrix.map_mul] at hg
  exact hg

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitaryRationalPointsOfFrameImagesRationalStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unitaryRationalPoints_of_frameImages_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (C' D' : Matrix (Fin n) (Fin j) E) (Z' : Matrix (Fin n) (Fin m) E), (matHom _ σ J g).1 * adMat F C = adMat F C' → (matHom _ σ J g).1 * adMat F Z = adMat F Z' → (matHom _ σ J g).1 * adMat F D = adMat F D' → g ∈ ratPts σ J := by
  first | exact @GlobalTheory.SphEis.mem_ratPts_of_cols_rat | exact GlobalTheory.SphEis.mem_ratPts_of_cols_rat | (intros; apply GlobalTheory.SphEis.mem_ratPts_of_cols_rat <;> assumption)
end
end
