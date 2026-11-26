module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotentDoubledStabilizerAddsDiagonalBloc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceBigCellExistsAdmissibleInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocksStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatAtVSelfDual
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.PsiUnrSelfDual

open GlobalTheory.InertSelfDual

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v →
    (∀ z : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      (z ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W v ↔ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W v,
        B.ψ (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F G.V.J)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F G.W.J) z γ) = 1)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hunr z hz
  have hV := hT.geo.hV
  have hW := hT.geo.hW
  constructor
  · intro hzm γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V G.W _ _ _ _ hT.base hV hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    haveI := hT.base.unram
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, hTS⟩ := exists_formFrame σ G.V.J (det_ne_zero_of_herm σ B hV) G.V.L hV.lat
      (fun y hy => (hV.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTS'⟩ := exists_formFrame σ G.W.J (det_ne_zero_of_skew σ B hW) G.W.L hW.lat
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (G.V.J * S.map σ)ᵀ * z * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (G.V.J * S.map σ)ᵀ * (u • z) * (incM F (G.W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, evFin F v (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
        (inclR (F := F) (AF F) (σ e) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ G.V.L := by
        have := G.V.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV G.V G.W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F G.V.J) (incM F G.W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y) z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      have := (hunr _).1 key
      rw [htC, map_neg] at this
      exact neg_mem_iff.1 this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, evFin F v (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
        (inclR (F := F) (AF F) (c i : E) * C j l)) ∈ v.adicCompletionIntegers F := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (G.V.J * S.map σ)ᵀ T' (G.W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
    refine ⟨_, fun u hu => ?_, hint' i j l, fun r => (s i : E) * T r j, ?_, fun r => T' r l, hTm' l, ?_⟩
    · rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    · have := G.V.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    · rw [smul_assoc]
      congr 1
      ext p q
      simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
      ring

end GlobalTheory.PsiUnrSelfDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunction
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacAny

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]


omit [DecidableEq α] [DecidableEq β] in
theorem symp_dbl (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    symp (R := R) c ξ JA (dbl JB) x y =
      symp (R := R) c ξ JA JB x.toCols₁ y.toCols₁ - symp (R := R) c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  simp [hTens, dbl, Fintype.sum_sum_type, Matrix.toCols₁, Matrix.toCols₂, Finset.sum_add_distrib, sub_eq_add_neg]

omit [DecidableEq α] [DecidableEq β] in
theorem symp_zero_right (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x : Matrix α β E) :
    symp (R := R) c ξ JA JB x 0 = 0 := by
  simp [symp, hTens]

theorem schr_box_star [Invertible (2 : R)] (ψ : AddChar R ℂ) (hψ : ∀ a, star (ψ a) = ψ (-a)) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (Φ Ψ : (κ → R) → ℂ) :
    schr ψ (Sum.elim w.1 w'.1, Sum.elim w.2 (-w'.2)) (boxFun Φ fun x => star (Ψ x)) =
      boxFun (schr ψ w Φ) fun x => star (schr ψ w' Ψ x) := by
  funext x
  have e1 : (x + Sum.elim w.1 w'.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 := by funext i; rfl
  have e2 : (x + Sum.elim w.1 w'.1) ∘ Sum.inr = x ∘ Sum.inr + w'.1 := by funext i; rfl
  have e3 : x ⬝ᵥ Sum.elim w.2 (-w'.2) + ⅟(2 : R) * (Sum.elim w.1 w'.1 ⬝ᵥ Sum.elim w.2 (-w'.2)) =
      ((x ∘ Sum.inl) ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) + -((x ∘ Sum.inr) ⬝ᵥ w'.2 + ⅟(2 : R) * (w'.1 ⬝ᵥ w'.2)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Function.comp_apply]
    ring
  simp only [schr, boxFun, e1, e2, e3, AddChar.map_add_eq_mul ψ _ (-_), star_mul', hψ]
  ring

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem local_identity (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ) (χ : ℂ) (hγ : At (evFin F v) γ)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
    (hA : co.rho ψ γ (tens (evFin F v) f r) = χ • tens (evFin F v) f r) (x₀ : κ → AF F) (hx₀ : r x₀ ≠ 0)
    (ξ : κ → Fv F v) : GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = χ * f ξ := by
  have hx1 : ∀ k, At (evFin F v) ((co.e γ).1 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).1 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  have hy1 : ∀ k, At (evFin F v) ((co.e γ).2 k) := fun k u hu => by
    have h := congrArg (fun w => (co.e w).2 k) (hγ u hu)
    simpa [LinearEquiv.map_smul] using h
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : At (evFin F v) z := GlobalTheory.VacIndic.at_pi fun k => GlobalTheory.LatVac.at_liftV v _
  set x : κ → AF F := x₀ + z with hx
  have hevx : (fun i => evFin F v (x i)) = ξ := by
    funext i
    simp [hx, hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : r x = r x₀ := hr x₀ z hzat
  have hrx1 : r (x + (co.e γ).1) = r x := hr x _ (GlobalTheory.VacIndic.at_pi hx1)
  have key := congrFun hA x
  simp only [Darboux.rho, schr, tens, Pi.smul_apply, smul_eq_mul] at key
  have hAt : At (evFin F v) (x ⬝ᵥ (co.e γ).2 + ⅟(2 : AF F) * ((co.e γ).1 ⬝ᵥ (co.e γ).2)) := by
    refine GlobalTheory.VacIndic.at_add ?_ (GlobalTheory.VacIndic.at_mul_left ?_)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
    · exact GlobalTheory.VacIndic.at_sum _ _ fun i => GlobalTheory.VacIndic.at_mul_left (hy1 i)
  rw [GlobalTheory.VacIndic.psi_of_at ψ hAt, hrx1] at key
  have hhalf : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
    rw [GlobalTheory.VacIndic.invOf_two_eq, GlobalTheory.VacIndic.evFin_algebraMap]
    simp [map_ofNat]
  have hdot : ∀ a b : κ → AF F, evFin F v (a ⬝ᵥ b) = (fun i => evFin F v (a i)) ⬝ᵥ (fun i => evFin F v (b i)) := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, map_sum, map_mul]
  have hsum : (fun i => evFin F v ((x + (co.e γ).1) i)) = ξ + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    rw [← hevx]
    simp [GlobalTheory.LatVac.locCo]
  rw [map_add (f := _), map_mul, hhalf, hdot, hdot, hevx, hsum] at key
  have hr0 : r x ≠ 0 := hrx ▸ hx₀
  rw [GlobalTheory.LatVac.psiAt_apply]
  apply mul_right_cancel₀ hr0
  rw [mul_assoc χ, ← key]
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ring

def latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) :
    AddSubgroup (Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) where
  carrier := {z | z.toCols₁ ∈ latAtV X Y v ∧ z.toCols₂ ∈ latAtV X Y v}
  zero_mem' := ⟨(latAtV X Y v).zero_mem, (latAtV X Y v).zero_mem⟩
  add_mem' := fun ha hb => ⟨(latAtV X Y v).add_mem ha.1 hb.1, (latAtV X Y v).add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨(latAtV X Y v).neg_mem ha.1, (latAtV X Y v).neg_mem ha.2⟩

theorem at_latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) :
    ∀ γ ∈ latDbl X Y v, At (evFin F v) γ := by
  intro γ hγ u hu
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable X Y v).1 _ hγ.1 u hu
  have h2 := (GlobalTheory.LatVac.latAtV_at_stable X Y v).1 _ hγ.2 u hu
  ext i (j | j)
  · exact congrFun (congrFun h1 i) j
  · exact congrFun (congrFun h2 i) j

theorem vecMulVec_mem_latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) {x : Fin n → E} (hx : x ∈ X.L)
    {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ GlobalTheory.DblVac.latD Y v) :
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) z ∈ latDbl X Y v :=
  ⟨GlobalTheory.VacTransport.vecMulVec_mem X Y v hx hz.1, GlobalTheory.VacTransport.vecMulVec_mem X Y v hx hz.2⟩

theorem mul_transpose_mem_doubledTensorLattice_of_into_doubled {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F))
    (h : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.InertSph.latAt Y v, h *ᵥ z ∈ GlobalTheory.DblVac.latD Y v)
    {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X Y v) : γ * hᵀ ∈ latDbl X Y v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, x, hx, y, hy, rfl⟩ := hz
    have hm : (a • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt Y v :=
      AddSubgroup.subset_closure ⟨a, ha, hv, y, hy, rfl⟩
    have e : a • incM F (Matrix.vecMulVec x y) =
        Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) (a • fun i => inclR (F := F) (AF F) (y i)) := by
      ext i j
      simp [Matrix.vecMulVec_apply, incM]
    rw [e, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    exact vecMulVec_mem_latDbl X Y v hx (hh _ hm)
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add z z' _ _ h h' => rw [Matrix.add_mul]; exact add_mem h h'
  | neg z _ h => rw [Matrix.neg_mul]; exact neg_mem h

theorem mul_transpose_mem_latDbl {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F))
    (h : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.DblVac.latD Y v, h *ᵥ z ∈ GlobalTheory.DblVac.latD Y v)
    {γ : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)} (hγ : γ ∈ latDbl X Y v) : γ * hᵀ ∈ latDbl X Y v := by
  have e : γ * hᵀ = γ.toCols₁ * (h.toCols₁)ᵀ + γ.toCols₂ * (h.toCols₂)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toCols₁, Matrix.toCols₂]
  rw [e]
  refine add_mem (mul_transpose_mem_doubledTensorLattice_of_into_doubled X Y v _ (fun z hz => ?_) hγ.1)
    (mul_transpose_mem_doubledTensorLattice_of_into_doubled X Y v _ (fun z hz => ?_) hγ.2)
  · have e1 : h.toCols₁ *ᵥ z = h *ᵥ Sum.elim z 0 := by
      ext i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toCols₁]
    rw [e1]
    exact hh _ ⟨hz, (GlobalTheory.InertSph.latAt Y v).zero_mem⟩
  · have e1 : h.toCols₂ *ᵥ z = h *ᵥ Sum.elim 0 z := by
      ext i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toCols₂]
    rw [e1]
    exact hh _ ⟨(GlobalTheory.InertSph.latAt Y v).zero_mem, hz⟩

theorem latDbl_selfDual (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    (z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (hz : At (evFin F v) z) :
    z ∈ latDbl X Y v ↔ ∀ γ ∈ latDbl X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F Y.J)) z γ) = 1 := by
  have hz1 : At (evFin F v) z.toCols₁ := fun u hu => by
    ext i j; exact congrFun (congrFun (hz u hu) i) (Sum.inl j)
  have hz2 : At (evFin F v) z.toCols₂ := fun u hu => by
    ext i j; exact congrFun (congrFun (hz u hu) i) (Sum.inr j)
  constructor
  · intro hm γ hγ
    rw [symp_dbl, AddChar.map_sub_eq_div, (hsd _ hz1).1 hm.1 _ hγ.1, (hsd _ hz2).1 hm.2 _ hγ.2, div_one]
  · intro h
    refine ⟨(hsd _ hz1).2 fun γ hγ => ?_, (hsd _ hz2).2 fun γ hγ => ?_⟩
    · have := h (Matrix.fromCols γ 0) ⟨by simpa using hγ, by simpa using zero_mem _⟩
      rwa [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, sub_zero] at this
    · have := h (Matrix.fromCols 0 γ) ⟨by simpa using zero_mem _, by simpa using hγ⟩
      rw [symp_dbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, symp_zero_right, zero_sub,
        AddChar.map_neg_eq_inv] at this
      exact inv_eq_one.1 this

theorem dbl_eigen (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsLattice E)
    (hY : Y.L.IsLattice E) (M : Model σ X Y) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (v : Pl (F := F)) (hunr : PsiUnr ψ v)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : M.IsVac ψ v φ)
    (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F X.J) (dbl (incM F Y.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (omd : GlobalTheory.DblVac.UD σ Y →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ))
    (hdc : IsDblCoord (cA σ) (-1 : AE F E) (incM F X.J) (incM F Y.J) M.co dd)
    (hU : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (r : (Fin n × Fin d → AF F) → ℂ) (hr : Rest (evFin F v) φ r) (g : GlobalTheory.DblVac.UD σ Y)
    (hg : g ∈ GlobalTheory.DblVac.KD σ Y v) : ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x))) =
        μ • boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) := by
  classical
  obtain ⟨hvSB, hφ0, θ, -, hvac⟩ := hφ
  have hstar : ∀ a, star (ψ a) = ψ (-a) := fun a => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, GlobalTheory.StdCharFromIsStd.norm_psi hψ a]
    simp
  set vD := boxFun φ (fun x => star (φ x)) with hvD
  set RD := boxFun r (fun x => star (r x)) with hRD
  have hvDSB : vD ∈ SB _ := box_mem_SB hvSB ⟨hvSB.1.comp _, hvSB.2.comp_left (star_zero _)⟩
  have hvD0 : vD ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hφ0
    refine Function.ne_iff.mpr ⟨Sum.elim x x, ?_⟩
    simp only [hvD, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  have hS : boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) = tens (evFin F v) vD RD := by
    funext x
    simp only [tens, boxFun, hvD, hRD, Function.comp_def, star_mul']
    ring
  have hRest : Rest (evFin F v) vD RD := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hz1, hr.1 _ _ hz2]
    · rw [← hS]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hr.2 _ (GlobalTheory.ConjSch.star_mem_schA _ _ hr.2)

  obtain ⟨φ₁, -, hA⟩ : ∃ φ₁ ∈ SB _, Acts (evFin F v) (omd g) vD φ₁ := by
    refine GlobalTheory.DblActs.acts_of_comm v ψ hψ (omd g) (fun Φ hΦ => hU.pres g Φ hΦ)
      (fun μ hμ Φ hΦ => hU.unit μ hμ g Φ hΦ) ?_ vD hvDSB
    intro u hu x y Φ hΦ
    set z := dd.e.symm (x, y) with hz
    have he : dd.e (u • z) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hz, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hg.1 u hu
    have e2 : actB (cA σ) g (u • z) = u • z := by
      simp only [actB]
      set P := GlobalTheory.DblVac.matD g with hP
      set c : AE F E := algebraMap (AF F) (AE F E) u with hc
      have hs1 : u • z = c • z := (algebraMap_smul (AE F E) u z).symm
      have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
      have h2' : c • (P - 1) = 0 := hs2 ▸ h2
      have : (c • z) * Pᵀ - c • z = z * (c • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2'] at this
      simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      rw [hs1]
      exact this
    have h3 := hU.impl g (u • z) Φ hΦ
    simp only [Darboux.rho, he, e2] at h3
    exact h3
  have hT : omd g (tens (evFin F v) vD RD) = tens (evFin F v) φ₁ RD := hA RD hRest
  rw [hS, hT]
  by_cases hR0 : RD = 0
  · refine ⟨0, ?_⟩
    funext x
    simp [tens, hR0]
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hR0

  set Λ := latDbl X Y v with hΛ
  set ch : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → ℂ := fun γ =>
    ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (dbl (incM F Y.J)) γ γ) with hch
  have hE0 : ∀ γ ∈ Λ, dd.rho ψ γ (tens (evFin F v) vD RD) = ch γ • tens (evFin F v) vD RD := by
    intro γ hγ
    have h1 := hvac _ hγ.1 r hr
    have h2 := hvac _ hγ.2 r hr
    rw [GlobalTheory.VacTransport.tens_smul] at h1 h2
    simp only [Darboux.rho] at h1 h2
    have h3 := hdc γ.toCols₁ γ.toCols₂
    rw [Matrix.fromCols_toCols] at h3
    rw [← hS, Darboux.rho, h3, schr_box_star ψ hstar, h1, h2]
    funext x
    simp only [hch, boxFun, Pi.smul_apply, smul_eq_mul, star_mul', hstar, symp_dbl, mul_sub, sub_eq_add_neg, mul_add,
      mul_neg, AddChar.map_add_eq_mul]
    ring
  have hE1 : ∀ γ ∈ Λ, dd.rho ψ γ (tens (evFin F v) φ₁ RD) = ch γ • tens (evFin F v) φ₁ RD := by
    intro γ hγ
    have hγ' : γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ ∈ Λ :=
      mul_transpose_mem_latDbl X Y v _ (fun z hz => (hg.2 z hz).2) hγ
    have hback : actB (cA σ) g (γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = γ := by
      change γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = γ
      have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
    have hsy : ch (γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = ch γ := by
      simp only [hch]
      rw [GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (dbl (incM F Y.J))
        (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 γ γ]
    have h1 := hU.impl g (γ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hRest.2
    rw [hback, hE0 _ hγ', hsy, map_smul, hT] at h1
    exact h1.symm

  have hAt : ∀ γ ∈ Λ, At (evFin F v) γ := at_latDbl X Y v
  let χ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo dd v γ = l then ch h.choose else 0
  have loc : ∀ f : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v) → ℂ,
      (∀ γ ∈ Λ, dd.rho ψ γ (tens (evFin F v) f RD) = ch γ • tens (evFin F v) f RD) →
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo dd v), ∀ ξ,
        GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf l hl ξ
    have h : ∃ γ ∈ Λ, GlobalTheory.LatVac.locCo dd v γ = l := AddSubgroup.mem_map.mp hl
    have key := local_identity v dd ψ h.choose f _ (hAt _ h.choose_spec.1) RD hRest.1 (hf _ h.choose_spec.1) x₀ hx₀ ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X Y v M.co hX hY
  have hsd' := GlobalTheory.LatVac.DualLoc.map_selfDual v dd ψ Λ hAt (latDbl_selfDual σ X Y v ψ hsd)
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo dd v)) c hc0 (fun x => hunr x) hsd'
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      have h3 := hdc γ.toCols₁ γ.toCols₂
      rw [Matrix.fromCols_toCols] at h3
      simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h3] at hcb ⊢
      rcases i with i | i
      · exact hcb _ hγ.1 i
      · refine ⟨(hcb _ hγ.2 i).1, ?_⟩
        simp only [Sum.elim_inr, Pi.neg_apply, map_neg, mul_neg]
        exact neg_mem (hcb _ hγ.2 i).2)
  obtain ⟨μ, hμ⟩ := GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt ψ v) (Λ.map (GlobalTheory.LatVac.locCo dd v)) χ vD φ₁
    (loc vD hE0) (loc φ₁ hE1) hvD0 hfill
  exact ⟨μ, by rw [hμ, GlobalTheory.VacTransport.tens_smul]⟩

theorem split_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ hunr dd omd hdc hsp r hr g hg
  exact dbl_eigen σ G.V G.W hT.geo.hV.lat.toIsLattice hT.geo.hW.lat.toIsLattice G.M B.ψ hT.base.std v hunr
    (GlobalTheory.PsiUnrSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v hunr) _ (hT.geo.hM.vac v) dd omd hdc hsp.2.1 r hr g hg

end GlobalTheory.DblVacAny

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunctionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeil_split_place_vacuum_eigenfunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.DblVacAny.split_eigen | exact GlobalTheory.DblVacAny.split_eigen | (intros; apply GlobalTheory.DblVacAny.split_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledStabilizerGeneratedDiagAntidiagSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitChoose

theorem isUnit_two_of_not_mem : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    IsUnit (2 : v.adicCompletionIntegers F) := by
  intro F _ _ v h
  have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h
  rwa [map_ofNat] at this

theorem exists_admissible_unipotent_splitPlace_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v hv hψ h2 g hg
  obtain ⟨π₁, π₂, b₁, b₂, hP, hS⟩ := GlobalTheory.T.exists_local_dictionary_splitPlace σ B W r s hB hW v hv hψ
  exact GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' σ W v hW.skew (isUnit_two_of_not_mem v h2) π₁ π₂ b₁ b₂ hP hS g hg

end GlobalTheory.SplitChoose
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_unipotent_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt | exact GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt | (intros; apply GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledStabilizerGeneratedDiagAntidiagSplitPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv hψ h2 _ H hD hA g hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ := GlobalTheory.T.exists_admissible_unipotent_splitPlace σ B G.W _ _ hT.base hT.geo.hW v hv hψ h2 g hg
  obtain ⟨p, hpK, hpD, hp⟩ := GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock σ G.W v h2 Y hYat hYlat hYadm
  obtain ⟨hpgK, hpg⟩ := hp g hg
  have hbig : GlobalTheory.DblVac.BigCell G.W v (p * g) := ⟨M, by rw [hpg]; exact hM, hMlat⟩
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ G.W v h2 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledStabilizerGeneratedDiagAntidiagSplitPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledStabilizer_generated_diag_antidiag_splitPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  first | exact @GlobalTheory.DblVac.gen_diag_anti_split | exact GlobalTheory.DblVac.gen_diag_anti_split | (intros; apply GlobalTheory.DblVac.gen_diag_anti_split <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitVac

theorem eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hs hv hψ h2 h3 k hk c hc
  obtain ⟨dd, omd, hdc, hsp, hbox⟩ := hT.weil.1.2
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.W) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledWeil_split_place_vacuum_eigenfunction F E σ B a a' G X om om' hT v hs hv hψ dd omd hdc hsp r hr p hp
    have h1 := GlobalTheory.T.doubledVacuum_eigenvalue_eq_one_splitPlace F E σ B a a' G X om om' hT v hs hv hψ dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.W v, q ∈ GlobalTheory.DblVac.PAnti σ G.W → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.W v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.doubledWeil_split_place_vacuum_eigenfunction F E σ B a a' G X om om' hT v hs hv hψ dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.W v k hk
  have hfix : omd gd S = S := GlobalTheory.T.doubledStabilizer_generated_diag_antidiag_splitPlace F E σ B a a' G X om om' hT v hs hψ h2 h3 H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inr _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inr_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.SplitVac
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LocVacFix

theorem bad_finite (F : Type) [Field F] [NumberField F] :
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | differentIdeal ℤ (𝓞 F) ≤ v.asIdeal ∨ (6 : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hd : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
    Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have h6 : {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) | v.asIdeal ∣ Ideal.span {(6 : 𝓞 F)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (show ((6 : ℕ) : 𝓞 F) ≠ 0 from Nat.cast_ne_zero.mpr (by norm_num))
  refine (hd.union h6).subset ?_
  rintro v (hv | hv)
  · exact Or.inl (Ideal.dvd_iff_le.mpr hv)
  · exact Or.inr (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv))

theorem two_three_of_six {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) : (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal := by
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply h6
    have e : (6 : 𝓞 F) = 3 * 2 := by norm_num
    rw [e]
    exact v.asIdeal.mul_mem_left 3 h
  refine ⟨h2, ?_⟩
  have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hz : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have ho : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  by_contra hle
  push_neg at hle
  generalize hN : Ideal.absNorm v.asIdeal = N at hmem hz ho hle
  interval_cases N
  · exact hz rfl
  · exact ho rfl
  · exact h2 (by exact_mod_cast hmem)
  · apply h6
    have e : (6 : 𝓞 F) = 2 * 3 := by norm_num
    rw [e]
    exact v.asIdeal.mul_mem_left 2 (by exact_mod_cast hmem)

theorem vac_fixed_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal → 3 < Ideal.absNorm v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hsp hvT hψ h2 h3 k hk
  obtain ⟨hSB, hne, θ, hθ, heig⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT v k hk.1 (G.M.vac v) hSB
  have heig₁ := GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ (G.M.vac v) hSB φ₁ hφ₁ heig hact
  obtain ⟨c, hc⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v hψ
    (GlobalTheory.PsiUnrSelfDual.latAtV_selfDual F E σ B a a' G X om om' hT v hψ) θ hθ (G.M.vac v) hSB hne heig
    φ₁ hφ₁ heig₁
  subst hc
  have hc1 : c = 1 := GlobalTheory.SplitVac.eigen_eq_one F E σ B a a' G X om om' hT v hsp hvT hψ h2 h3 k hk c hact
  rw [hc1, one_smul] at hact
  exact hact

end GlobalTheory.LocVacFix
