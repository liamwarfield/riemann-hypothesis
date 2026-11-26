module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordFMemFil
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.HTBasis

variable {l : ℕ} [Fact l.Prime]

def repOf {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) :
    Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp r)

theorem repOf_apply {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (v : Fin m → ↥LL.1) :
    repOf r g v = (r g : Matrix (Fin m) (Fin m) ↥LL.1).mulVec v := rfl

variable (P : LocPrime l) (LL : FinExt l) (m : ℕ)

def embF : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp LL.1.val

theorem embF_apply (x : ↥LL.1) : embF P LL x = algebraMap (Om l) P.R.BdR (x : Om l) := rfl

def mulF : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (embF P LL) (AlgHom.id ℚ_[l] P.R.BdR) fun _ _ => Commute.all _ _

@[simp] theorem mulF_tmul (c : ↥LL.1) (b : P.R.BdR) : mulF P LL (c ⊗ₜ[ℚ_[l]] b) = embF P LL c * b := by
  simp [mulF]

def coordF : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin m → P.R.BdR) :=
  TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : Fin m → ↥LL.1) (b : P.R.BdR) j => embF P LL (v j) * b)
    (fun v v' b => by funext j; simp [add_mul])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_assoc])
    (fun v b b' => by funext j; simp [mul_add])
    (fun c v b => by funext j; simp [Algebra.smul_def, mul_left_comm]))

@[simp] theorem coordF_tmul (v : Fin m → ↥LL.1) (b : P.R.BdR) :
    coordF P LL m (v ⊗ₜ[ℚ_[l]] b) = fun j => embF P LL (v j) * b := rfl

section Lemmas

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (m : ℕ)

theorem coordF_sm (r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) r x) = mulF P LL r • coordF P LL m x := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | add r s hr hs => simp only [map_add (f := _), LinearMap.add_apply, hr, hs, add_smul]
  | tmul c b =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
    | tmul v b' =>
      funext j
      simp only [GlobalTheory.DRFil.sm_tmul, coordF_tmul, mulF_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
      ring

theorem embF_mem_fil (K : FinExt l) (c : ↥LL.1) : embF P LL c ∈ (P.PD K).Fil 0 :=
  (GlobalTheory.DeRhamSymbol.mem_iff K 0 _).2 (GlobalTheory.DeRhamSymbol.om_mem _)

theorem coordF_mem_fil (K : FinExt l) {n : ℤ} {x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR}
    (hx : x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n) (j : Fin m) :
    coordF P LL m x j ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K (v j)) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_mem_fil (K : FinExt l) {n : ℤ} {r : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR}
    (hr : r ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) n) : mulF P LL r ∈ (P.PD K).Fil n := by
  obtain ⟨z, rfl⟩ := hr
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _)]; exact add_mem ha hb
  | tmul v b =>
    have := (P.PD K).Fil_mul 0 n _ _ (embF_mem_fil P LL K v) b.2
    rw [zero_add] at this
    simpa using this

theorem mulF_idem (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hτ : ∀ x : ↥K.1, ((τ x : ↥LL.1) : Om l) = (x : Om l)) :
    mulF P LL (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  have e : ∀ i, mulF P LL (a i ⊗ₜ[ℚ_[l]] algebraMap ↥K.1 P.R.BdR (c i)) =
      algebraMap (Om l) P.R.BdR (((a i * τ (c i) : ↥LL.1)) : Om l) := by
    intro i
    rw [mulF_tmul, embF_apply, IntermediateField.coe_mul, map_mul, hτ]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, ← map_sum]
  have h2 := congrArg (fun x : ↥LL.1 => (x : Om l)) h1
  simp only [IntermediateField.coe_sum, IntermediateField.coe_one] at h2
  simp only [IntermediateField.coe_mul] at h2 ⊢
  rw [h2, map_one]

theorem coordF_act (K : FinExt l) (r : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1)
    (g : ↥(GK K)) (hg : ∀ x ∈ LL.1, (g : GQ l) x = x) (x : (Fin m → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) :
    coordF P LL m (actVdR (P.PD K) (repOf r) g x) =
      ((r g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
        (fun j => P.actQdR (g : GQ l) (coordF P LL m x j)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero _).symm
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb, ← Matrix.mulVec_add]
    congr 1
    funext j
    simp only [Pi.add_apply, map_add]
  | tmul v b =>
    have hfix : ∀ c : ↥LL.1, P.actQdR (g : GQ l) (embF P LL c) = embF P LL c := fun c => by
      rw [embF_apply, P.actQdR_Om, hg _ c.2]
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [actVdR, AlgebraTensorModule.map_tmul, coordF_tmul, repOf_apply, P.PD_actdR,
      Matrix.mulVec, dotProduct, Matrix.map_apply, map_mul, hfix, map_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    rw [mul_assoc]
    exact congrArg _ (congrArg _ (P.PD_actdR K g b))

end Lemmas

section Theta

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

def thetaOf (T : LocTied l P AI) : Formalism.MainNotions.LocalSituation.ThetaL P AI :=
  (GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI T).some

def colHT (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ) :
    Matrix (Fin m) (Fin m) ℂ_[l] :=
  Matrix.of fun j i => J.θ (((GlobalTheory.DeRhamSymbol.tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j)

end Theta

end GlobalTheory.HTBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixIsUnitDet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixIsUnitDet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem colHT_isUnit_det {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ)
    (hu : ∀ i j, u i j ∈ (P.PD K).Fil (k i))
    (hspan : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i)
    (hli : LinearIndependent P.R.BdR u) : IsUnit (colHT J u k).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hc0
  set s : Fin m → Fin m → P.R.BdR := fun i j => ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) * u i j with hs
  have hs0 : ∀ i j, s i j ∈ (P.PD (botExt l)).Fil 0 := fun i j =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i j))
  choose γ hγ0 hγ using J.θ_onto
  set z : Fin m → P.R.BdR := fun j => ∑ i, γ (c i) * s i j with hz
  have hz0 : ∀ j, z j ∈ (P.PD (botExt l)).Fil 0 := fun j => by
    have := Submodule.sum_mem ((P.PD (botExt l)).Fil 0) (t := Finset.univ)
      (f := fun i => γ (c i) * s i j) fun i _ => by
        simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)
    exact this
  have hz1 : ∀ j, z j ∈ (P.PD K).Fil 1 := fun j => by
    rw [mem_iff K]
    refine (J.θ_ker _ (hz0 j)).1 ?_
    have h1 := congrFun hc j
    simp only [Matrix.mulVec, dotProduct, colHT, Matrix.of_apply, Pi.zero_apply] at h1
    rw [hz, GlobalTheory.DeRhamSymbolBasis.theta_sum J _ _ fun i => by
      simpa using (P.PD (botExt l)).Fil_mul 0 0 _ _ (hγ0 (c i)) (hs0 i j)]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [J.θ_mul _ (hγ0 (c i)) _ (hs0 i j), hγ, mul_comm]
  obtain ⟨f, hf, hfz⟩ := hspan 1 z hz1
  have hz' : z = ∑ i, (γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) • u i := by
    funext j
    simp only [hz, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hdiff := Fintype.linearIndependent_iff.1 hli
    (fun i => f i - γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR)) (by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hfz, ← hz', sub_self])
  funext i
  have hfi : f i = γ (c i) * ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) := sub_eq_zero.1 (hdiff i)
  have hγi : γ (c i) = f i * ((tU P ^ (k i) : P.R.BdRˣ) : P.R.BdR) := by
    rw [hfi, mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
  have hmem : γ (c i) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ ((mem_iff K _ _).1 (hf i)) (zpow_mem J (k i))
    rw [sub_add_cancel] at this
    rwa [hγi]
  rw [Pi.zero_apply, ← hγ (c i)]
  exact (J.θ_ker _ (hγ0 (c i))).2 hmem

end GlobalTheory.HTBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixIsUnitDetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K : FinExt l} {m : ℕ} (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) → ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) → LinearIndependent P.R.BdR u → IsUnit (colHT J u k).det := by
  first | (exact @GlobalTheory.HTBasis.colHT_isUnit_det) | (exact GlobalTheory.HTBasis.colHT_isUnit_det) | (intros; apply GlobalTheory.HTBasis.colHT_isUnit_det  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

noncomputable section

namespace GlobalTheory.HTBasis

open GlobalTheory.DeRhamSymbol GlobalTheory.DeRhamSymbolBasis

theorem colHT_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI J K LL m r' u k hu g hg
  ext j i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [Matrix.map_apply, colHT, Matrix.of_apply]
  set M := (r' g : Matrix (Fin m) (Fin m) ↥LL.1) with hM
  set t : P.R.BdR := ((tU P ^ (-k i) : P.R.BdRˣ) : P.R.BdR) with ht
  set q : ℚ_[l] := ((P.χQ (g : GQ l) ^ k i : ℚ_[l]ˣ) : ℚ_[l]) with hq
  have key : ∀ x, t * u i x ∈ (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x =>
    (shift_iff J (k i) 0 _).2 (by rw [add_zero]; exact (mem_iff K _ _).1 (hu i x))
  have hmem : ∀ x, algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x) ∈
      (P.PD (Formalism.MainNotions.LocalSituation.botExt l)).Fil 0 := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
    exact om_mul_mem _ (act_mem _ (key x))
  have h1 := congrFun (hg i) j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, embF_apply] at h1
  have h2 : t * u i j = ∑ x, algebraMap (Om l) P.R.BdR ((M j x : ↥LL.1) : Om l) *
      (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) := by
    conv_lhs => rw [← h1]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_left_comm, shift_act]
  have h3 : ∀ x, J.θ (algebraMap ℚ_[l] P.R.BdR q * P.actQdR (g : GQ l) (t * u i x)) =
      (q : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)) := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR,
      J.θ_mul _ (om_mem _) _ (act_mem _ (key x)), J.θ_Om, J.θ_act _ _ (key x),
      GlobalTheory.MemLoc.TiedTheta.actC_eq]
  have hunit : (q : ℂ_[l]) * ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = 1 := by
    have e : q * (((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) = 1 := by
      rw [hq, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
    have e2 := congrArg (fun z : ℚ_[l] => (z : ℂ_[l])) e
    rw [map_mul, UniformSpace.Completion.coe_mul, map_one, UniformSpace.Completion.coe_one] at e2
    exact e2
  rw [h2, theta_comb J _ _ hmem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h3]
  linear_combination (-((((M j x : ↥LL.1) : Om l) : ℂ_[l]) * Per.σC (g : GQ l) (J.θ (t * u i x)))) * hunit

end GlobalTheory.HTBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariantStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.colHT_equivariant) | (exact GlobalTheory.HTBasis.colHT_equivariant) | (intros; apply GlobalTheory.HTBasis.colHT_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasis
noncomputable section

namespace GlobalTheory.HTBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_dR_frame : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1),
    Module.finrank ↥LL.1 ↥(DdR (P.PD K) (repOf r')) = Module.finrank ℚ_[l] ↥K.1 * m →
    ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) →
    ∃ (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ),
      (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) (repOf r') τ' a) ∧
      (∀ i j, u i j ∈ (P.PD K).Fil (k i)) ∧
      (∀ g : ↥(GK K), (∀ x ∈ LL.1, (g : GQ l) x = x) → ∀ i,
        ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec
          (fun j => P.actQdR (g : GQ l) (u i j)) = u i) ∧
      (∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
        ∃ f : Fin m → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u i) ∧
      LinearIndependent P.R.BdR u := by
  intro l _ P AI T K LL m r' hdR τ' hτ
  haveI := K.2
  haveI := LL.2
  have hDR : IsDR (P.PD K) (repOf r') := by
    unfold IsDR
    rw [hdR, Module.finrank_fin_fun]
  haveI hfinD : FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) (repOf r')) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · haveI : Subsingleton ((Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) := ⟨fun x y => by
        have h : ∀ z : (Fin 0 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add a b ha hb => rw [ha, hb, add_zero]
        rw [h x, h y]⟩
      infer_instance
    · exact Module.finite_of_finrank_pos (by rw [hdR]; exact Nat.mul_pos Module.finrank_pos hm)
  obtain ⟨m', d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) (repOf r')
    (GlobalTheory.DRFil.filSpans T K LL (repOf r') hDR) τ'
  let u' : Fin m' → Fin m → P.R.BdR := fun i => coordF P LL m (d i)
  have hspan' : ∀ (n : ℤ) (y : Fin m → P.R.BdR), (∀ j, y j ∈ (P.PD K).Fil n) →
      ∃ f : Fin m' → P.R.BdR, (∀ i, f i ∈ (P.PD K).Fil (n - k i)) ∧ y = ∑ i, f i • u' i := by
    intro n y hy
    have hY : (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) ∈
        FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) n :=
      Submodule.sum_mem _ fun j _ => GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (hy j)
    have hcY : coordF P LL m (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j) = y := by
      funext j'
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finset.sum_apply, Pi.single_apply]
    obtain ⟨r, hr, he⟩ := had.span n _ hY
    refine ⟨fun i => mulF P LL (r i), fun i => mulF_mem_fil P LL K (hr i), ?_⟩
    have e1 := coordF_sm P LL m (GlobalTheory.DRFil.idem P.R.BdR τ')
      (∑ j, (Pi.single j 1 : Fin m → ↥LL.1) ⊗ₜ[ℚ_[l]] y j)
    rw [mulF_idem P LL K τ' hτ, one_smul, hcY] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1, he, map_sum]
    exact Finset.sum_congr rfl fun i _ => coordF_sm P LL m (r i) (d i)
  have htop : ⊤ ≤ Submodule.span P.R.BdR (Set.range u') := by
    rintro y -
    choose f hf using fun j => (P.PD K).Fil_exh (y j)
    have hn : ∀ j, y j ∈ (P.PD K).Fil (-(∑ j, |f j|)) := by
      intro j
      have hle : -(∑ j, |f j|) ≤ f j := by
        have h1 : |f j| ≤ ∑ j, |f j| :=
          Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 := neg_abs_le (f j)
        linarith
      exact SetLike.le_def.1 (GlobalTheory.DRFil.fil_antitone (P.PD K) hle) (hf j)
    obtain ⟨c, -, hc⟩ := hspan' _ y hn
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  letI : Field P.R.BdR := (GlobalTheory.DRFil.isField_dR T).toField
  have hle1 : m ≤ m' := by
    have h1 := finrank_range_le_card (R := P.R.BdR) u'
    rw [Set.finrank, eq_top_iff.2 htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hle2 : m' ≤ m := by
    have := GlobalTheory.Per.Components.card_le_of_idem_indep (GlobalTheory.DRFil.idem_mul_idem (F := P.R.BdR) τ')
      (GlobalTheory.DRFil.idem_ne_zero (F := P.R.BdR) τ')
      (fun i j => GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥LL.1 (Fin m)).coord j) (d i))
      (fun r hr => had.indep r (by
        rw [GlobalTheory.DRFil.eq_sum_basis (Pi.basisFun ↥LL.1 (Fin m))
          (∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥LL.1 (Fin m → ↥LL.1) (r i) (d i))]
        refine Finset.sum_eq_zero fun j _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self]
        rw [hr j, map_zero, LinearMap.zero_apply]))
    simpa using this
  obtain rfl : m = m' := le_antisymm hle1 hle2
  have hind : LinearIndependent P.R.BdR u' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨u', k, fun a => ?_, fun i j => coordF_mem_fil P LL m K (had.mem i).2 j, fun g hg i => ?_,
    hspan', hind⟩
  · rw [had.multV_eq a, Multiset.count_map]
    simp [Finset.sum_boole, eq_comm]
    rfl
  · have h1 := coordF_act P LL m K r' g hg (d i)
    rw [((GlobalTheory.DRFil.mem_DdR (P.PD K) (repOf r') (d i)).1 (had.mem i).1.1) g] at h1
    exact h1.symm

end GlobalTheory.HTBasis

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.HTBasis.htc_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  intro l _ P AI T K LL m r' ρ hdR τ' hτ K' _hK hL
  obtain ⟨u, k, hcount, hmem, heq, hspan, hind⟩ :=
    GlobalTheory.HTBasis.exists_dR_frame l P AI T K LL m r' hdR τ' hτ
  have hU := GlobalTheory.T.hodgeTateSymbolMatrix_isUnit_det (GlobalTheory.HTBasis.thetaOf T) u k hmem hspan hind
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hU).unit, k, hcount, fun g hg => ?_⟩
  have hfix : ∀ x ∈ LL.1, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (hL hx)
  exact GlobalTheory.T.hodgeTateSymbolMatrix_equivariant (GlobalTheory.HTBasis.thetaOf T) r' u k hmem g (heq g hfix)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem _root_.GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → (∀ (σ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), σ x ∈ LL.1) → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.htc_basis) | (exact GlobalTheory.HTBasis.htc_basis) | (intros; apply GlobalTheory.HTBasis.htc_basis  <;> assumption)
end
