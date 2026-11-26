module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfMemSpectrumFrobeniusMatrixFilZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrystallinePeriodMatrixMemFilZeroOfWeightZero
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Coord

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V]
    (ρ : Representation Qp G V) {d : ℕ} (e : Basis (Fin d) Qp V)

private theorem coord_sum (c : Fin d → BdR) (i : Fin d) :
    (TensorProduct.lid Qp BdR) (LinearMap.rTensor BdR (e.coord i) (∑ j, e j ⊗ₜ[Qp] c j)) = c i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj]
  · simp

private theorem sum_mem_fil_iff (a : ℤ) (c : Fin d → BdR) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ FilV PD (LL := Qp) (V := V) a ↔ ∀ i, c i ∈ PD.Fil a := by
  constructor
  · rintro ⟨z, hz⟩ i
    rw [← coord_sum e c i, ← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v x =>
      have := ((PD.Fil a).restrictScalars Qp).smul_mem (e.coord i v) x.2
      simpa using this
    | add x y hx hy =>
      simp only [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · intro h
    exact Submodule.sum_mem _ fun j _ => ⟨e j ⊗ₜ ⟨c j, h j⟩, rfl⟩

private theorem sum_mem_DdR (c : Fin d → BdR)
    (h : ∀ g, ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)).mulVec (fun j => PD.actdR g (c j)) = c) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro g
  conv_rhs => rw [← h g]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Matrix.mulVec, dotProduct, tmul_sum, Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ρ g (e j) ⊗ₜ[Qp] PD.actdR g (c j) = _
  conv_lhs => rw [← e.sum_repr (ρ g (e j))]
  rw [sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_tmul, Algebra.smul_def]

private theorem core
    (hinv : ∀ a b, b ∈ PD.Fil a → b ∉ PD.Fil (a + 1) → ∃ β ∈ PD.Fil (-a), β * b - 1 ∈ PD.Fil 1)
    (hT : ∀ n x, x ∈ PD.Fil n → (∀ g, PD.actdR g x - x ∈ PD.Fil (n + 1)) →
      ∃ κ ∈ PD.Fil 0, (∀ g, PD.actdR g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ x - κ ∈ PD.Fil (n + 1))
    (h0 : DdR PD ρ ≤ FilV PD (LL := Qp) (V := V) 0) (h1 : DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 = ⊥)
    (N N' : Matrix (Fin d) (Fin d) BdR) (hN : N * N' = 1)
    (hg : ∀ g, (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR) * N.map (PD.actdR g) = N) :
    (∀ i j, N i j ∈ PD.Fil 0) ∧ ∀ i j, N' i j ∈ PD.Fil 0 := by
  let A : G → Matrix (Fin d) (Fin d) BdR := fun g => (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)
  have hA : ∀ g i j, A g i j ∈ PD.Fil 0 := fun g i j => by
    change algebraMap Qp BdR _ ∈ _
    rw [IsScalarTower.algebraMap_apply Qp K BdR, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ PD.one_mem
  have hcol : ∀ j g, (A g).mulVec (fun i => PD.actdR g (N i j)) = fun i => N i j := fun j g => by
    funext i
    exact congrFun (congrFun (hg g) i) j
  have hN' : N' * N = 1 := mul_eq_one_comm.1 hN
  have hA' : ∀ g, N' * A g = N'.map (PD.actdR g) := fun g => by
    have h2 : N.map (PD.actdR g) * N'.map (PD.actdR g) = 1 := by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) BdR => X.map (PD.actdR g : BdR →+* BdR)) hN
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    calc N' * A g = N' * A g * (N.map (PD.actdR g) * N'.map (PD.actdR g)) := by rw [h2, mul_one]
      _ = N' * (A g * N.map (PD.actdR g)) * N'.map (PD.actdR g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg g, hN', one_mul]
  refine ⟨fun i j => (sum_mem_fil_iff PD e 0 (fun i => N i j)).1 (h0 (sum_mem_DdR PD ρ e _ (hcol j))) i,
    fun i j => ?_⟩
  have hFa : Antitone fun a => (PD.Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => PD.Fil_anti a
  let R : G → (Fin d → BdR) →+ (Fin d → BdR) := fun g =>
    { toFun := fun c => (A g).mulVec (fun j => PD.actdR g (c j))
      map_zero' := by simp [← Pi.zero_def]
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]
        congr 1
        funext j
        simp }
  let FM : ℤ → AddSubgroup (Fin d → BdR) := fun a => AddSubgroup.pi Set.univ fun _ => (PD.Fil a).toAddSubgroup
  have hFM : ∀ a c, c ∈ FM a ↔ ∀ i, c i ∈ PD.Fil a := fun a c => by
    simp [FM, AddSubgroup.mem_pi]
  obtain ⟨m, k, b, c, h, hs⟩ := GlobalTheory.DRFil.filtered (G := G) (fun g => (PD.actdR g : BdR →+* BdR)) R
    (fun a => (PD.Fil a).toAddSubgroup) FM
    (fun g b x => by
      change (A g).mulVec _ = _ • (A g).mulVec _
      rw [← Matrix.mulVec_smul]
      congr 1
      funext j
      simp)
    PD.Fil_mul
    (fun a c x z hx hz => (hFM _ _).2 fun i => PD.Fil_mul _ _ _ _ hx ((hFM _ _).1 hz i))
    PD.Fil_G
    (fun g a z hz => (hFM _ _).2 fun i => by
      change ∑ j, A g i j * PD.actdR g (z j) ∈ _
      refine Submodule.sum_mem _ fun j _ => ?_
      have := PD.Fil_mul _ _ _ _ (hA g i j) (PD.Fil_G g _ _ ((hFM _ _).1 hz j))
      rwa [zero_add] at this)
    hinv hT hFa (fun a a' h z hz => (hFM _ _).2 fun i => hFa h ((hFM _ _).1 hz i)) PD.Fil_exh
    (fun x => by
      choose r hr using fun i => PD.Fil_exh (x i)
      obtain ⟨a, ha⟩ := (Set.finite_range r).bddBelow
      exact ⟨a, (hFM _ _).2 fun i => hFa (ha ⟨i, rfl⟩) (hr i)⟩)
    0 (fun i => (1 : Matrix (Fin d) (Fin d) BdR) i j)
    ((hFM _ _).2 fun i => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [PD.one_mem, Submodule.zero_mem _])
    d (fun i => N' i j) (fun j i => N i j) (fun j g => hcol j g)
    (by
      funext i
      rw [← hN, Matrix.mul_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _)
  have h3 : N' i j = ∑ n, b n * N'.mulVec (c n) i := by
    have h4 := congrFun (congrArg N'.mulVec hs) i
    rw [Matrix.mulVec_sum, Finset.sum_apply] at h4
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h4
    rw [← h4]
    exact (congrFun (congrFun (mul_one N') i) j).symm
  rw [h3]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨hc, hk, hb⟩ := h n
  by_cases hk1 : 1 ≤ k n
  · have h5 : ∑ j, e j ⊗ₜ[Qp] c n j ∈ DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 :=
      ⟨sum_mem_DdR PD ρ e _ hc, (sum_mem_fil_iff PD e 1 _).2 fun i => hFa hk1 ((hFM _ _).1 hk i)⟩
    rw [h1, Submodule.mem_bot] at h5
    have h6 : c n = 0 := funext fun i => by
      rw [← coord_sum e (c n) i, h5]
      simp
    rw [h6]
    simp
  · have h5 : b n ∈ PD.Fil 0 := hFa (show (0 : ℤ) ≤ 0 - k n by omega) hb
    obtain ⟨κ, hκ⟩ := PD.invdR (N'.mulVec (c n) i) fun g => by
      have h6 : (A g).mulVec (fun j => PD.actdR g (c n j)) = c n := hc g
      conv_rhs => rw [← h6, Matrix.mulVec_mulVec, hA' g]
      simp [Matrix.mulVec, dotProduct]
    have h6 : N'.mulVec (c n) i ∈ PD.Fil 0 := by
      rw [← hκ, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ PD.one_mem
    simpa using PD.Fil_mul _ _ _ _ h5 h6

end Coord

theorem UpperTheory.crystalline_period_matrix_mem_fil_zero_of_weight_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → DdR ((PP l).PD K) ρ ≤ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 0 → DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) 1 = ⊥ → ∀ (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → (∀ i j, (PP l).ιB (M i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ ∀ i j, (PP l).ιB (M' i j) ∈ ((PP l).PD (botExt l)).Fil 0 := by
  intro l _ K V _ _ _ ρ d e _ h0 h1 M M' hM hg
  obtain ⟨T⟩ := tiedP l
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
  have key := core ((PP l).PD K) ρ e (GlobalTheory.DRFil.graded_inv Θ K) (GlobalTheory.DRFil.graded_invariants T Θ K) h0 h1
    (M.map (PP l).ιB) (M'.map (PP l).ιB)
    (by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) (Bcr l) => X.map ((PP l).ιB : Bcr l →+* Bdr l)) hM
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this)
    (fun g => by
      ext i j
      have := congrArg (PP l).ιB (congrFun (congrFun (hg g) i) j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, ← this, Matrix.mul_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Matrix.map_apply, map_mul, AlgHom.commutes]
      rw [← (PP l).PD_actB K g, ← (PP l).PD_ι K, ← (PP l).PD_ι K, ((PP l).PD K).ι_comm])
  exact ⟨fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (key.1 i j), fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (key.2 i j)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCrystallinePeriodMatrixBcrisOfIsCrys
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Generic

open GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V] [IsDomain B]

private theorem exists_inv_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ M M' : Matrix (Fin d) (Fin d) B, M * M' = 1 ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  classical
  obtain ⟨h1, -⟩ := finite_le₀ PD hf ρ
  have h2 : finrank K₀ ↥(DcrisK₀ PD ρ) = d := by
    rw [(isCrys_iff_finrank PD ρ).1 h, finrank_eq_card_basis v, Fintype.card_fin]
  let d₀ := Module.finBasisOfFinrankEq K₀ ↥(DcrisK₀ PD ρ) h2
  let b := (Algebra.TensorProduct.basis B d₀).map
    (LinearEquiv.ofBijective _ (comparison_bijective PD hf hu ρ h))
  have hd : ∀ g i, sig PD ρ g (b i) = b i := by
    intro g i
    have : b i = (d₀ i : B ⊗[Qp] V) := by simp [b, comparison_tmul]
    rw [this]
    exact (mem_DcrisK₀ PD ρ _).1 (d₀ i).2 g
  let e := Algebra.TensorProduct.basis B v
  have hrep : ∀ g (w : B ⊗[Qp] V) k, e.repr (sig PD ρ g w) k =
      ∑ j, algebraMap Qp B (v.repr (ρ g (v j)) k) * PD.actB g (e.repr w j) := by
    intro g w k
    conv_lhs => rw [← e.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, sig_smul, map_smul, Finset.sum_apply', Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, sig_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext k i
  rw [Matrix.mul_apply]
  change _ = e.repr (b i) k
  conv_rhs => rw [← hd g i, hrep]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply]

private theorem exists_period_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ (M M' : Matrix (Fin d) (Fin d) B) (A : Matrix (Fin d) (Fin d) K₀), M * M' = 1 ∧ IsUnit A.det ∧
      M.map PD.φ = M * A.map (algebraMap K₀ B) ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  obtain ⟨M, M', hM, hg⟩ := exists_inv_matrix PD hf hu ρ v h
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hinv : ∀ g, (M' * M.map PD.φ).map (PD.actB g) = M' * M.map PD.φ := by
    intro g
    set R := (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) with hR
    have h1 : M.map (PD.actB g) * M'.map (PD.actB g) = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : M'.map (PD.actB g) = M' * R := by
      have : R * (M.map (PD.actB g) * M'.map (PD.actB g)) = M * M'.map (PD.actB g) := by
        rw [← Matrix.mul_assoc, hg g]
      rw [h1, Matrix.mul_one] at this
      rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]
    have h3 : R * (M.map PD.φ).map (PD.actB g) = M.map PD.φ := by
      have h4 : R.map PD.φ = R := by
        ext i j
        simp [hR]
      have h5 : (M.map PD.φ).map (PD.actB g) = (M.map (PD.actB g)).map PD.φ := by
        ext i j
        simp [PD.φ_comm]
      rw [h5, ← h4, ← Matrix.map_mul, hg g]
    rw [Matrix.map_mul, h2, Matrix.mul_assoc, h3]
  choose A hA using fun i j => PD.invB ((M' * M.map PD.φ) i j) fun g => congrFun (congrFun (hinv g) i) j
  have hA' : (Matrix.of A).map (algebraMap K₀ B) = M' * M.map PD.φ := by
    ext i j
    exact hA i j
  refine ⟨M, M', Matrix.of A, hM, ?_, by rw [hA', ← Matrix.mul_assoc, hM, Matrix.one_mul], hg⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 : ((Matrix.of A).map (algebraMap K₀ B)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2 : (M' * M.map PD.φ) * (M'.map PD.φ * M) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M.map PD.φ), ← Matrix.map_mul, hM,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hM']
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, ← hA', h1, zero_mul, Matrix.det_one] at h3
  exact zero_ne_one h3

end Generic

theorem UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → ∃ (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 ∧ IsUnit A.det ∧ M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) ∧ (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) := by
  intro l _ K V _ _ _ ρ d e h
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨M, M', A, h1, h2, h3, h4⟩ := exists_period_matrix ((PP l).PD K)
    (GlobalTheory.TateDualCrys.fracInv_of_tied T K) (GlobalTheory.TateDualCrys.lineUnit_of_tied T K) ρ e h
  refine ⟨M, M', A, h1, h2, ?_, fun g => ?_⟩
  · rw [← h3]
    ext i j
    exact ((PP l).PD_φ K _).symm
  · have h5 : M.map ((PP l).actQ (g : GQ l)) = M.map (((PP l).PD K).actB g) := by
      ext i j
      exact ((PP l).PD_actB K g _).symm
    rw [h5, h4]
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

namespace UpperTheory.V.Loc

open Polynomial

variable {l : ℕ} [Fact l.Prime]

private def wtS (l : ℕ) [Fact l.Prime] : Subring (Bcr l) where
  carrier := {b | (PP l).ιB b ∈ ((PP l).PD (botExt l)).Fil 0}
  mul_mem' := fun {a b} ha hb => by
    have := ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ ha hb
    rw [add_zero, ← map_mul] at this
    exact this
  one_mem' := by
    change (PP l).ιB 1 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_one]; exact ((PP l).PD (botExt l)).one_mem
  add_mem' := fun {a b} ha hb => by
    change (PP l).ιB (a + b) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    change (PP l).ιB 0 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha => by
    change (PP l).ιB (-a) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_neg]; exact Submodule.neg_mem _ ha

private theorem wt_alg (K : FinExt l) (c : ↥(K0 K)) : algebraMap ↥(K0 K) (Bcr l) c ∈ wtS l := by
  have h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0 := by
    rw [← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact (((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem
  have h2 := (PP l).PD_Fil K (botExt l) 0
  change (PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)
  rw [← h2]
  exact h

private theorem wt_phi (K : FinExt l) (c : ↥(K0 K)) :
    (PP l).φB (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) (((PP l).PD K).σ c) := by
  rw [← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]

private theorem wt_iter (K : FinExt l) {d : ℕ} (M : Matrix (Fin d) (Fin d) (Bcr l))
    (A : Matrix (Fin d) (Fin d) ↥(K0 K)) (hA : IsUnit A.det)
    (h : M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l))) (k : ℕ) :
    ∃ F : Matrix (Fin d) (Fin d) ↥(K0 K), IsUnit F.det ∧
      M.map (((PP l).φB)^[k]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨F, hF, e⟩ := ih
    refine ⟨A * F.map ((PP l).PD K).σ, ?_, ?_⟩
    · rw [Matrix.det_mul]
      refine hA.mul ?_
      have := hF.map (((PP l).PD K).σ : ↥(K0 K) →+* ↥(K0 K))
      rw [RingHom.map_det] at this
      exact this
    · rw [Function.iterate_succ', ← Matrix.map_map, e, Matrix.map_mul, h, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact wt_phi K _

private theorem wt_spec {L : Type} [Field L] {d : ℕ} (G : Matrix (Fin d) (Fin d) L) (hG : IsUnit G.det) {a : L}
    (ha : a ∈ spectrum L G) : a ≠ 0 ∧ a⁻¹ ∈ spectrum L (G⁻¹).transpose := by
  rw [spectrum.mem_iff] at ha
  have h0 : a ≠ 0 := by
    rintro rfl
    apply ha
    rw [map_zero, zero_sub]
    exact ((Matrix.isUnit_iff_isUnit_det _).2 hG).neg
  refine ⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩
  have e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) =
      algebraMap L (Matrix (Fin d) (Fin d) L) a - G := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_mul,
      mul_inv_cancel₀ h0, neg_smul, neg_smul, one_smul]
    abel
  rw [← e]
  refine ((Matrix.isUnit_transpose _).2 hu).mul ?_
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact ((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG

private theorem wt_aeval (K : FinExt l) (ψ : Bcr l →ₐ[ℚ_[l]] Bcr l)
    (hψ : ∀ c : ↥(K0 K), ψ (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) c) {d : ℕ}
    (M : Matrix (Fin d) (Fin d) (Bcr l)) (F : Matrix (Fin d) (Fin d) ↥(K0 K))
    (h : M.map ψ = M * F.map (algebraMap ↥(K0 K) (Bcr l))) (Q : ℚ_[l][X]) :
    M.map (aeval (ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) Q) =
      M * (aeval F (Q.map (algebraMap ℚ_[l] ↥(K0 K)))).map (algebraMap ↥(K0 K) (Bcr l)) := by
  have hp : ∀ n : ℕ, M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n) =
      M * (F ^ n).map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      rfl
    | succ n ih =>
      have e : M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ (n + 1)) =
          (M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n)).map ψ := by
        ext i j
        rw [pow_succ']
        rfl
      rw [e, ih, Matrix.map_mul, h, pow_succ', Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact hψ _
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), Matrix.map_add _ (map_add _), Matrix.mul_add, ← hp, ← hq]
    rfl
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
    ext i j
    have := congrFun (congrFun (hp n) i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.map_apply, Matrix.mul_apply, LinearMap.smul_apply, this, Matrix.smul_apply, smul_eq_mul,
      map_mul, ← IsScalarTower.algebraMap_apply]
    rw [Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

private theorem wt_matFix (K : FinExt l) {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l))
    (A : Matrix (Fin d) (Fin d) ↥(K0 K)) (hMM : M * M' = 1) (hM : ∀ i j, M i j ∈ wtS l)
    (hM' : ∀ i j, M' i j ∈ wtS l) (hA : IsUnit A.det)
    (h : M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l))) :
    ∀ g ∈ Iq l, M.map ((PP l).actQ g) = M := by
  haveI := ((PP l).PD K).finK₀
  let s : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) := AlgEquiv.ofBijective ((PP l).PD K).σ ((PP l).PD K).σ_bij
  have hf : 0 < orderOf s := orderOf_pos s
  have hσ : ∀ x : ↥(K0 K), (((PP l).PD K).σ)^[orderOf s] x = x := fun x => by
    have := AlgEquiv.congr_fun (pow_orderOf_eq_one s) x
    rw [AlgEquiv.coe_pow] at this
    exact this
  generalize orderOf s = f at hf hσ
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k) := fun k => (AlgHom.coe_pow _ _).symm
  choose F hF hMF using wt_iter K M A hA h
  have hinv : ∀ k, M'.transpose.map (((PP l).φB)^[k]) =
      M'.transpose * ((F k)⁻¹).transpose.map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro k
    rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]
    congr 1
    have e1 : M'.map (((PP l).φB)^[k]) * M.map (((PP l).φB)^[k]) = 1 := by
      rw [hc, ← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : (F k).map (algebraMap ↥(K0 K) (Bcr l)) * ((F k)⁻¹).map (algebraMap ↥(K0 K) (Bcr l)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF k), Matrix.map_one _ (map_zero _) (map_one _)]
    calc M'.map (((PP l).φB)^[k]) = M'.map (((PP l).φB)^[k]) * (M * ((F k).map (algebraMap ↥(K0 K) (Bcr l)) *
          ((F k)⁻¹).map (algebraMap ↥(K0 K) (Bcr l))) * M') := by rw [e2, Matrix.mul_one, hMM, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc M, ← hMF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hS : ∀ (N : Matrix (Fin d) (Fin d) (Bcr l)) (E : Matrix (Fin d) (Fin d) ↥(K0 K)) (k : ℕ),
      (∀ i j, N i j ∈ wtS l) → N.map (((PP l).φB)^[k]) = N * E.map (algebraMap ↥(K0 K) (Bcr l)) →
      ∀ i j, ((PP l).φB)^[k] (N i j) ∈ wtS l := by
    intro N E k hN e i j
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this]
    exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (hN _ _) (wt_alg K _)
  have h1 := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M M' (F f) hMM' (fun k => hS M (F k) k hM (hMF k)) (hMF f)
  have h2 := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M'.transpose M.transpose ((F f)⁻¹).transpose
    (by rw [← Matrix.transpose_mul, hMM', Matrix.transpose_one])
    (fun k => hS M'.transpose _ k (fun i j => hM' j i) (hinv k)) (hinv f)
  obtain ⟨P, hP, hP0, hPF⟩ := UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one (K0 K) (F f) (fun a ha => by
    have hu : IsUnit ((F f).map (algebraMap ↥(K0 K) (Om l))).det := by
      have := (hF f).map (algebraMap ↥(K0 K) (Om l))
      rw [RingHom.map_det] at this
      exact this
    obtain ⟨h0, ha'⟩ := wt_spec _ hu ha
    have e : ((F f).map (algebraMap ↥(K0 K) (Om l)))⁻¹ = ((F f)⁻¹).map (algebraMap ↥(K0 K) (Om l)) := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF f), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, ← Matrix.transpose_map] at ha'
    have h3 := h2 _ ha'
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact le_antisymm (h1 a ha) h3)
  have hfix : ∀ (k : ℕ) (c : ↥(K0 K)), ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c) := by
    intro k
    induction k with
    | zero => intro c; rfl
    | succ k ih => intro c; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, wt_phi]
  have h4 := wt_aeval K ((PP l).φB ^ f) (fun c => by rw [← hc, hfix, hσ]) M (F f) (by rw [← hc]; exact hMF f)
    (P.map (algebraMap ℤ_[l] ℚ_[l]))
  rw [Polynomial.map_map, hPF, Matrix.map_zero _ (map_zero _), Matrix.mul_zero] at h4
  intro g hg
  ext i j
  refine UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero (expand ℤ_[l] f P) (hP.expand hf) (by rwa [coeff_expand hf, if_pos (dvd_zero _), Nat.zero_div])
    (M i j) ?_ (fun k => hS M (F k) k hM (hMF k) i j) g hg
  have e : ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ f = ((PP l).φB ^ f).toLinearMap := by
    ext x
    rw [Module.End.pow_apply, AlgHom.toLinearMap_apply, ← hc]
    rfl
  rw [Polynomial.map_expand, expand_aeval, e]
  exact congrFun (congrFun h4 i) j

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.crWt0 :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → IsCr φ ρ → FilD φ ρ 0 = Ddr φ ρ → FilD φ ρ 1 = ⊥ → ∀ g, φ g ∈ Iq l → ρ g = 1 := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ _ hcr h0 h1 g hg
  obtain ⟨K, e, -, -, he, -, -, hidx⟩ := openField φ hφ
  have he' : ∀ x, ((e x : ↥(GK K)) : GQ l) = φ x := fun x => DFunLike.congr_fun he x
  let ρ' : Representation ℚ_[l] ↥(GK K) V := (resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom
  have hB : ∀ x y, actVB ((PP l).PD K) ρ' (e x) y = actC φ (resCoef ℚ_[l] ρ) x y := by
    intro x y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ (e.symm (e x)) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actB (e x) b = ρ x v ⊗ₜ[ℚ_[l]] (PP l).actQ (φ x) b
      rw [(PP l).PD_actB, he', e.symm_apply_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hD : ∀ x y, actVdR ((PP l).PD K) ρ' (e x) y = actD φ ρ x y := by
    intro x y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ (e.symm (e x)) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actdR (e x) b = ρ x v ⊗ₜ[ℚ_[l]] (PP l).actQdR (φ x) b
      rw [(PP l).PD_actdR, he', e.symm_apply_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hC : Dcris ((PP l).PD K) ρ' = Dcr φ (resCoef ℚ_[l] ρ) := by
    ext y
    simp only [Dcris, Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      e.surjective.forall, hB]
  have hDD : ∀ y, y ∈ DdR ((PP l).PD K) ρ' ↔ y ∈ Ddr φ ρ := by
    intro y
    simp only [DdR, Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      e.surjective.forall, hD]
  have hFil : ∀ a, (((PP l).PD K).Fil a).restrictScalars ℚ_[l] =
      (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] := fun a =>
    SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)
  have hF : ∀ a y, y ∈ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a ↔ y ∈ FilT A V a := by
    intro a y
    unfold FilV FilT
    rw [hFil]
    exact Iff.rfl
  have hcrys : IsCrys ((PP l).PD K) ρ' := by
    unfold IsCrys
    rw [hC, ← hidx]
    exact hcr
  let b := Module.finBasis ℚ_[l] V
  obtain ⟨M, M', A', hMM, hA, hφM, hρ⟩ := UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys K ρ' b hcrys
  obtain ⟨hM, hM'⟩ := UpperTheory.crystalline_period_matrix_mem_fil_zero_of_weight_zero K ρ' b hcrys
    (fun y hy => (hF 0 y).2 ((h0.ge ((hDD y).1 hy)).2))
    (eq_bot_iff.2 fun y hy => h1.le ⟨(hDD y).1 hy.1, (hF 1 y).1 hy.2⟩) M M' hMM hρ
  have h2 := hρ (e g)
  rw [he', wt_matFix K M M' A' hMM hM hM' hA hφM _ hg] at h2
  have h3 := congrArg (· * M') h2
  simp only [Matrix.mul_assoc, hMM, Matrix.mul_one] at h3
  haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
    rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
  have h4 : LinearMap.toMatrix b b (ρ' (e g)) = 1 := by
    apply Matrix.map_injective (algebraMap ℚ_[l] (Bcr l)).injective
    change Matrix.map _ _ = Matrix.map _ _
    rw [h3, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← LinearMap.toMatrix_one b] at h4
  have h5 := (LinearMap.toMatrix b b).injective h4
  ext v
  have h6 : ρ (e.symm (e g)) v = v := LinearMap.congr_fun h5 v
  rwa [e.symm_apply_apply] at h6
