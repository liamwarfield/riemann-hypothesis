module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlternatingDifferenceTermWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoBadWindowDivRho
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatProdEqEtaResultantMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatProdEqEtaResultantMul
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.SgnProd

theorem val_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add]

theorem eta_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta
  rw [val_mul K hx hy, zpow_add₀ (by norm_num)]

theorem eta_of_sq_one (K : UQ) {ε : K.E} (h : ε * ε = 1) (a : K.E) : K.eta (ε * a) = K.eta a := by
  have hε : ε ≠ 0 := by rintro rfl; simp at h
  have hv : val K.O ε = 0 := by
    have h1 := val_mul K hε hε
    rw [h] at h1
    have h0 : val K.O (1 : K.E) = 0 := by simp [val]
    omega
  unfold UQ.eta
  by_cases ha : a = 0
  · simp [ha]
  rw [val_mul K hε ha, hv, zero_add]

theorem exists_basis_lat (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) :
    ∃ e : Module.Basis (Fin (Module.finrank K.E V)) K.E V, Submodule.span K.O (Set.range e) = L := by
  have : Submodule.IsLattice K.E L := Submodule.IsLattice.of_fg K.E hfg
  have : Submodule.IsFullLattice K.E L := ⟨hsp⟩
  have : Module.Finite K.O L := Submodule.IsLattice.finite K.E L
  have : Module.Free K.O L := Submodule.IsLattice.free K.E L
  let b := Module.finBasisOfFinrankEq K.O L (Submodule.IsFullLattice.finrank_eq K.E L)
  refine ⟨b.extendOfIsFullLattice K.E, ?_⟩
  have : Set.range (b.extendOfIsFullLattice K.E) = L.subtype '' Set.range b := by
    ext x; simp
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_smul_mem (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [Module.Finite K.E V] (L : Submodule K.O V) (hfg : L.FG) (hsp : Submodule.span K.E (L : Set V) = ⊤) (y : V) :
    ∃ s : K.O, s ≠ 0 ∧ s • y ∈ L := by
  obtain ⟨e, he⟩ := exists_basis_lat K L hfg hsp
  obtain ⟨⟨s, hs⟩, hsc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors K.O) Finset.univ
    (fun i => e.repr y i)
  choose a ha using fun i => hsc i (Finset.mem_univ i)
  refine ⟨s, nonZeroDivisors.ne_zero hs, ?_⟩
  have : s • y = ∑ i, a i • e i := by
    conv_lhs => rw [← e.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K.E (a i), ha i, ← smul_assoc]
  rw [this, ← he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

theorem det_trace_ne_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hvm⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set q : K.E[X] := ∑ k : Fin (Module.finrank K.E B.A), C (c k) * X ^ (k : ℕ) with hq
  have hz : ∀ l, Algebra.trace K.E B.A (aeval B.g q * e l) = 0 := by
    intro l
    have := congrFun hvm l
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, hq, map_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have ha : aeval B.g (C (c k) * X ^ (k : ℕ)) = c k • B.g ^ (k : ℕ) := by
      rw [← smul_eq_C_mul, map_smul, aeval_X_pow]
    rw [ha, smul_mul_assoc, map_smul, smul_eq_mul]
  have hz' : aeval B.g q = 0 := by
    apply GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul B hsep
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_smul_comm, map_smul, hz l, smul_zero]
  have hdvd := GlobalTheory.UnitLemma.Centraliser.P_dvd_of_aeval_eq_zero B hsep q hz'
  have hdeg : q.degree < B.P.degree := by
    have hm : B.P.Monic := LinearMap.charpoly_monic _
    have hn : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [degree_eq_natDegree hm.ne_zero, hn]
    exact degree_sum_fin_lt c
  have hq0 : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  apply hc
  funext k
  have := congrArg (fun p : K.E[X] => p.coeff k) hq0
  simp only [hq, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single k (fun b _ hb => if_neg (fun h => hb (Fin.ext h.symm))) (by simp)] at this
  simpa using this

theorem trace_mat_toMatrix {E A : Type} [Field E] [CommRing A] [Algebra E A] {ι κ : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι E A) (x : κ → A) (f : ι → A) :
    (Matrix.of fun k l => Algebra.trace E A (x k * f l)) =
      (Matrix.of fun k i => Algebra.trace E A (x k * b i)) * b.toMatrix f := by
  ext k l
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.of_apply, Matrix.mul_apply, ← b.sum_toMatrix_smul_self f l, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, Matrix.of_apply, mul_comm]

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

open Module

theorem lattice_split (K : UQ) (V₁ V₂ : Type) [AddCommGroup V₁] [Module K.E V₁] [Module K.O V₁]
    [IsScalarTower K.O K.E V₁] [Module.Finite K.E V₁] [AddCommGroup V₂] [Module K.E V₂] [Module K.O V₂]
    [IsScalarTower K.O K.E V₂] [Module.Finite K.E V₂] (M : Submodule K.O (V₁ × V₂)) (hfg : M.FG)
    (hsp : Submodule.span K.E (M : Set (V₁ × V₂)) = ⊤) :
    ∃ (e₁ : Basis (Fin (finrank K.E V₁)) K.E V₁) (e₂ : Basis (Fin (finrank K.E V₂)) K.E V₂)
      (x : Fin (finrank K.E V₂) → V₁ × V₂),
      Submodule.span K.O (Set.range e₁) = M.comap (LinearMap.inl K.O V₁ V₂) ∧
      Submodule.span K.O (Set.range e₂) = M.map (LinearMap.snd K.O V₁ V₂) ∧
      (∀ j, (x j).2 = e₂ j) ∧
      Submodule.span K.O (Set.range (Fin.addCases (fun i => ((e₁ i, 0) : V₁ × V₂)) x)) = M := by
  set M₁ := M.comap (LinearMap.inl K.O V₁ V₂) with hM₁
  set M₂ := M.map (LinearMap.snd K.O V₁ V₂) with hM₂
  have hfg₁ : M₁.FG := by
    haveI : IsNoetherian K.O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (LinearMap.inl K.O V₁ V₂) LinearMap.inl_injective ?_
    exact Submodule.FG.of_le_of_isNoetherian (T := M) (Submodule.map_comap_le _ _)
  have hsp₁ : Submodule.span K.E (M₁ : Set V₁) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨s, hs0, hs⟩ := exists_smul_mem K M hfg hsp ((y, 0) : V₁ × V₂)
    have hsy : s • y ∈ M₁ := by
      show LinearMap.inl K.O V₁ V₂ (s • y) ∈ M
      simpa [LinearMap.inl_apply, Prod.smul_mk] using hs
    have hs' : algebraMap K.O K.E s ≠ 0 := by
      rwa [ne_eq, (IsFractionRing.injective K.O K.E).eq_iff' (map_zero _)]
    have : y = (algebraMap K.O K.E s)⁻¹ • (s • y) := by
      rw [← algebraMap_smul K.E s y, smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)
  have hfg₂ : M₂.FG := hfg.map _
  have hsp₂ : Submodule.span K.E (M₂ : Set V₂) = ⊤ := by
    have h1 : (M₂ : Set V₂) = (LinearMap.snd K.E V₁ V₂) '' (M : Set (V₁ × V₂)) := by
      rw [hM₂, Submodule.map_coe]; rfl
    rw [h1, Submodule.span_image, hsp, Submodule.map_top, LinearMap.range_eq_top.2 LinearMap.snd_surjective]
  obtain ⟨e₁, he₁⟩ := exists_basis_lat K M₁ hfg₁ hsp₁
  obtain ⟨e₂, he₂⟩ := exists_basis_lat K M₂ hfg₂ hsp₂
  have hlift : ∀ j, ∃ x ∈ M, x.2 = e₂ j := fun j => by
    have : e₂ j ∈ M₂ := he₂ ▸ Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 this
    exact ⟨x, hx, hxe⟩
  choose x hxM hx2 using hlift
  refine ⟨e₁, e₂, x, he₁, he₂, hx2, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l using Fin.addCases with
    | left i =>
      simp only [Fin.addCases_left, SetLike.mem_coe]
      have : e₁ i ∈ M₁ := he₁ ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this
    | right j => simp only [Fin.addCases_right, SetLike.mem_coe]; exact hxM j
  · intro y hy
    have hy2 : y.2 ∈ M₂ := Submodule.mem_map_of_mem hy
    rw [← he₂, Submodule.mem_span_range_iff_exists_fun] at hy2
    obtain ⟨c, hc⟩ := hy2
    set z := y - ∑ j, c j • x j with hz
    have hzM : z ∈ M := M.sub_mem hy (M.sum_mem fun j _ => M.smul_mem _ (hxM j))
    have hz2 : z.2 = 0 := by
      simp only [hz, Prod.snd_sub, Prod.snd_sum, Prod.smul_snd, hx2, hc, sub_self]
    have hz1 : z.1 ∈ M₁ := by
      show LinearMap.inl K.O V₁ V₂ z.1 ∈ M
      have : LinearMap.inl K.O V₁ V₂ z.1 = z := Prod.ext rfl hz2.symm
      rw [this]; exact hzM
    rw [← he₁, Submodule.mem_span_range_iff_exists_fun] at hz1
    obtain ⟨d, hd⟩ := hz1
    have hyz : y = ∑ i, d i • ((e₁ i, 0) : V₁ × V₂) + ∑ j, c j • x j := by
      have : ∑ i, d i • ((e₁ i, 0) : V₁ × V₂) = z := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, hd]
        · simp [Prod.snd_sum, hz2]
      rw [this, hz, sub_add_cancel]
    rw [hyz]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Fin.castAdd _ i, Fin.addCases_left _⟩
    · exact Submodule.subset_span ⟨Fin.natAdd _ j, Fin.addCases_right _⟩

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

open Module

theorem det_trace_lift {E A₁ A₂ : Type} [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    {a b : ℕ} (g : A₁ × A₂) (e₁ : Basis (Fin a) E A₁) (e₂ : Basis (Fin b) E A₂) (x : Fin b → A₁ × A₂)
    (hx : ∀ j, (x j).2 = e₂ j) :
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) x l)).det =
    (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
      (g ^ (k : ℕ) * Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) (fun j => ((0, e₂ j) : A₁ × A₂)) l)).det := by
  classical
  set f : Fin (a + b) → A₁ × A₂ := Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) x with hf
  let b₀ := (e₁.prod e₂).reindex finSumFinEquiv
  have hb₀ : ∀ l, b₀ l = Fin.addCases (fun i => ((e₁ i, 0) : A₁ × A₂)) (fun j => ((0, e₂ j) : A₁ × A₂)) l := by
    intro l
    induction l using Fin.addCases with
    | left i => simp [b₀]
    | right j => simp [b₀]
  have h := trace_mat_toMatrix b₀ (fun k : Fin (a + b) => g ^ (k : ℕ)) f
  rw [h, Matrix.det_mul]
  simp only [hb₀]
  suffices hU : (b₀.toMatrix f).det = 1 by rw [hU, mul_one]
  have hcc : ∀ i' l', b₀.toMatrix f (Fin.castAdd b i') (Fin.castAdd b l') = if l' = i' then 1 else 0 := by
    intro i' l'
    simp [Basis.toMatrix_apply, b₀, hf, Finsupp.single_apply]
  have hnc : ∀ j' l', b₀.toMatrix f (Fin.natAdd a j') (Fin.castAdd b l') = 0 := by
    intro j' l'
    simp [Basis.toMatrix_apply, b₀, hf]
  have hnn : ∀ j' j, b₀.toMatrix f (Fin.natAdd a j') (Fin.natAdd a j) = if j = j' then 1 else 0 := by
    intro j' j
    simp [Basis.toMatrix_apply, b₀, hf, hx, Finsupp.single_apply]
  have htri : (b₀.toMatrix f).BlockTriangular id := by
    intro i l hli
    simp only [id] at hli
    induction i using Fin.addCases with
    | left i' =>
      induction l using Fin.addCases with
      | left l' =>
        rw [hcc, if_neg]
        rintro rfl
        exact lt_irrefl _ hli
      | right j =>
        exfalso
        rw [Fin.lt_def, Fin.coe_natAdd, Fin.val_castAdd] at hli
        have := i'.2
        omega
    | right j' =>
      induction l using Fin.addCases with
      | left l' => exact hnc j' l'
      | right j =>
        rw [hnn, if_neg]
        rintro rfl
        exact lt_irrefl _ hli
  rw [Matrix.det_of_upperTriangular htri, Fin.prod_univ_add]
  simp [hcc, hnn]

end GlobalTheory.UnitLemma.SgnProd

namespace GlobalTheory.UnitLemma.SgnProd

open Module

theorem sgnLat_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K), (B₁.P * B₂.P).Separable → ∀ M ∈ (B₁.prod B₂).Lin,
    (B₁.prod B₂).sgnLat M = K.eta (resultant B₁.P B₂.P) *
      B₁.sgnLat (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * B₂.sgnLat (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  intro K B₁ B₂ hsep M hM
  obtain ⟨hfg, hsp⟩ := hM.1
  obtain ⟨e₁, e₂, x, he₁, he₂, hx, hspan⟩ := lattice_split K B₁.A B₂.A M hfg hsp
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) := by
      exact LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  let f : Fin (finrank K.E B₁.A + finrank K.E B₂.A) → B₁.A × B₂.A :=
    Fin.addCases (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) x
  have hcard : Fintype.card (Fin (finrank K.E B₁.A + finrank K.E B₂.A)) = finrank K.E (B₁.A × B₂.A) := by
    simp [Module.finrank_prod]
  have htop : ⊤ ≤ Submodule.span K.E (Set.range f) := by
    rw [← Submodule.span_span_of_tower K.O, hspan]
    exact hsp.ge
  let bf : Basis (Fin (finrank K.E B₁.A + finrank K.E B₂.A)) K.E (B₁.A × B₂.A) :=
    basisOfTopLeSpanOfCardEqFinrank f htop hcard
  have hbf : ⇑bf = f := coe_basisOfTopLeSpanOfCardEqFinrank f htop hcard
  have hN : finrank K.E B₁.A + finrank K.E B₂.A = finrank K.E (B₁.prod B₂).A := by
    rw [← Fintype.card_fin (finrank K.E B₁.A + finrank K.E B₂.A)]
    exact hcard
  let bF : Basis (Fin (finrank K.E (B₁.prod B₂).A)) K.E (B₁.prod B₂).A := bf.reindex (finCongr hN)
  have hrange : Set.range ⇑bF = Set.range f := by
    exact (Basis.range_reindex bf (finCongr hN)).trans (by rw [hbf])
  have hspanF : Submodule.span K.O (Set.range ⇑bF) = M := by
    rw [hrange]
    exact hspan
  have key := SgnBasis.sgnLat_span_basis K (B₁.prod B₂) bF
  rw [hspanF] at key
  rw [key, ← he₁, ← he₂, SgnBasis.sgnLat_span_basis K B₁ e₁, SgnBasis.sgnLat_span_basis K B₂ e₂]
  have hdet : (Matrix.of fun k l : Fin (finrank K.E (B₁.prod B₂).A) =>
      Algebra.trace K.E (B₁.prod B₂).A ((B₁.prod B₂).g ^ (k : ℕ) * bF l)).det =
      (Matrix.of fun k l : Fin (finrank K.E B₁.A + finrank K.E B₂.A) =>
        Algebra.trace K.E (B₁.A × B₂.A) ((B₁.g, B₂.g) ^ (k : ℕ) * f l)).det := by
    rw [← Matrix.det_submatrix_equiv_self (finCongr hN).symm]
    congr 1
    ext k l
    have hbF : bF l = f ((finCongr hN).symm l) := by
      rw [← hbf]
      exact Basis.reindex_apply bf (finCongr hN) l
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    erw [hbF]
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast]
    rfl
  obtain ⟨ε, hε, hL7⟩ := GlobalTheory.det_trace_pow_prod K.E B₁.A B₂.A B₁.g B₂.g _ _ e₁ e₂ hsep
  have hchain : (Matrix.of fun k l : Fin (finrank K.E (B₁.prod B₂).A) =>
      Algebra.trace K.E (B₁.prod B₂).A ((B₁.prod B₂).g ^ (k : ℕ) * bF l)).det =
      ε * resultant B₁.P B₂.P * (Matrix.of fun k l : Fin (finrank K.E B₁.A) =>
        Algebra.trace K.E B₁.A (B₁.g ^ (k : ℕ) * e₁ l)).det * (Matrix.of fun k l : Fin (finrank K.E B₂.A) =>
        Algebra.trace K.E B₂.A (B₂.g ^ (k : ℕ) * e₂ l)).det :=
    hdet.trans ((det_trace_lift (B₁.g, B₂.g) e₁ e₂ x hx).trans hL7)
  have hne := det_trace_ne_zero (B₁.prod B₂) (by rw [hP]; exact hsep) bF
  rw [hchain] at hne ⊢
  simp only [mul_ne_zero_iff] at hne
  obtain ⟨⟨⟨-, hR⟩, h₁⟩, h₂⟩ := hne
  rw [mul_assoc, mul_assoc, eta_of_sq_one K hε, eta_mul K hR (mul_ne_zero h₁ h₂), eta_mul K h₁ h₂, mul_assoc]

end GlobalTheory.UnitLemma.SgnProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatProdEqEtaResultantMulStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sgnLat_prod_eq_eta_resultant_mul : ∀ (K : UQ) (B₁ B₂ : InvAlg K), (B₁.P * B₂.P).Separable → ∀ M ∈ (B₁.prod B₂).Lin, (B₁.prod B₂).sgnLat M = K.eta (resultant B₁.P B₂.P) * B₁.sgnLat (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * B₂.sgnLat (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | exact GlobalTheory.UnitLemma.SgnProd.sgnLat_prod | (intros; apply GlobalTheory.UnitLemma.SgnProd.sgnLat_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductLatticePositionsAndTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductLatticePositionsAndTerms
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

section Prod

variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

theorem aeval_prod_fst (x : A₁ × A₂) (f : R[X]) : (aeval x f).1 = aeval x.1 f :=
  (aeval_algHom_apply (AlgHom.fst R A₁ A₂) x f).symm

theorem aeval_prod_snd (x : A₁ × A₂) (f : R[X]) : (aeval x f).2 = aeval x.2 f :=
  (aeval_algHom_apply (AlgHom.snd R A₁ A₂) x f).symm

theorem isIntegral_pair_one {r : A₁} (hr : IsIntegral R r) : IsIntegral R ((r, 1) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst, hfr, zero_mul]; rfl
  · rw [Prod.snd_mul, aeval_prod_snd (f := X - C 1)]; simp

theorem isIntegral_one_pair {r : A₂} (hr : IsIntegral R r) : IsIntegral R ((1, r) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst (f := X - C 1)]; simp
  · rw [Prod.snd_mul, aeval_prod_snd, hfr, zero_mul]; rfl

theorem isIntegral_fst {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.1 := hx.map (AlgHom.fst R A₁ A₂)

theorem isIntegral_snd {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.2 := hx.map (AlgHom.snd R A₁ A₂)

end Prod

theorem dlt_map {ι κ A : Type} [CommMonoid A] (π : κ → A) (e : ι ↪ κ) (I : Finset ι) (f : A → ℚ) (y : A) :
    dlt π (I.map e) f y = dlt (π ∘ e) I f y := by
  unfold dlt
  symm
  refine Finset.sum_bij (fun J _ => J.map e) (fun J hJ => ?_) (fun J₁ _ J₂ _ h => Finset.map_injective e h)
    (fun J hJ => ?_) (fun J _ => ?_)
  · exact Finset.mem_powerset.2 (Finset.map_subset_map.2 (Finset.mem_powerset.1 hJ))
  · obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 (Finset.mem_powerset.1 hJ)
    exact ⟨u, Finset.mem_powerset.2 hu, rfl⟩
  · simp [Finset.prod_map, Finset.card_map]

theorem dlt_empty {ι A : Type} [CommMonoid A] (π : ι → A) (f : A → ℚ) (y : A) : dlt π ∅ f y = f y := by
  simp [dlt]

theorem pos_term_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  intro K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a N M p u₁ u₂
  refine ⟨fun h => ⟨fun i => ⟨fun r hr => ?_, fun m hm => ?_⟩, fun j => ⟨fun r hr => ?_, fun m hm => ?_⟩⟩, ?_⟩
  · have := (h (Sum.inl i)).1 (r, 1) (isIntegral_pair_one hr)
    have key : (LinearMap.inl K.O B₁.A B₂.A) (al K a ^ ((p ∘ Sum.inl) i + N) • (e₁ i * r)) =
        al K a ^ (p (Sum.inl i) + N) • (((e₁ i, 0) : B₁.A × B₂.A) * (r, 1)) :=
      Prod.ext rfl (by show (0 : B₂.A) = al K a ^ (p (Sum.inl i) + N) • ((0 : B₂.A) * 1); simp)
    rw [Submodule.mem_comap, key]
    exact this
  · exact isIntegral_fst ((h (Sum.inl i)).2 (m, 0) hm)
  · have := (h (Sum.inr j)).1 (1, r) (isIntegral_one_pair hr)
    exact ⟨_, this, rfl⟩
  · obtain ⟨m', hm', rfl⟩ := hm
    exact isIntegral_snd ((h (Sum.inr j)).2 m' hm')
  · have hT : ∀ (z : B₁.A × B₂.A), z ∈ M → ∀ t : B₂.A,
        Algebra.trace K.E (B₁.A × B₂.A) (((0 : B₁.A), t) * z) = Algebra.trace K.E B₂.A (t * z.2) := by
      intro z _ t
      rw [Algebra.trace_prod_apply]
      simp
    have hD : ∀ t : B₂.A, InDual (B₁.prod B₂) ((0 : B₁.A), t) M ↔ InDual B₂ t (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
      intro t
      constructor
      · rintro h z ⟨z', hz', rfl⟩
        show Algebra.trace K.E B₂.A (t * z'.2) ∈ _
        rw [← hT z' hz' t]
        exact h z' hz'
      · intro h z hz
        convert h z.2 ⟨z, hz, rfl⟩ using 1
        exact hT z hz t
    have hE1 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) = ((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₁, ((e₁ x, 0) : B₁.A × B₂.A)) = (∑ i ∈ S₁, e₁ i, 0)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have hE2 : eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A)))
        (S₂.map Function.Embedding.inr) = ((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) := by
      unfold eS
      rw [Finset.sum_map]
      show (∑ x ∈ S₂, ((0, e₂ x) : B₁.A × B₂.A)) = (0, ∑ i ∈ S₂, e₂ i)
      ext <;> simp [Prod.fst_sum, Prod.snd_sum]
    have keyM : ∀ y : B₁.A, indM (B₁.prod B₂) M (LinearMap.inl K.O B₁.A B₂.A y) =
        indM B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) y := fun y => by
      unfold indM
      classical
      exact if_congr Iff.rfl rfl rfl
    have keyD : ∀ t : B₂.A, indD (B₁.prod B₂) M (((0 : B₁.A), t) : B₁.A × B₂.A) =
        indD B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) t := fun t => by
      unfold indD
      classical
      exact if_congr (hD t) rfl rfl
    unfold term
    rw [dlt_map, dlt_map, dlt_empty, dlt_empty, hE1, hE2]
    have h0 : ∀ (B : InvAlg K) (e : ι₁ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    have h0' : ∀ (B : InvAlg K) (e : ι₂ → B.A), eS B e ∅ = 0 := fun _ _ => by simp [eS]
    rw [h0, h0', zero_mul, zero_mul]
    have hm0 : indM B₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) 0 = 1 := by simp [indM]
    have hd0 : indD B₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) 0 = 1 := by
      simp [indD, InDual]
    rw [hm0, hd0, mul_one, one_mul]
    congr 1
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      unfold indM
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inl) j) *
          (((eS B₁ e₁ S₁, 0) : B₁.A × B₂.A) * (u₁, u₂)) =
          LinearMap.inl K.O B₁.A B₂.A ((∏ j ∈ J, π₁ j) * (eS B₁ e₁ S₁ * u₁)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indM (B₁.prod B₂) M) this).trans (keyM _)
    · unfold dlt
      refine Finset.sum_congr rfl fun J _ => ?_
      congr 1
      have : (∏ j ∈ J, (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)) ∘ Sum.inr) j) *
          (((0, eS B₂ e₂ S₂) : B₁.A × B₂.A) * 1) = ((0 : B₁.A), (∏ j ∈ J, π₂ j) * (eS B₂ e₂ S₂ * 1)) := by
        ext <;> simp [Prod.fst_prod, Prod.snd_prod]
      exact (congrArg (indD (B₁.prod B₂) M) this).trans (keyD _)

end GlobalTheory.UnitLemma.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductLatticePositionsAndTermsStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTerm_prod_eq_mul_components : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O) (N : ℕ) (M : Submodule K.O (B₁.A × B₂.A)) (p : ι₁ ⊕ ι₂ → ℤ) (u₁ : B₁.A) (u₂ : B₂.A), (Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p → Pos B₁ a e₁ N (M.comap (LinearMap.inl K.O B₁.A B₂.A)) (p ∘ Sum.inl) ∧ Pos B₂ a e₂ N (M.map (LinearMap.snd K.O B₁.A B₂.A)) (p ∘ Sum.inr)) ∧ term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) * (show (B₁.prod B₂).A from (u₁, u₂))) (eS (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₂.map Function.Embedding.inr) * 1) M = term B₁ π₁ S₁ ∅ (eS B₁ e₁ S₁ * u₁) (eS B₁ e₁ ∅ * 1) (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * term B₂ π₂ ∅ S₂ (eS B₂ e₂ ∅ * u₂) (eS B₂ e₂ S₂ * 1) (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
  first | exact @GlobalTheory.UnitLemma.Desc.pos_term_prod | exact GlobalTheory.UnitLemma.Desc.pos_term_prod | (intros; apply GlobalTheory.UnitLemma.Desc.pos_term_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactors
noncomputable section

namespace GlobalTheory.UnitLemma.Desc.ProdSum

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

theorem abs_sgnLat {K : UQ} (B : InvAlg K) (M : Submodule K.O B.A) : |B.sgnLat M| = 1 := by
  unfold InvAlg.sgnLat
  exact abs_eta _

theorem isUnit_alg {K : UQ} (B : InvAlg K) {a : K.O} (ha : a ≠ 0) : IsUnit (algebraMap K.O B.A a) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
  refine IsUnit.map _ (IsUnit.mk0 _ ?_)
  intro h
  exact ha ((IsFractionRing.injective K.O K.E) (by rw [h, map_zero]))

variable {ι₁ ι₂ : Type} (S₁ : Finset ι₁) (S₂ : Finset ι₂) (L k : ℕ) (p : ι₁ ⊕ ι₂ → ℤ)

theorem win_inl (h : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p) :
    Win S₁ ∅ L k (p ∘ Sum.inl) := by
  intro i
  obtain ⟨h1, h2, h3, _⟩ := h (Sum.inl i)
  exact ⟨h1, h2, fun hi => h3 (by simpa using hi), fun hi => absurd hi (Finset.notMem_empty _)⟩

theorem win_inr (h : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p) :
    Win ∅ S₂ L k (p ∘ Sum.inr) := by
  intro j
  obtain ⟨h1, h2, _, h4⟩ := h (Sum.inr j)
  exact ⟨h1, h2, fun hj => absurd hj (Finset.notMem_empty _), fun hj => h4 (by simpa using hj)⟩

theorem win_of (h₁ : Win S₁ ∅ L k (p ∘ Sum.inl)) (h₂ : Win ∅ S₂ L k (p ∘ Sum.inr)) :
    Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p := by
  rintro (i | j)
  · obtain ⟨a1, a2, a3, _⟩ := h₁ i
    exact ⟨a1, a2, fun hi => a3 (by simpa using hi), fun hi => by simp at hi⟩
  · obtain ⟨a1, a2, _, a4⟩ := h₂ j
    exact ⟨a1, a2, fun hj => by simp at hj, fun hj => a4 (by simpa using hj)⟩

theorem mid_inl (h : Mid (S₁.disjSum S₂) L k p) : Mid S₁ L k (p ∘ Sum.inl) :=
  fun i hi => h (Sum.inl i) (by simpa using hi)

theorem mid_inr (h : Mid (S₁.disjSum S₂) L k p) : Mid S₂ L k (p ∘ Sum.inr) :=
  fun j hj => h (Sum.inr j) (by simpa using hj)

end GlobalTheory.UnitLemma.Desc.ProdSum

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc GlobalTheory.UnitLemma.Desc.ProdSum Polynomial Filter Topology

theorem GlobalTheory.UnitLemma.Desc.hh_prod_tendsto : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  intro K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ a hL₁ hL₂ hsep ha hF₁ hF₂
  classical
  have hP : (B₁.prod B₂).P = B₁.P * B₂.P := by
    have h1 : LinearMap.mulLeft K.E (B₁.prod B₂).g =
        (LinearMap.mulLeft K.E B₁.g).prodMap (LinearMap.mulLeft K.E B₂.g) :=
      LinearMap.ext fun _ => rfl
    have h2 := LinearMap.charpoly_prodMap (LinearMap.mulLeft K.E B₁.g) (LinearMap.mulLeft K.E B₂.g)
    rw [← h1] at h2
    exact h2
  have hsB : (B₁.prod B₂).P.Separable := hP ▸ hsep
  have hs₁ : B₁.P.Separable := hL₁.2
  have hs₂ : B₂.P.Separable := hL₂.2
  have hF := GlobalTheory.T.isUniformizerIdempotentFrame_prod K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ hF₁ hF₂
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF
  have hIS : S₁.map Function.Embedding.inl ⊆ S₁.disjSum S₂ := by intro x; cases x <;> simp
  have hI'S : S₂.map Function.Embedding.inr ⊆ S₁.disjSum S₂ := by intro x; cases x <;> simp
  have hcov : ∀ i ∈ S₁.disjSum S₂, i ∈ S₁.map Function.Embedding.inl ∨ i ∈ S₂.map Function.Embedding.inr := by
    rintro (i | j) h <;> simp_all
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.alternatingDifference_term_window K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF _ _ hIS hI'S hcov N 1 1
    isUnit_one isUnit_one
  obtain ⟨L₁, hL₁'⟩ := GlobalTheory.T.alternatingDifference_term_window K B₁ ι₁ e₁ π₁ S₁ a hs₁ ha hF₁ S₁ ∅ subset_rfl (Finset.empty_subset _)
    (fun i hi => Or.inl hi) N 1 1 isUnit_one isUnit_one
  obtain ⟨L₂, hL₂'⟩ := GlobalTheory.T.alternatingDifference_term_window K B₂ ι₂ e₂ π₂ S₂ a hs₂ ha hF₂ ∅ S₂ (Finset.empty_subset _) subset_rfl
    (fun i hi => Or.inr hi) N 1 1 isUnit_one isUnit_one
  obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : ℕ → Submodule K.O B₁.A → ℚ, ∀ k M,
      φ₁ k M = B₁.sgnLat M * term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : ℕ → Submodule K.O B₂.A → ℚ, ∀ k M,
      φ₂ k M = B₂.sgnLat M * term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Submodule K.O (B₁.prod B₂).A → ℚ, ∀ k M,
      g k M = (B₁.prod B₂).sgnLat M * term (B₁.prod B₂)
        (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
        (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Submodule K.O (B₁.prod B₂).A → ℚ, ∀ k M,
      f k M = g k M - K.eta (resultant B₁.P B₂.P) *
        (φ₁ k (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ k (M.map (LinearMap.snd K.O B₁.A B₂.A))) :=
    ⟨_, fun _ _ => rfl⟩
  have hfinB : ∀ k, {M ∈ (B₁.prod B₂).Lin | g k M ≠ 0}.Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ hsB hF _ _ hIS hI'S
      (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 ((isUnit_alg (B₁.prod B₂) ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hg, h, mul_zero])⟩)
  have hfin₁ : ∀ k, {M ∈ B₁.Lin | φ₁ k M ≠ 0}.Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B₁ ι₁ e₁ π₁ S₁ hs₁ hF₁ S₁ ∅ subset_rfl (Finset.empty_subset _) _ _
      ((isUnit_alg B₁ ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hφ₁, h, mul_zero])⟩)
  have hfin₂ : ∀ k, {M ∈ B₂.Lin | φ₂ k M ≠ 0}.Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B₂ ι₂ e₂ π₂ S₂ hs₂ hF₂ ∅ S₂ (Finset.empty_subset _) subset_rfl _ _
      ((isUnit_alg B₂ ha.1).pow (2 * k)) isUnit_one).subset
      (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by rw [hφ₂, h, mul_zero])⟩)
  have hsum : ∀ k, ∑ᶠ M ∈ (B₁.prod B₂).Lin, f k M =
      HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
        (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
        (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 -
      (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) *
        (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) := by
    intro k
    obtain ⟨hfinP, hfib⟩ := GlobalTheory.T.sum_stableLattices_product_eq_q_pow_mul K B₁ B₂ hL₁.1 hL₂.1 hsep (φ₁ k) (φ₂ k) (hfin₁ k) (hfin₂ k)
    have e1 : ∀ M, f k M = g k M + (-K.eta (resultant B₁.P B₂.P)) *
        (φ₁ k (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ k (M.map (LinearMap.snd K.O B₁.A B₂.A))) := by
      intro M; rw [hf]; ring
    rw [finsum_mem_congr rfl (fun M _ => e1 M)]
    rw [finsum_mem_add_distrib' ?_ ?_, ← mul_finsum_mem, hfib]
    · have h0 : ∑ᶠ M ∈ (B₁.prod B₂).Lin, g k M = HH (B₁.prod B₂)
          (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hg k M
      have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ k M = HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hφ₁ k M
      have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ k M = HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 := by
        unfold HH; exact finsum_mem_congr rfl fun M _ => hφ₂ k M
      rw [h0, h1, h2]
      unfold UQ.eta
      rw [neg_eq_neg_one_mul (K.q : ℚ), mul_zpow]
      ring
    · exact (hfinB k).subset (fun M ⟨hM, hne⟩ => ⟨hM, hne⟩)
    · exact hfinP.subset (fun M ⟨hM, hne⟩ => ⟨hM, fun h => hne (by simp only [h, mul_zero])⟩)
  have hbound : ∀ k M, |f k M| ≤ 2 ^ (S₁.map (@Function.Embedding.inl ι₁ ι₂)).card * 2 ^ (S₂.map (@Function.Embedding.inr ι₁ ι₂)).card +
      2 ^ S₁.card * 2 ^ (∅ : Finset ι₁).card * (2 ^ (∅ : Finset ι₂).card * 2 ^ S₂.card) := by
    intro k M
    rw [hf, hg, hφ₁, hφ₂]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_sgnLat, one_mul]; exact abs_term _ _ _ _ _ _ _
    · rw [abs_mul, abs_eta, one_mul, abs_mul, abs_mul, abs_mul, abs_sgnLat, abs_sgnLat, one_mul, one_mul]
      exact mul_le_mul (abs_term _ _ _ _ _ _ _) (abs_term _ _ _ _ _ _ _) (abs_nonneg _) (by positivity)
  have hsupp : ∀ k, max L₀ (max L₁ L₂) ≤ k → ∀ M ∈ (B₁.prod B₂).Lin, ∀ p,
      Pos (B₁.prod B₂) a (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) N M p →
      f k M ≠ 0 → Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (max L₀ (max L₁ L₂)) k p ∧
        ¬ Mid (S₁.disjSum S₂) (max L₀ (max L₁ L₂)) k p := by
    intro k hk M hM p hp hne
    set L := max L₀ (max L₁ L₂) with hL
    have tp := GlobalTheory.T.latticeTerm_prod_eq_mul_components K B₁ B₂ ι₁ ι₂ e₁ π₁ e₂ π₂ S₁ S₂ a N M p (algebraMap K.O B₁.A a ^ (2 * k))
      (algebraMap K.O B₂.A a ^ (2 * k))
    obtain ⟨hp₁, hp₂⟩ := tp.1 hp
    have a0 := hL₀ L (le_max_left _ _) k hk M p hp
    have a1 := hL₁' L (le_trans (le_max_left _ _) (le_max_right _ _)) k hk _ _ hp₁
    have a2 := hL₂' L (le_trans (le_max_right _ _) (le_max_right _ _)) k hk _ _ hp₂
    rw [one_mul] at a0 a1 a2
    have hwin : Win (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) L k p := by
      by_cases h0 : term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M = 0
      · have hne' := hne
        rw [hf, hg, hφ₁, hφ₂, h0] at hne'
        have t1 : term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 (M.comap (LinearMap.inl K.O B₁.A B₂.A)) ≠ 0 :=
          fun h => hne' (by rw [h]; ring)
        have t2 : term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0 :=
          fun h => hne' (by rw [h]; ring)
        exact win_of S₁ S₂ L k p (a1.1 t1) (a2.1 t2)
      · exact a0.1 h0
    refine ⟨hwin, fun hmid => hne ?_⟩
    have e0 := a0.2 hwin hmid
    have e1 := a1.2 (win_inl S₁ S₂ L k p hwin) (mid_inl S₁ S₂ L k p hmid)
    have e2 := a2.2 (win_inr S₁ S₂ L k p hwin) (mid_inr S₁ S₂ L k p hmid)
    have hA : (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) =
        ((algebraMap K.O B₁.A a ^ (2 * k), algebraMap K.O B₂.A a ^ (2 * k)) : B₁.A × B₂.A) :=
      Prod.ext (by simp) (by simp)
    have key : term (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A)))
          (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr)
          (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 M =
        term B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 (M.comap (LinearMap.inl K.O B₁.A B₂.A)) *
        term B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1 (M.map (LinearMap.snd K.O B₁.A B₂.A)) := by
      rw [e1, e2]
      refine Eq.trans e0 (Eq.trans ?_ tp.2)
      congr 2
    rw [hf, hg, hφ₁, hφ₂, key, GlobalTheory.T.sgnLat_prod_eq_eta_resultant_mul K B₁ B₂ hsep M hM]
    ring
  have hc := GlobalTheory.T.tendsto_finsum_div_rho_pow_zero K (B₁.prod B₂) (ι₁ ⊕ ι₂) _ _ _ a hsB ha hF (S₁.map Function.Embedding.inl)
    (S₂.map Function.Embedding.inr) hcov N (max L₀ (max L₁ L₂)) _ f hN hbound hsupp
  refine hc.congr (fun k => ?_)
  rw [hsum k]
  have hA' : (algebraMap K.O (B₁.A × B₂.A) a ^ k) =
      ((algebraMap K.O B₁.A a ^ k, algebraMap K.O B₂.A a ^ k) : B₁.A × B₂.A) :=
    Prod.ext (by simp) (by simp)
  have hr : (B₁.prod B₂).rho (algebraMap K.O (B₁.prod B₂).A a ^ k) =
      B₁.rho (algebraMap K.O B₁.A a ^ k) * B₂.rho (algebraMap K.O B₂.A a ^ k) := by
    rw [← GlobalTheory.T.rho_prod_finiteAlgebraWithInvolution K B₁ B₂]
    exact congrArg _ hA'
  rw [hr, Nat.cast_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoSignedLatticeSumProductSubFactorsStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_signedLatticeSum_product_sub_factors : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂) (a : K.O), B₁.LieReg → B₂.LieReg → (B₁.P * B₂.P).Separable → K.Small a → IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → Tendsto (fun k : ℕ => (((HH (B₁.prod B₂) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) (S₂.map Function.Embedding.inr) (algebraMap K.O (B₁.A × B₂.A) a ^ (2 * k)) 1 - (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (HH B₁ π₁ S₁ ∅ (algebraMap K.O B₁.A a ^ (2 * k)) 1 * HH B₂ π₂ ∅ S₂ (algebraMap K.O B₂.A a ^ (2 * k)) 1) : ℚ) : ℝ) / ((B₁.rho (algebraMap K.O B₁.A a ^ k) : ℝ) * (B₂.rho (algebraMap K.O B₂.A a ^ k) : ℝ)))) atTop (𝓝 0) := by
  first | exact @GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | exact GlobalTheory.UnitLemma.Desc.hh_prod_tendsto | (intros; apply GlobalTheory.UnitLemma.Desc.hh_prod_tendsto <;> assumption)
end
