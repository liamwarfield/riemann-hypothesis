module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstIntegralCoordsLatticeSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_integral_coords_lattice_section : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ), IsPreconnected B → ContinuousOn lam B → ContinuousOn ζ B → (∀ b ∈ B, IsLatBasis (K b) (lam b)) → (∀ b ∈ B, ζ b ∈ K b) → b₀ ∈ B → ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | exact GlobalTheory.ShFam.Hor.LogCh.exists_const_coords | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_const_coords <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvex
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvex
set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh.Glob

variable {g r : ℕ}

def rip (w : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun v := ∑ k, (v k * (starRingEnd ℂ) (w k)).re
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_assoc]

theorem rip_apply (w v : Fin g → ℂ) : rip w v = ∑ k, (v k * (starRingEnd ℂ) (w k)).re := rfl

theorem rip_comm (w v : Fin g → ℂ) : rip w v = rip v w := by
  simp only [rip_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_re]
  ring

theorem eq_zero_of_rip_self {v : Fin g → ℂ} (h : rip v v = 0) : v = 0 := by
  have h' : ∑ k, Complex.normSq (v k) = 0 := by
    rw [← h, rip_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (v k))).1 h'
  funext k
  exact Complex.normSq_eq_zero.1 (this k (Finset.mem_univ k))

theorem continuous_rip : Continuous fun q : (Fin g → ℂ) × (Fin g → ℂ) => rip q.1 q.2 := by
  simp only [rip_apply]
  refine continuous_finsetSum _ fun k _ => Complex.continuous_re.comp ?_
  exact ((continuous_apply k).comp continuous_snd).mul
    (Complex.continuous_conj.comp ((continuous_apply k).comp continuous_fst))

def gram (l : Fin r → Fin g → ℂ) : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i a => rip (l a) (l i)

def pair (l y : Fin r → Fin g → ℂ) : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun j a => rip (l a) (y j)

theorem det_gram_ne_zero {l : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) : (gram l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv
  have hs : ∀ a, rip (l a) (∑ i, v i • l i) = 0 := by
    intro a
    have := congrFun hv0 a
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.vecMul, dotProduct, gram, map_sum] using this
  have hz : (∑ i, v i • l i) = 0 := by
    apply eq_zero_of_rip_self
    calc rip (∑ i, v i • l i) (∑ i, v i • l i) = ∑ a, rip (∑ i, v i • l i) (v a • l a) := map_sum _ _ _
      _ = ∑ a, v a * rip (l a) (∑ i, v i • l i) :=
        Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul, rip_comm]
      _ = 0 := by simp [hs]
  exact funext fun i => Fintype.linearIndependent_iff.1 hl v hz i

def coord (l y : Fin r → Fin g → ℂ) : Matrix (Fin r) (Fin r) ℝ := pair l y * (gram l)⁻¹

theorem coord_eq {l y : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) (c : Matrix (Fin r) (Fin r) ℝ)
    (hy : ∀ j, y j = ∑ i, c j i • l i) : coord l y = c := by
  have : pair l y = c * gram l := by
    ext j a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [pair, gram, Matrix.mul_apply, hy j, map_sum]
  rw [coord, this]
  exact Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.2 (det_gram_ne_zero hl))

theorem continuous_coord {T : Type*} [TopologicalSpace T] {l y : T → Fin r → Fin g → ℂ} (hl : Continuous l)
    (hy : Continuous y) (hi : ∀ t, LinearIndependent ℝ (l t)) : Continuous fun t => coord (l t) (y t) := by
  have hg : Continuous fun t => gram (l t) := continuous_matrix fun i a =>
    continuous_rip.comp (((continuous_apply a).comp hl).prodMk ((continuous_apply i).comp hl))
  have hp : Continuous fun t => pair (l t) (y t) := continuous_matrix fun j a =>
    continuous_rip.comp (((continuous_apply a).comp hl).prodMk ((continuous_apply j).comp hy))
  have hinv : Continuous fun t => (gram (l t))⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hg.matrix_det.inv₀ fun t => det_gram_ne_zero (hi t)).smul hg.matrix_adjugate
  exact hp.matrix_mul hinv

def act (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) : Fin r → Fin g → ℂ := fun j => ∑ i, m j i • l i

theorem act_real (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (j : Fin r) :
    act m l j = ∑ i, (m.map (Int.cast : ℤ → ℝ)) j i • l i := by
  simp only [act, Matrix.map_apply, Int.cast_smul_eq_zsmul]

theorem coord_act {l : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) (m : Matrix (Fin r) (Fin r) ℤ) :
    coord l (act m l) = m.map (Int.cast : ℤ → ℝ) :=
  coord_eq hl _ (act_real m l)

theorem act_injective {l : Fin r → Fin g → ℂ} (hl : LinearIndependent ℝ l) {m m' : Matrix (Fin r) (Fin r) ℤ}
    (h : act m l = act m' l) : m = m' := by
  have := (coord_act hl m).symm.trans ((congrArg (coord l) h).trans (coord_act hl m'))
  ext j i
  simpa using congrFun (congrFun this j) i

theorem act_one (l : Fin r → Fin g → ℂ) : act 1 l = l := by
  funext j
  simp [act, Matrix.one_apply]

theorem act_act (m n : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) : act m (act n l) = act (m * n) l := by
  funext j
  simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem sum_act_int (a : Fin r → ℤ) (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) :
    ∑ j, a j • act m l j = ∑ i, (Matrix.vecMul a m) i • l i := by
  simp only [act, Matrix.vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem sum_act_real (c : Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) :
    ∑ j, c j • act m l j = ∑ i, (Matrix.vecMul c (m.map (Int.cast : ℤ → ℝ))) i • l i := by
  simp only [act_real, Matrix.vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

def GLZ (r : ℕ) : Type := (Matrix (Fin r) (Fin r) ℤ)ˣ

instance : TopologicalSpace (GLZ r) := ⊥

instance : DiscreteTopology (GLZ r) := ⟨rfl⟩

def GLZ.mat (M : GLZ r) : Matrix (Fin r) (Fin r) ℤ := Units.val M

theorem GLZ.mat_injective : Function.Injective (GLZ.mat : GLZ r → _) := Units.val_injective

theorem exists_glz {S : Set (Fin g → ℂ)} {l l' : Fin r → Fin g → ℂ} (hl : IsLatBasis S l) (hl' : IsLatBasis S l') :
    ∃ M : GLZ r, l' = act M.mat l := by
  have mem : ∀ {q : Fin r → Fin g → ℂ}, IsLatBasis S q → ∀ j, q j ∈ S := fun {q} hq j =>
    (hq.2 _).2 ⟨Pi.single j 1, by simp [Pi.single_apply, ite_smul]⟩
  choose m hm using fun j => (hl.2 _).1 (mem hl' j)
  choose n hn using fun j => (hl'.2 _).1 (mem hl j)
  have e1 : l' = act (Matrix.of m) l := funext hm
  have e2 : l = act (Matrix.of n) l' := funext hn
  have h1 : Matrix.of m * Matrix.of n = 1 := by
    refine act_injective hl'.1 ?_
    rw [← act_act, ← e2, ← e1, act_one]
  have h2 : Matrix.of n * Matrix.of m = 1 := by
    refine act_injective hl.1 ?_
    rw [← act_act, ← e1, ← e2, act_one]
  exact ⟨⟨Matrix.of m, Matrix.of n, h1, h2⟩, e1⟩

theorem isLatBasis_act {S : Set (Fin g → ℂ)} {l : Fin r → Fin g → ℂ} (hl : IsLatBasis S l) (M : GLZ r) :
    IsLatBasis S (act M.mat l) := by
  obtain ⟨m, n, hM, h1, h2⟩ : ∃ m n : Matrix (Fin r) (Fin r) ℤ, M.mat = m ∧ m * n = 1 ∧ n * m = 1 :=
    ⟨M.mat, Units.inv M, rfl, Units.mul_inv M, Units.inv_mul M⟩
  rw [hM]
  have hr : m.map (Int.cast : ℤ → ℝ) * n.map (Int.cast : ℤ → ℝ) = 1 := by
    have h : (m * n).map (Int.castRingHom ℝ) = 1 := by rw [h1]; simp
    rw [Matrix.map_mul] at h
    exact h
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc j => ?_, fun w => ?_⟩
  · rw [sum_act_real] at hc
    have h0 := Fintype.linearIndependent_iff.1 hl.1 _ hc
    have h0' : Matrix.vecMul c (m.map (Int.cast : ℤ → ℝ)) = 0 := funext h0
    have : c = Matrix.vecMul (Matrix.vecMul c (m.map (Int.cast : ℤ → ℝ))) (n.map (Int.cast : ℤ → ℝ)) := by
      rw [Matrix.vecMul_vecMul, hr, Matrix.vecMul_one]
    rw [this, h0']
    simp
  · constructor
    · intro hw
      obtain ⟨b, rfl⟩ := (hl.2 _).1 hw
      refine ⟨Matrix.vecMul b n, ?_⟩
      rw [sum_act_int, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
    · rintro ⟨a, rfl⟩
      exact (hl.2 _).2 ⟨Matrix.vecMul a m, sum_act_int a m l⟩

theorem continuous_of_act {T : Type*} [TopologicalSpace T] {l y : T → Fin r → Fin g → ℂ} (hl : Continuous l)
    (hy : Continuous y) (hi : ∀ t, LinearIndependent ℝ (l t)) (M : T → GLZ r)
    (h : ∀ t, y t = act (M t).mat (l t)) : Continuous M := by
  have hc := continuous_coord hl hy hi
  have he : ∀ t, coord (l t) (y t) = (M t).mat.map (Int.cast : ℤ → ℝ) := fun t => by
    rw [h t, coord_act (hi t)]
  have hp : Continuous fun t => ((M t).mat : Fin r → Fin r → ℤ) := by
    refine continuous_pi fun j => continuous_pi fun i => ?_
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    have : Continuous fun t => coord (l t) (y t) j i :=
      hc.matrix_elem j i
    refine this.congr fun t => ?_
    rw [he t]
    rfl
  have hlc : IsLocallyConstant (fun t => ((M t).mat : Fin r → Fin r → ℤ)) :=
    (IsLocallyConstant.iff_continuous _).2 hp
  exact ((IsLocallyConstant.desc M GLZ.mat hlc GLZ.mat_injective)).continuous

theorem continuous_act (m : Matrix (Fin r) (Fin r) ℤ) : Continuous (act m : (Fin r → Fin g → ℂ) → _) :=
  continuous_pi fun j => continuous_finsetSum _ fun i _ => (continuous_apply i).const_smul (m j i)

variable {n : ℕ}

abbrev Frames (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (r : ℕ) : Type :=
  {p : ↥B × (Fin r → Fin g → ℂ) // IsLatBasis (K p.1) p.2}

def proj (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (r : ℕ) : Frames B K r → ↥B := fun e => e.1.1

theorem continuous_proj (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (r : ℕ) :
    Continuous (proj B K r) := continuous_fst.comp continuous_subtype_val

theorem local_data {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} (hB : IsOpen B)
    (hloc : ∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧
      ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) {b₀ : Fin n → ℂ} (hb : b₀ ∈ B) :
    ∃ (V : Set (Fin n → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsOpen V ∧ b₀ ∈ V ∧ V ⊆ B ∧
      AnalyticAt ℂ lam b₀ ∧ ContinuousOn lam V ∧ ∀ b ∈ V, IsLatBasis (K b) (lam b) := by
  obtain ⟨lam, han, hev⟩ := hloc b₀ hb
  have h := (han.eventually_analyticAt.and hev).and (hB.mem_nhds hb)
  obtain ⟨V, hVs, hV, hbV⟩ := eventually_nhds_iff.1 h
  exact ⟨V, lam, hV, hbV, fun x hx => (hVs x hx).2, han,
    fun x hx => (hVs x hx).1.1.continuousAt.continuousWithinAt, fun x hx => (hVs x hx).1.2⟩

theorem isCoveringMap_proj {B : Set (Fin n → ℂ)} {K : (Fin n → ℂ) → Set (Fin g → ℂ)} (hB : IsOpen B)
    (hloc : ∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧
      ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) : IsCoveringMap (proj B K r) := by
  intro x₀
  obtain ⟨V, lam, hV, hxV, hVB, -, hc, hbas⟩ := local_data hB hloc x₀.2
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := GLZ r)
  have hU : IsOpen (Subtype.val ⁻¹' V : Set ↥B) := hV.preimage continuous_subtype_val
  have hM : ∀ e : proj B K r ⁻¹' (Subtype.val ⁻¹' V : Set ↥B), ∃ M : GLZ r,
      e.1.1.2 = act M.mat (lam e.1.1.1.1) := fun e => exists_glz (hbas _ e.2) e.1.2
  choose M hM using hM
  have hcl : Continuous fun e : proj B K r ⁻¹' (Subtype.val ⁻¹' V : Set ↥B) => lam e.1.1.1.1 :=
    hc.comp_continuous (by fun_prop) fun e => e.2
  have hMc : Continuous M :=
    continuous_of_act hcl (by fun_prop) (fun e => (hbas _ e.2).1) M hM
  refine ⟨inferInstance, _, hxV, hU, hU.preimage (continuous_proj B K r), ?_⟩
  refine ⟨{ toFun := fun e => (⟨proj B K r e.1, e.2⟩, M e)
            invFun := fun q => ⟨⟨⟨q.1.1, act q.2.mat (lam q.1.1.1)⟩, isLatBasis_act (hbas _ q.1.2) q.2⟩, q.1.2⟩
            left_inv := fun e => ?_
            right_inv := fun q => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun e => rfl⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (hM e).symm
  · refine Prod.ext rfl ?_
    apply GLZ.mat_injective
    exact act_injective (hbas _ q.1.2).1 (hM _).symm
  · exact (Continuous.subtype_mk ((continuous_proj B K r).comp continuous_subtype_val) _).prodMk hMc
  · refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine (continuous_subtype_val.comp continuous_fst).prodMk ?_
    rw [continuous_prod_of_discrete_right]
    intro m
    have hlu : Continuous fun u : ↥(Subtype.val ⁻¹' V : Set ↥B) => lam u.1.1 :=
      hc.comp_continuous (by fun_prop) fun u => u.2
    exact (continuous_act m.mat).comp hlu

theorem exists_global (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (hB : IsOpen B)
    (hconv : Convex ℝ B)
    (hloc : ∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧
      ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) :
    ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, DifferentiableOn ℂ lam B ∧ ∀ b ∈ B, IsLatBasis (K b) (lam b) := by
  rcases B.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨a₀, ha₀⟩ := hne
  have hcs : ContractibleSpace ↥B := hconv.contractibleSpace ⟨a₀, ha₀⟩
  have hlp : LocallyPathConnectedSpace ↥B := hB.locallyPathConnectedSpace
  obtain ⟨l₀, -, hl₀⟩ := hloc a₀ ha₀
  have cov := isCoveringMap_proj (r := r) hB hloc
  obtain ⟨F, ⟨-, hF⟩, -⟩ := cov.existsUnique_continuousMap_lifts (ContinuousMap.id ↥B) ⟨a₀, ha₀⟩
    ⟨⟨⟨a₀, ha₀⟩, l₀ a₀⟩, hl₀.self_of_nhds⟩ rfl
  have hFb : ∀ x : ↥B, (F x).1.1 = x := fun x => congrFun hF x
  have hbas : ∀ x : ↥B, IsLatBasis (K x) (F x).1.2 := fun x => by
    have := (F x).2
    rwa [hFb x] at this
  classical
  let lamG : (Fin n → ℂ) → Fin r → Fin g → ℂ := fun b => if h : b ∈ B then (F ⟨b, h⟩).1.2 else 0
  have hlamG : ∀ x : ↥B, lamG x = (F x).1.2 := fun x => by simp [lamG, x.2]
  refine ⟨lamG, fun b₀ hb₀ => ?_, fun b hb => hlamG ⟨b, hb⟩ ▸ hbas ⟨b, hb⟩⟩
  obtain ⟨V, lam, hV, hbV, hVB, han, hc, hlat⟩ := local_data hB hloc hb₀
  have hM : ∀ t : ↥V, ∃ M : GLZ r, (F ⟨t, hVB t.2⟩).1.2 = act M.mat (lam t) :=
    fun t => exists_glz (hlat _ t.2) (hbas ⟨t, hVB t.2⟩)
  choose M hM using hM
  have hMc : Continuous M := continuous_of_act (hc.comp_continuous continuous_subtype_val fun t => t.2)
    (by fun_prop) (fun t => (hlat _ t.2).1) M hM
  have hopen : IsOpen (Subtype.val '' (M ⁻¹' {M ⟨b₀, hbV⟩}) : Set (Fin n → ℂ)) :=
    hV.isOpenMap_subtype_val _ ((isOpen_discrete _).preimage hMc)
  have hev : lamG =ᶠ[𝓝 b₀] fun b => act (M ⟨b₀, hbV⟩).mat (lam b) := by
    filter_upwards [hopen.mem_nhds ⟨⟨b₀, hbV⟩, rfl, rfl⟩] with b hb
    obtain ⟨t, ht, rfl⟩ := hb
    rw [show lamG t = (F ⟨t, hVB t.2⟩).1.2 from hlamG ⟨t, hVB t.2⟩, hM t, show M t = M ⟨b₀, hbV⟩ from ht]
  have hd : DifferentiableAt ℂ (fun b => act (M ⟨b₀, hbV⟩).mat (lam b)) b₀ := by
    have hda := han.differentiableAt
    refine differentiableAt_pi.2 fun j => ?_
    simp only [act, ← Int.cast_smul_eq_zsmul ℂ]
    exact DifferentiableAt.fun_sum fun i _ => (differentiableAt_pi.1 hda i).fun_const_smul _
  exact (hev.differentiableAt_iff.2 hd).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh.Glob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalHolomorphicLatticeBasisConvexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex : ∀ (n g r : ℕ) (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)), IsOpen B → Convex ℝ B → (∀ b₀ ∈ B, ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, AnalyticAt ℂ lam b₀ ∧ ∀ᶠ b in 𝓝 b₀, IsLatBasis (K b) (lam b)) → ∃ lam : (Fin n → ℂ) → Fin r → Fin g → ℂ, DifferentiableOn ℂ lam B ∧ ∀ b ∈ B, IsLatBasis (K b) (lam b) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | exact GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Glob.exists_global <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedCombinationOfSpanCoordinateRows
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedCombinationOfSpanCoordinateRows
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.combo_of_bounded_rows_bounded : ∀ (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) (C : ℝ), (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) → ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' := by
  intro X g r r₀ T lam u A C hu hC w hw
  rw [Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  refine ⟨∑ i, |c i| * C, fun x hx => ?_⟩
  have key : ∑ j, ((∑ i, c i • fun j => (A i j : ℝ)) j : ℂ) • lam x j = ∑ i, (c i : ℂ) • u x i := by
    simp_rw [hu x hx, Finset.smul_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, Int.cast_smul_eq_zsmul]
  rw [key]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (u x) i).trans (hC x hx)) (abs_nonneg _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedCombinationOfSpanCoordinateRowsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_combination_of_span_coordinate_rows : ∀ (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) (C : ℝ), (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) → ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' := by
  first | exact @GlobalTheory.combo_of_bounded_rows_bounded | exact GlobalTheory.combo_of_bounded_rows_bounded | (intros; apply GlobalTheory.combo_of_bounded_rows_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverP
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem dvd_of_exp_eq_one (k : ℤ) (N : ℕ) (hN : 0 < N)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (k : ℂ) / N) = 1) : (N : ℤ) ∣ k := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_eq_iff hN'] at hm
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (2 * Real.pi * Complex.I) * ((k : ℂ) + m * N) = 0 := by linear_combination -hm
  have h4 : ((k + m * N : ℤ) : ℂ) = 0 := by push_cast; exact (mul_eq_zero.1 h3).resolve_left hpi
  have h5 : k + m * N = 0 := by exact_mod_cast h4
  exact ⟨-m, by linarith⟩

theorem eq_of_exp_eq (m m' : ℤ) (h : ∀ N : ℕ, 0 < N → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / N) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (m' : ℂ) / N)) : m = m' := by
  have hN : 0 < (m - m').natAbs + 1 := Nat.succ_pos _
  have h1 := h _ hN
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ)) = 1 := by
    have e : -(2 * Real.pi * Complex.I) * (((m - m' : ℤ)) : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) =
        -(2 * Real.pi * Complex.I) * (m : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) -
          -(2 * Real.pi * Complex.I) * (m' : ℂ) / (((m - m').natAbs + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.exp_sub, h1, div_self (Complex.exp_ne_zero _)]
  have h3 := dvd_of_exp_eq_one _ _ hN h2
  have h4 : m - m' = 0 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem hermForm_im_sum (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ) (x y : Fin r → ℤ) :
    (hermForm Hm (∑ j, x j • lam j) (∑ j, y j • lam j)).im =
      ∑ i, ∑ j, (x i : ℝ) * (y j : ℝ) * (hermForm Hm (lam i) (lam j)).im := by
  have hs : ∀ (k : ℤ) (v : Fin g → ℂ), k • v = (k : ℂ) • v := fun k v => (Int.cast_smul_eq_zsmul ℂ k v).symm
  simp only [hermForm, hs, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, star_intCast, Finset.mul_sum, Complex.im_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  ring

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem logDom_facts (n a : ℕ) : IsOpen (logDom n a) ∧ Convex ℝ (logDom n a) ∧
    (∀ s, AnalyticAt ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧
    Set.MapsTo (logExp a) (logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) :=
  GlobalTheory.T.punctPolydiscUniversalCover_open_convex_exp_analytic n a

theorem logExp_ne_zero (n a : ℕ) (s : Fin n → ℂ) (k : Fin n) (hk : (k : ℕ) < a) : logExp a s k ≠ 0 := by
  simp [logExp, hk, Complex.exp_ne_zero]

theorem isLatFam_comp (m n g : ℕ) (B : Set (Fin n → ℂ)) (B' : Set (Fin m → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) : IsLatFam B K → IsOpen B' →
    AnalyticOnNhd ℂ φ B' → Set.MapsTo φ B' B → IsLatFam B' (fun b => K (φ b)) :=
  GlobalTheory.T.isLatFam_comp_of_analyticOnNhd m n g B B' K φ

theorem det_ne_zero_of_herm (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (lam : Fin r → Fin g → ℂ)
    (M : Matrix (Fin r) (Fin r) ℤ) : (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ lam →
    Submodule.span ℝ (Set.range lam) = ⊤ → (∀ i j, (hermForm Hm (lam i) (lam j)).im = M i j) → M.det ≠ 0 :=
  GlobalTheory.T.det_ne_zero_of_imHermForm_integral_real_basis g r Hm lam M

theorem linIndep_rows (g r r₀ : ℕ) (lam : Fin r → Fin g → ℂ) (u : Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) :
    LinearIndependent ℝ u → (∀ i, u i = ∑ m, A i m • lam m) → LinearIndependent ℚ (fun i j => (A i j : ℚ)) :=
  GlobalTheory.T.rat_linearIndependent_coords_of_real_independent g r r₀ lam u A

theorem bounded_span (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ)
    (A : Fin r₀ → Fin r → ℤ) (C : ℝ) : (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) →
    ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' :=
  GlobalTheory.T.bounded_combination_of_span_coordinate_rows X g r r₀ T lam u A C

theorem mem_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b) (i : Fin r) :
    b i ∈ K :=
  (h.2 (b i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩

theorem span_top_of_isLatBasis {g r : ℕ} {K : Set (Fin g → ℂ)} {b : Fin r → Fin g → ℂ} (h : IsLatBasis K b)
    (hK : Submodule.span ℝ K = ⊤) : Submodule.span ℝ (Set.range b) = ⊤ := by
  rw [eq_top_iff, ← hK, Submodule.span_le]
  intro w hw
  obtain ⟨m, rfl⟩ := (h.2 w).1 hw
  exact Submodule.sum_mem _ fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := b) j)) _

end GlobalTheory.ShFam.Hor.LogCh.Core

namespace GlobalTheory.ShFam.Hor.LogCh.Core

theorem core : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ (∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := logDom_facts n a
  have hDp : IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => GlobalTheory.T.exists_analytic_local_lattice_basis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩

  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]

  have hstdK : ∀ j : Fin g, ∀ s ∈ logDom n a, (Pi.single j 1 : Fin g → ℂ) ∈ K (logExp a s) := by
    intro j s hs
    obtain ⟨i, hi⟩ := hstd j
    rw [← hi _ (hEm hs)]
    exact hζK _ (hEm hs) i
  have hρex : ∀ j : Fin g, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a,
      (Pi.single j 1 : Fin g → ℂ) = ∑ k, m k • lam s k := fun j =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun _ => Pi.single j 1) s₀ hDp
      hlamD.continuousOn continuousOn_const hlamB (fun s hs => hstdK j s hs) hs₀
  choose mρ hmρ using hρex

  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex

  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ (logExp a s₀) j = ∑ k, (∑ i, c i • A i) k • lam s₀ k := by
    intro c
    simp only [fun i => hA i s₀ hs₀, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ x y : Fin (2 * g) → ℤ, (hermForm Hm₀ (∑ k, x k • lam s₀ k) (∑ k, y k • lam s₀ k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro x y
    rw [hermForm_im_sum]
    simp only [hM₀, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq, hform, Complex.ofReal_intCast] at h4
    exact dvd_of_exp_eq_one _ N hN h4
  have hdet : (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).det ≠ 0 :=
    det_ne_zero_of_herm g (2 * g) Hm₀ (lam s₀) M hpos₀ (hlamB s₀ hs₀).1
      (span_top_of_isLatBasis (hlamB s₀ hs₀) hspan₀) hM₀
  have hlinQ := linIndep_rows g (2 * g) r₀ (lam s₀) (ζ (logExp a s₀)) A (hζli _ hz₁) (fun i => hA i s₀ hs₀)
  have hco := GlobalTheory.T.coisotropic_sublattice_of_torsion_count (2 * g) r₀ M A hdet hlinQ hdvd

  obtain ⟨C, hC⟩ := hζbd
  have hgr := GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic n a g (2 * g) lam ((M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ).map (Int.cast : ℤ → ℝ))
    (Submodule.span ℝ (Set.range fun i j => (A i j : ℝ))) hlamD
    (fun s hs => by
      obtain ⟨Hm, hH, hpos, hspan, hint, hpair⟩ := hin s hs
      exact ⟨(hlamB s hs).1, span_top_of_isLatBasis (hlamB s hs) hspan, Hm, hH, hpos, fun i j => by
        rw [hM s hs Hm hint hpair i j]; simp⟩)
    (fun v hv => hco v fun i => hv _ (Submodule.subset_span (Set.mem_range_self (f := fun i j => (A i j : ℝ)) i)))
    (fun w hw => by
      obtain ⟨C', hC'⟩ := bounded_span (Fin n → ℂ) g (2 * g) r₀ (logDom n a) lam (fun s => ζ (logExp a s)) A C
        (fun s hs i => hA i s hs) (fun s hs => hC _ (hEm hs)) w hw
      exact ⟨C', fun s hs _ => hC' s hs⟩)
  refine ⟨2 * g, lam, fun j k => (mρ j k : ℂ), hlamD.continuousOn,
    fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ, (hlamB s hs).2, fun j => ?_⟩, hgr⟩
  rw [hmρ j s hs]
  exact Finset.sum_congr rfl fun k _ => Int.cast_smul_eq_zsmul ℂ _ _

end GlobalTheory.ShFam.Hor.LogCh.Core
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverPStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_latticeBasis_punctPolydiscCover_polyGrowth : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ (∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Core.core | exact GlobalTheory.ShFam.Hor.LogCh.Core.core | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Core.core <;> assumption)
end
