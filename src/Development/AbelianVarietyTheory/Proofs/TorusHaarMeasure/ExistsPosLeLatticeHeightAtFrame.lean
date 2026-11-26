module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisMem
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDetAddEqDetMulDetOneAdd
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfHermOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightAtFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanLeNormMinor
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem relIndex_span_le_norm_minor :
    (∀ (r : ℕ) (X : Data E r), ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ e : ι → Fin r, Function.Injective e → (Matrix.of fun k a => w a (e k)).det ≠ 0 → (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ) ≤ C * ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2) := by
  intro r X
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.LatDen.latDen r X).2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨∏ _τ : X.Ψ, ((n : ℝ) ^ r) ^ 2, Finset.prod_pos fun _ _ => by positivity, ?_⟩
  intro ι _ _ w _ hw e he hdet
  set M : Matrix ι ι E := Matrix.of fun k a => w a (e k) with hM
  set L : AddSubgroup (Fin r → E) :=
    X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup with hL
  let A : Matrix ι ι (𝓞 E) := Matrix.of fun k a => ⟨(n : E) * w a (e k), hint _ (hw a) _⟩
  have hA : (algebraMap (𝓞 E) E).mapMatrix A = (n : E) • M := by
    ext k a
    rfl
  have hdetA : ((A.det : 𝓞 E) : E) = (n : E) ^ Fintype.card ι * M.det := by
    rw [← Matrix.det_smul, ← hA, ← RingHom.map_det]
  have hA0 : A.det ≠ 0 := by
    intro h
    rw [h] at hdetA
    exact mul_ne_zero (pow_ne_zero _ hn0) hdet (hdetA.symm.trans rfl)
  let φ : L →+ (ι → 𝓞 E) :=
    { toFun := fun v k => ⟨(n : E) * v.1 (e k), hint _ v.2.1 _⟩
      map_zero' := by
        ext k
        exact mul_zero (n : E)
      map_add' := fun u v => by
        ext k
        exact mul_add (n : E) _ _ }
  set R := (LinearMap.range A.mulVecLin).toAddSubgroup with hR
  have hidx := index_range_mulVecLin_eq_abs_norm_det ι A hA0
  rw [← hR] at hidx
  have hR0 : R.index ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at hidx
    exact hA0 (by exact_mod_cast hidx)
  have hle : R.comap φ ≤ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.addSubgroupOf L := by
    rintro ⟨v, hvΛ, hv⟩ ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
    have hb : M *ᵥ (fun a => (c a : E)) = M *ᵥ b := by
      funext k
      have h := congrArg (algebraMap (𝓞 E) E) (congrFun hc k)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum] at h
      apply mul_left_cancel₀ hn0
      have h2 : (algebraMap (𝓞 E) E) (φ ⟨∑ i, b i • w i, hvΛ, hv⟩ k) =
          (n : E) * (∑ i, b i • w i) (e k) := rfl
      rw [h2] at h
      have h3 : (M *ᵥ b) k = (∑ i, b i • w i) (e k) := by
        simp [Matrix.mulVec, dotProduct, hM, Finset.sum_apply, mul_comm]
      rw [h3, ← h, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, ← mul_assoc]
      rfl
    have hcb := Matrix.mulVec_injective_of_det_ne_zero hdet hb
    change (∑ i, b i • w i) ∈ Submodule.span (𝓞 E) (Set.range w)
    rw [← hcb]
    refine Submodule.sum_mem _ fun a _ => ?_
    exact Submodule.smul_mem _ (c a) (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : (R.comap φ).index ≤ R.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_top_right]
    exact AddSubgroup.relIndex_le_of_le_right le_top (by rwa [AddSubgroup.relIndex_top_right])
  have h0 : (R.comap φ).index ≠ 0 := by
    rw [AddSubgroup.index_comap]
    exact fun h => hR0 (AddSubgroup.index_eq_zero_of_relIndex_eq_zero h)
  have h2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex L ≤ R.index :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (AddSubgroup.index_dvd_of_le hle)).trans h1
  have h3 : (R.index : ℝ) = ∏ τ : X.Ψ, ‖τ.1 ((A.det : 𝓞 E) : E)‖ ^ 2 := by
    rw [← abs_norm_eq_prod_cmType_sq r X, ← hidx, Rat.cast_natCast]
  have hcard : Fintype.card ι ≤ r := by simpa using Fintype.card_le_of_injective e he
  refine (Nat.cast_le.2 h2).trans ?_
  rw [h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun τ _ => ?_
  rw [hdetA, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  gcongr

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormDetSubmatrixSqLeDetGram
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem norm_det_submatrix_sq_le_det_gram :
    ∀ (m : Type) [Fintype m] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix m ι ℂ)
      (e : ι → m), Function.Injective e →
        ‖(M.submatrix e id).det‖ ^ 2 ≤ (Mᴴ * M).det.re := by
  classical
  intro m _ ι _ _ M e he
  set N : Matrix ι ι ℂ := M.submatrix e id with hN
  set s : Finset m := Finset.univ.map ⟨e, he⟩ with hs
  let B : Matrix (sᶜ : Finset m) ι ℂ := fun i j => M i j
  have hsplit : Mᴴ * M = Nᴴ * N + Bᴴ * B := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.add_apply]
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · rw [hs, Finset.sum_map]
      rfl
    · rw [← Finset.sum_coe_sort sᶜ]
  have hN1 : (Nᴴ * N).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self N
  have hB1 : (Bᴴ * B).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have key := (det_re_mono_of_posSemidef ι (Nᴴ * N) (Bᴴ * B) hN1 hB1).2.1
  rw [hsplit]
  refine le_trans (le_of_eq ?_) key
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightAtFrame
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightLower

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_pos_le_height : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∃ m : ℝ, 0 < m ∧ ∀ W, m ≤ d x W) := by
  intro r X d hd x hx
  obtain ⟨C, hC, hCle⟩ := GlobalTheory.relIndex_span_le_norm_minor r X
  have hω : ∀ τ : X.Ψ, ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (M : Matrix (Fin r) ι ℂ), ((mat x τ * M)ᴴ * (mat x τ * M)).det.re ≤ ω * (Mᴴ * M).det.re :=
    fun τ => GlobalTheory.gram_det_mul_le GlobalTheory.det_re_mono_of_posSemidef r (mat x τ)
  choose ω hω1 hωle using hω
  have hΩ : 0 < ∏ τ, ω τ := Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (hω1 τ)
  refine ⟨1 / (C * ∏ τ, ω τ), by positivity, fun W => ?_⟩
  obtain ⟨w, hwi, hwΛ, hspan⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  obtain ⟨e, he, hδ⟩ := GlobalTheory.exists_maximal_minor_ne_zero_of_linearIndependent E r _ w hwi
  have hdW := hd x hx _ w hwi hwΛ
  rw [hspan] at hdW
  rw [hdW]
  have hI0 := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X _ w hwi hwΛ
  have hIle := hCle _ w hwi hwΛ e he hδ
  rw [hspan] at hI0 hIle
  set I := ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex
    (X.Λ.toAddSubgroup ⊓ W.toAddSubgroup)) with hIdef
  have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hI0

  have key : ∀ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      ω τ * (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    intro τ
    have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ)
    have h1 := hωle τ _ ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu] at h1
    have h2 := GlobalTheory.norm_det_submatrix_sq_le_det_gram (Fin r) _
      (Matrix.of fun k a => τ.1 (w a k)) e he
    have h3 : ((Matrix.of fun k a => τ.1 (w a k)).submatrix e id).det =
        τ.1 (Matrix.of fun k a => w a (e k)).det := by
      rw [RingHom.map_det]
      congr 1
    rw [h3] at h2
    exact h2.trans h1
  have hprod : ∏ τ : X.Ψ, ‖τ.1 (Matrix.of fun k a => w a (e k)).det‖ ^ 2 ≤
      (∏ τ, ω τ) * ∏ τ : X.Ψ, (((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
        ((mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => by positivity) (fun τ _ => key τ)
  rw [div_le_div_iff₀ (by positivity) hIpos, one_mul]
  calc (I : ℝ) ≤ C * _ := hIle
    _ ≤ C * ((∏ τ, ω τ) * _) := mul_le_mul_of_nonneg_left hprod hC.le
    _ = _ := by ring

end GlobalTheory.HeightLower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightAtFrameStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_pos_le_latticeHeight_at_frame : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∃ m : ℝ, 0 < m ∧ ∀ W, m ≤ d x W) := by
  first | exact @GlobalTheory.HeightLower.exists_pos_le_height | exact GlobalTheory.HeightLower.exists_pos_le_height | (intros; apply GlobalTheory.HeightLower.exists_pos_le_height <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanMap
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightInv

theorem _root_.GlobalTheory.HeightInv.relIndex_span_map {R K V ι : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) (f : V →ₗ[K] V)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) (hΛ : ∀ x, x ∈ Λ ↔ f x ∈ Λ)
    (w : ι → V) :
    (Submodule.span R (Set.range fun a => f (w a))).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range fun a => f (w a))).toAddSubgroup) =
      (Submodule.span R (Set.range w)).toAddSubgroup.relIndex
        (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup) := by
  let g : V →+ V := f.toAddMonoidHom
  have hg : Function.Injective g := hinj
  have hΛmap : Λ.toAddSubgroup.map g = Λ.toAddSubgroup := by
    ext v
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hΛ x).1 hx
    · intro hv
      obtain ⟨x, rfl⟩ := hsurj v
      exact ⟨x, (hΛ x).2 hv, rfl⟩
  have hK : Submodule.span K (Set.range fun a => f (w a)) = (Submodule.span K (Set.range w)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hR : Submodule.span R (Set.range fun a => f (w a)) =
      (Submodule.span R (Set.range w)).map (f.restrictScalars R) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hKg : ((Submodule.span K (Set.range w)).map f).toAddSubgroup =
      (Submodule.span K (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hRg : ((Submodule.span R (Set.range w)).map (f.restrictScalars R)).toAddSubgroup =
      (Submodule.span R (Set.range w)).toAddSubgroup.map g := by
    ext v
    simp [Submodule.mem_map, AddSubgroup.mem_map, g]
  have hinf : Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup.map g =
      (Λ.toAddSubgroup ⊓ (Submodule.span K (Set.range w)).toAddSubgroup).map g := by
    rw [AddSubgroup.map_inf_eq _ _ _ hg, hΛmap]
  rw [hK, hR, hKg, hRg, hinf, AddSubgroup.relIndex_map_map_of_injective _ _ hg]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem height_lact : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0) ∧ ∀ W : Submodule E (Fin r → E), d (lact γ x) (W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin) = d x W) := by
  intro r X d hd γ hγ x hx
  have hmat : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ :=
    fun τ => rfl
  have hγdet : (γ : Matrix (Fin r) (Fin r) E).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hτdet : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    have := τ.1.map_det (γ : Matrix (Fin r) (Fin r) E)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero τ.1).2 hγdet
  have hx' : ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 := by
    intro τ
    rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hτdet τ) (hx τ)
  refine ⟨hx', fun W => ?_⟩
  obtain ⟨w, hw, hwΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  set f := (γ : Matrix (Fin r) (Fin r) E).mulVecLin with hf
  have hinj : Function.Injective f := Matrix.mulVec_injective_of_isUnit γ.isUnit
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have hΛ : ∀ y, y ∈ X.Λ ↔ f y ∈ X.Λ := hγ.2
  have hw' : LinearIndependent E (fun a => f (w a)) :=
    hw.map' f (LinearMap.ker_eq_bot.2 hinj)
  have hsp' : W.map f = Submodule.span E (Set.range fun a => f (w a)) := by
    conv_lhs => rw [← hsp]
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have e1 := hd (lact γ x) hx' _ (fun a => f (w a)) hw' (fun a => (hΛ _).1 (hwΛ a))
  have e2 := hd x hx _ w hw hwΛ
  have hM : ∀ τ : X.Ψ, (mat (lact γ x) τ)⁻¹ * (Matrix.of fun k a => τ.1 (f (w a) k)) =
      (mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)) := by
    intro τ
    have : (Matrix.of fun k a => τ.1 (f (w a) k)) =
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (Matrix.of fun k a => τ.1 (w a k)) := by
      ext k a
      simp [hf, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, hmat, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hτdet τ).isUnit]
  rw [hsp', e1, relIndex_span_map X.Λ f hinj hsurj hΛ w]
  rw [hsp] at e2
  rw [e2, hsp]
  simp only [hM]

end GlobalTheory.HeightInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightBotTop
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightBotTop
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightEnds

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * (xᴴ)ᵀ := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem norm_det_orth {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (hx : IsOrth X x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 X.Gm.det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (hx τ)
  simp only [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.det_diagonal, norm_mul, norm_star, norm_prod] at h
  have h1 : ∀ a : Fin r, ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  simp only [h1, Finset.prod_const_one] at h
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← h]
  ring

theorem gramDet_square {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    (Nᴴ * N).det.re = ‖N.det‖ ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast

theorem exists_pos_le_bot_top : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, IsOrth X x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  intro r X d hd
  obtain ⟨w0, hw0, hΛ0, hsp0⟩ := GlobalTheory.LatBasis.exists_basis_mem r X ⊤
  have hr : r = Module.finrank E (⊤ : Submodule E (Fin r → E)) := by simp
  let w : Fin r → Fin r → E := w0 ∘ finCongr hr
  have hw : LinearIndependent E w := hw0.comp _ (finCongr hr).injective
  have hΛ : ∀ a, w a ∈ X.Λ := fun a => hΛ0 _
  have hsp : Submodule.span E (Set.range w) = ⊤ := by
    rw [(finCongr hr).surjective.range_comp]; exact hsp0
  have hdet : (Matrix.of w).det ≠ 0 := by
    have : IsUnit (Matrix.of w) := Matrix.linearIndependent_rows_iff_isUnit.1 hw
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X (Fin r) w hw hΛ
  set n : ℕ := (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup) with hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hind)
  let c : ℝ := (∏ τ : X.Ψ, ‖τ.1 X.Gm.det‖ * ‖τ.1 (Matrix.of w).det‖ ^ 2) / n
  have hc : 0 < c := by
    refine div_pos (Finset.prod_pos fun τ _ => mul_pos ?_ (pow_pos ?_ 2)) hnpos
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 X.Gm_det)
    · exact norm_pos_iff.2 ((map_ne_zero τ.1).2 hdet)
  refine ⟨min 1 c, lt_min one_pos hc, fun x hx => ?_⟩
  have hxd : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := by
    intro τ h0
    have := norm_det_orth X x hx τ
    simp [h0] at this
  constructor
  · have h := hd x hxd Empty (fun a => a.elim) linearIndependent_empty_type (fun a => a.elim)
    have hre : Set.range (fun a : Empty => (a.elim : Fin r → E)) = ∅ := Set.range_eq_empty _
    rw [hre] at h
    simp only [Submodule.span_empty, Matrix.det_isEmpty, Complex.one_re, Finset.prod_const_one,
      Submodule.bot_toAddSubgroup, inf_bot_eq, AddSubgroup.relIndex_self, Nat.cast_one,
      div_one] at h
    rw [h]
    exact min_le_left _ _
  · have h := hd x hxd (Fin r) w hw hΛ
    rw [← hn, hsp] at h
    rw [h]
    refine (min_le_right _ _).trans (le_of_eq ?_)
    refine congrArg (· / (n : ℝ)) (Finset.prod_congr rfl fun τ _ => ?_)
    have h1 : (Matrix.of fun k a => τ.1 (w a k)).det = τ.1 (Matrix.of w).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
      rfl
    have h2 := norm_det_orth X x hx τ
    have h3 : ‖(mat x τ).det‖ ≠ 0 := norm_ne_zero_iff.2 (hxd τ)
    rw [gramDet_square, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h1, norm_mul,
      norm_inv, mul_pow, inv_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_right h2

end GlobalTheory.HeightEnds
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsPosLeLatticeHeightBotTopStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_pos_le_latticeHeight_bot_top : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∃ m : ℝ, 0 < m ∧ ∀ x, IsOrth X x → m ≤ d x ⊥ ∧ m ≤ d x ⊤) := by
  first | exact @GlobalTheory.HeightEnds.exists_pos_le_bot_top | exact GlobalTheory.HeightEnds.exists_pos_le_bot_top | (intros; apply GlobalTheory.HeightEnds.exists_pos_le_bot_top <;> assumption)
end
end
