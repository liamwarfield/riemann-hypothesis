module

public import Development.WeilBound.ThetaLifts.SmallCones.GenSmallOf
public import Development.WeilBound.ThetaLifts.SmallCones.Kernel
public import Development.WeilBound.ThetaLifts.SmallCones.TwoExp
public import Development.WeilBound.ThetaLifts.SmallCones.LineInt
public import Development.WeilBound.ThetaLifts.SmallCones.FcCols
public import Development.WeilBound.ThetaLifts.SmallCones.WittOf
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneMain
public import Development.WeilBound.ThetaLifts.SmallCones.IwaExOf
public import Development.WeilBound.ThetaLifts.SmallCones.KFinDataOf
public import Development.WeilBound.ThetaLifts.SmallCones.FormSwapZero
public import Development.WeilBound.ThetaLifts.SmallCones.LinExOf
public import Development.WeilBound.ThetaLifts.SmallCones.SoZero

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.MixABOf
noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open Matrix (vecMulVec)

theorem mixAB_of (hW : MixW) (hX : MixX) (hZ : EvZero) (hP : PairEx) (hE : ThetaExp) (hU : EvUniq) : MixAB := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀
  have hB := hp.base
  have hψ := hB.std
  have p := pg_herm hB hH hp.herm
  have p' := pg_skew hB hH' hp.skew
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n d₁ X W₁ _ _ _ _ hp.herm hp₀.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp.resX hp₀.resW M₁ g₁
    have hz := hZ F E σ B n d X W M χX χW om _ _ _ _ hp d₁ X W₁ H' i₀ i₁ M₁ rfl hH' g₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hz
    obtain ⟨⟨e₁, he₁⟩, h2⟩ := hX F E σ B n d₁ X W₁ M₁ χX χW om₁ _ _ _ _ hp₁ n₁ X₁ H j₀ j₁ M₀ om₀ _ _ hH hp₀
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (polX p (skew_det hp₀.skew)) hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoA H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.one_mul, vv_mul_r]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polA p p').uniq hU hB hp.good hp₀.good (isEv_sumA hψ p' hc) (isEv_sumA hψ p' he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      hW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ _ t' h₁ q' hq' u' hu' Φ hΦ, map_smul,
      h2 e₁ he₁ h₁ t g₁ q hq u hu _ (he₀.maps Φ hΦ), map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n₁ d X₁ W _ _ _ _ hp₀.herm hp.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp₀.resX hp.resW M₁ g₁
    obtain ⟨⟨e₀, he₀⟩, h2⟩ := hX F E σ B n d X W M χX χW om _ _ _ _ hp n₁ X₁ H j₀ j₁ M₁ om₁ _ _ hH hp₁
    have hz := hZ F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ X₁ W₁ H' i₀ i₁ M₀ rfl hH' hp₀.good
    obtain ⟨⟨e₁, he₁⟩, -⟩ := hz
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (pol0 (herm_det hp₀.herm) p') hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoB H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polB p p').uniq hU hB hp.good hp₀.good (isEv_sumB hψ p hc) (isEv_sumB hψ p he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      h2 e₀ he₀ _ t g₁ q hq u hu Φ hΦ, map_smul,
      hW F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ W₁ H' i₀ i₁ M₀ om₀ _ _ hH' hp₀ e₁ he₁ _ t' h₁ q' hq' u' hu' _ (he₀.maps Φ hΦ),
      map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring

end PositivityTheory.ThKCT.Ker
end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.SplitLatMap
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr PositivityTheory.ThKG.Tow.Pln

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_low {n n₁ : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ}
    {ι : Matrix (Fin n) (Fin n₁) ℂ} {P : Matrix (Fin n₁) (Fin n) ℂ} (hP : P * ι = 1) (h : IsCartan M θ) (e : θ * ι = ι * θ₁) :
    IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← Matrix.one_mul (θ₁ * θ₁), ← hP, Matrix.mul_assoc, ← Matrix.mul_assoc ι, ← e, Matrix.mul_assoc θ, ← e,
      ← Matrix.mul_assoc θ, h1, Matrix.one_mul]
  · have m : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ),
        (A * C).map star = A.map star * C.map star := fun A C => Matrix.map_mul (f := starRingEnd ℂ)
    calc _ = (ι * θ₁)ᵀ * M * (ι * θ₁).map star := by simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by rw [← e]; simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  · rw [← gram_vec, Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec]
    refine h3 _ fun h0 => hx ?_
    rw [← Matrix.one_mulVec x, ← hP, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem splitLat_map {v : Pl F} (τ : E →ₐ[F] Fv F v) {n m : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {L' : Submodule (𝓞 E) (Fin m → E)} (A : Matrix (Fin m) (Fin n) E) (h : ∀ z ∈ L, A *ᵥ z ∈ L') {w : Fin n → Fv F v}
    (hw : w ∈ splitLat τ L) : A.map τ *ᵥ w ∈ splitLat τ L' :=
  splitLat_le τ ((splitLat τ L').comap ((A.map τ).mulVecLin.restrictScalars _)) (fun z hz => by
    have e : A.map τ *ᵥ (fun i => τ (z i)) = fun i => τ ((A *ᵥ z) i) :=
      funext fun i => (RingHom.map_mulVec (τ : E →+* Fv F v) A z i).symm
    show A.map τ *ᵥ (fun i => τ (z i)) ∈ splitLat τ L'
    rw [e]
    exact map_mem_splitLat τ (h z hz)) hw

theorem low_eps {B : Base F E} (hB : B.IsGood σ) {ε : E} {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) {D : Submodule (𝓞 E) E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hY : IsEps σ B ε κ D Y r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {ε' : E}
    {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E} (h : IsFr (σ : E →+* E) ε' Y.J Y₁.J H.ι H.x H.y A') :
    1 ≤ r ∧ 1 ≤ s ∧ IsEps σ B ε κ D Y₁ (r - 1) (s - 1) := by
  have hcm := hB.cm
  set P : Matrix (Fin n₁) (Fin n) E := A'.submatrix Sum.inl id with hPd
  have hP : ∀ (u : Fin n₁ → E) (a b : E), P *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = u := fun u a b => funext fun j => by
    have : A' *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = Sum.elim u ![a, b] := by
      rw [← fr_mulVec, Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
    exact congrFun this (Sum.inl j)
  have hPι : P * H.ι = 1 := Matrix.ext fun i j => by
    exact (congrFun (congrFun h.inv2 (Sum.inl i)) (Sum.inl j)).trans (by simp [Matrix.one_apply])
  have hform : ∀ u u', form σ Y₁.J u u' = form σ Y.J (H.ι *ᵥ u) (H.ι *ᵥ u') := hH.gram ▸ form_gram Y.J H.ι
  have hL : Y₁.L = Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := Submodule.ext hH.low
  have cg : ∀ e : E →+* ℂ, (H.ι.map e)ᵀ * (κ • Y.J.map e) * (H.ι.map e).map star = κ • Y₁.J.map e := fun e => by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm, hH.gram]
  have hPe : ∀ {S : Type} [CommRing S] (e : E →+* S), P.map e * H.ι.map e = 1 := fun e => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXX : ∀ e : E →+* ℂ, (fun i => e (H.x i)) ⬝ᵥ (κ • Y.J.map e) *ᵥ star (fun i => e (H.x i)) = 0 := fun e => by
    rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hH.xx, map_zero, smul_zero]
  have hmin : min r s ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := aniso (hY.sig w) h0 (hXX _)
    have h2 : H.x = 0 := funext fun i => (B.emb w).1.injective ((congrFun h1 i).trans (map_zero _).symm)
    have e := hH.xy
    rw [h2, form, zero_dotProduct] at e
    exact zero_ne_one e
  have hlat : (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E))).IsLattice E :=
    Submodule.IsLattice.of_fg E (fg_comap _ (fun u u' e => by
      have := congrArg (P *ᵥ ·) (show H.ι *ᵥ u = H.ι *ᵥ u' from e)
      simpa [Matrix.mulVec_mulVec, hPι] using this) Y.L hY.lat.fg)
  have hfull : (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E))).IsFullLattice E := by
    let := hlat
    refine { span_eq_top := ?_ }
    apply top_unique
    intro u _
    have hz : H.ι *ᵥ u ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
      rw [Submodule.IsFullLattice.span_eq_top (self := hY.lat)]
      trivial
    have hmap : ∀ z ∈ Y.L, P *ᵥ z ∈
        Submodule.span E (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) : Set (Fin n₁ → E)) := by
      intro z hz
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      apply Submodule.subset_span
      change H.ι *ᵥ (P *ᵥ (a • H.x + H.ι *ᵥ u' + b • H.y)) ∈ Y.L
      rw [add_comm (a • H.x), hP]
      exact (hH.low u').1 hu'
    have hspan := (Submodule.span_le.mpr (show (Y.L : Set (Fin n → E)) ⊆
        (Submodule.span E (Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) : Set (Fin n₁ → E))).comap (Matrix.mulVecLin P) from hmap)) hz
    simpa only [Submodule.mem_comap, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hPι, Matrix.one_mulVec] using hspan
  refine ⟨by omega, by omega, fun i j => ?_, fun w => ?_, hL ▸ hfull, fun u => ?_,
    fun w => ?_, fun v u => ?_⟩
  · rw [← form_single (σ := σ) Y₁.J j i, ← form_single (σ := σ) Y₁.J i j, hform, hform, form_swap hcm hY.herm]
  · rw [← cg]
    refine (real_plane _ (fun i => (B.emb w).1 (H.x i)) (κ • fun i => (B.emb w).1 (H.y i)) _ (P.map (B.emb w).1) hH.rank
      (map_herm hcm _ (hκ _) hY.herm) (hXX _) ?_ ?_ ?_ ?_ (hPe _) (hY.sig w)).1
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.yy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.xy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J H.ι H.x (fun u => (hH.orth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J H.ι H.y (fun u => (hH.orth u).2), smul_zero, smul_zero]
  · refine ⟨fun hu u' hu' => ?_, fun G => (hH.low u).2 ((hY.dual _).2 fun z hz => ?_)⟩
    · rw [hform]; exact (hY.dual _).1 ((hH.low u).1 hu) _ ((hH.low u').1 hu')
    · obtain ⟨_, _, u', -, -, hu', hz'⟩ := hH.split z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (hH.orth u).1,
        (hH.orth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform]
      exact G u' hu'
  · rw [← cg]
    exact cartan_low (hPe _) (hY.cartan w) (hH.cartan w).1
  · have hn := hH.rank
    let f : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, by have := j.2; unfold skip; split_ifs <;> omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by
      have := congrArg Fin.val e
      simp only [f, skip] at this
      split_ifs at this <;> omega)
    let T : Matrix (Fin n) (Fin n₁) (Fv F v.1) := (1 : Matrix (Fin n) (Fin n) _).submatrix id f
    have e1 : (Y.bas v).1 * T = H.ι.map (B.τ v) * (Y₁.bas v).1 := Matrix.ext fun a j => by
      rw [← (hH.bas v (f j)).2.2 j rfl a]
      simp [T, Matrix.mul_apply, Matrix.one_apply]
    have e2 : (∀ i, u i ∈ v.1.adicCompletionIntegers F) ↔ ∀ i, (T *ᵥ u) i ∈ v.1.adicCompletionIntegers F := by
      refine ⟨fun G i => sum_mem fun j _ => mul_mem ?_ (G j), fun G j => ?_⟩
      · simp only [T, Matrix.submatrix_apply, Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simpa [T, Matrix.mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using G (f j)
    rw [e2, hY.bas v, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    refine ⟨fun G => ?_, splitLat_map _ _ fun z hz => (hH.low z).1 hz⟩
    have := splitLat_map (L' := Y₁.L) _ P (fun z hz => by
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      rwa [add_comm (a • H.x), hP]) G
    rwa [Matrix.mulVec_mulVec, show P.map (B.τ v) * H.ι.map (B.τ v) = 1 from hPe (B.τ v : E →+* Fv F v.1),
      Matrix.one_mulVec] at this

theorem low_of : Low := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hH
  refine ⟨fun hY => ?_, fun hY => ?_⟩
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inl hY) hH
    simp only [isHerm_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inr hY) hH
    simp only [isSkew_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.Unfold
section -- merged from Development.WeilBound.ThetaLifts.SmallCones.UnfMain
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise

namespace PositivityTheory.ThKCT.Unf

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  {T : Type} [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  {μN : Measure N} [SigmaFinite μN] [IsFiniteMeasureOnCompacts μN] {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0}
  (ν : Measure G) [ν.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure] (μT : Measure T) [μT.IsHaarMeasure]

theorem integral_eq_of {X : Type} [MeasurableSpace X] {μ₁ μ₂ : Measure X} {f : X → ℂ} (hf : Measurable f)
    (h : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → ∫⁻ x, ψ (f x) ∂μ₁ = ∫⁻ x, ψ (f x) ∂μ₂) : ∫ x, f x ∂μ₁ = ∫ x, f x ∂μ₂ := by
  have e : μ₁.map f = μ₂.map f := by
    ext s hs
    rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) hf,
      lintegral_map (measurable_one.indicator hs) hf, h _ (measurable_one.indicator hs)]
  have k : ∀ μ : Measure X, ∫ x, f x ∂μ = ∫ z, z ∂(μ.map f) := fun μ =>
    (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
  rw [k, k, e]

theorem unfold_abs (h : Par μN nn ι mm χ) {K : Subgroup G} (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure]
    (hG : ∀ g, ∃ p u t, ∃ k ∈ K, g = nn p * ι u * mm t * k) {Γ Q ΓN : Subgroup G} [Countable Γ] [DiscreteTopology Γ]
    (hQ : Q ≤ Γ) {Γ₁ : Subgroup H} [Countable Γ₁]
    (hN : ΓN ≤ Q) (hNn : ∀ δ ∈ ΓN, ∃ p, δ = nn p) (h₁ : ∀ γ ∈ Γ₁, ι γ ∈ Q)
    (hb : ∀ q ∈ Q, ∃! z : Γ₁ × ΓN, q = ι z.1 * z.2) {C : Set N} (hC : IsCompact C)
    (hcov : ∀ p, ∃ δ ∈ ΓN, ∃ p' ∈ C, δ * nn p = nn p') {D₁ : Set H} (hD₁ : IsFundamentalDomain Γ₁ D₁ μH)
    {D : Set G} (hD : IsFundamentalDomain Γ D ν) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (I : Type) (r : I → G), (∀ x, r x ∈ Γ) → (∀ γ ∈ Γ, ∃! x, γ * (r x)⁻¹ ∈ Q) → ∀ f : G → ℂ, Continuous f →
      (∀ p g, f (nn p * g) = f g) → (∀ q ∈ Q, ∀ g, f (q * g) = f g) →
      ∫⁻ k, ∫⁻ t, (∫⁻ u in D₁, ‖f (ι u * mm t * k.1)‖ₑ ∂μH) * χ t ∂μT ∂μK < ⊤ →
      (∀ᵐ g ∂(ν.restrict D), Summable fun x => f (r x * g)) ∧ IntegrableOn (fun g => ∑' x, f (r x * g)) D ν ∧
        ∫ g in D, ∑' x, f (r x * g) ∂ν = κ * ∫ k, ∫ t, (∫ u in D₁, f (ι u * mm t * k.1) ∂μH) * ((χ t : ℝ) : ℂ) ∂μT ∂μK := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Countable Q := (Subgroup.inclusion_injective hQ).countable
  haveI : DiscreteTopology Q := DiscreteTopology.of_continuous_injective
    (continuous_inclusion hQ) (Subgroup.inclusion_injective hQ)
  have ci := h.ci.measurable
  have cm := h.cm.measurable
  have hχ : Measurable fun s => (χ s : ℝ≥0∞) := h.cχ.measurable.coe_nnreal_ennreal
  obtain ⟨c, c0, c1, hc⟩ := haar_eq ν μH μT h hK μK hG
  obtain ⟨a, a0, a1, ha⟩ := fold μH h hN hNn h₁ hb hC hcov hD₁
  obtain ⟨𝓖, g1, g2, g3⟩ := exists_cut Q
  have k0 : a / c ≠ 0 := (ENNReal.div_pos a0 c1).ne'
  have k1 : a / c ≠ ⊤ := ENNReal.div_ne_top a1 c0
  refine ⟨(a / c).toReal, ENNReal.toReal_pos k0 k1, fun I r hr hu f hf i1 i2 hfin => ?_⟩
  have hinj : Function.Injective fun x => (⟨r x, hr x⟩ : Γ) := fun x x' e =>
    (hu _ (hr x)).unique (by simp) (by rw [show r x = r x' from congrArg Subtype.val e]; simp)
  haveI := hinj.countable
  obtain ⟨𝓕, f1, f2⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.unf G ν Γ Q hQ D hD I r hr hu
  have key : ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ p g, φ (nn p * g) = φ g) → (∀ q ∈ Q, ∀ g, φ (q * g) = φ g) →
      ∫⁻ g in D, ∑' x, φ (r x * g) ∂ν = a / c * ∫⁻ k, ∫⁻ t, (∫⁻ u in D₁, φ (ι u * mm t * k.1) ∂μH) * χ t ∂μT ∂μK :=
    fun φ hφ j1 j2 => by
      have hβ : Measurable (𝓖.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator g1
      have e1 : ∫⁻ g in 𝓖, φ g ∂ν = ∫⁻ g, 𝓖.indicator 1 g * φ g ∂ν := by
        rw [← lintegral_indicator g1]
        exact lintegral_congr fun g => by by_cases h : g ∈ 𝓖 <;> simp [h]
      have e2 := hc (fun g => 𝓖.indicator 1 g * φ g) (hβ.mul hφ)
      simp only [mul_assoc _ (mm _), ha _ hβ g2 φ hφ j1 j2, mul_assoc a] at e2
      simp only [lintegral_const_mul' _ _ a1] at e2
      rw [f2 φ hφ, f1.setLIntegral_eq (g3 ν) φ fun q x => j2 q q.2 x, e1, ENNReal.div_eq_inv_mul, mul_assoc]
      simp only [mul_assoc _ (mm _)]
      rw [← e2, ← mul_assoc, ENNReal.inv_mul_cancel c0 c1, one_mul]
  have hm := hf.measurable
  have n1 := key (fun g => ‖f g‖ₑ) hm.enorm (fun p g => by rw [i1]) fun q hq g => by rw [i2 q hq]
  have n2 : ∫⁻ g in D, ∑' x, ‖f (r x * g)‖ₑ ∂ν < ⊤ := by rw [n1]; exact ENNReal.mul_lt_top k1.lt_top hfin
  have hx : ∀ x, Measurable fun g => f (r x * g) := fun x => hm.comp (measurable_const_mul _)
  refine ⟨(ae_lt_top (Measurable.tsum fun x => (hx x).enorm) n2.ne).mono fun g hg => ?_,
    ⟨(Measurable.tsum hx).aestronglyMeasurable, (lintegral_mono fun g => enorm_tsum_le_tsum_enorm).trans_lt n2⟩, ?_⟩
  · exact Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 hg.ne)
  set wd := μT.withDensity fun s => (χ s : ℝ≥0∞) with hwd
  set ρ := μK.prod (wd.prod (μH.restrict D₁)) with hρ
  have hπ : Measurable fun z : K × T × H => ι z.2.2 * mm z.2.1 * z.1.1 := by fun_prop
  have L1 : ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ g, φ g ∂(Measure.sum fun x => (ν.restrict D).map (r x * ·)) =
      ∫⁻ g in D, ∑' x, φ (r x * g) ∂ν := fun φ hφ => by
    rw [lintegral_sum_measure, lintegral_tsum fun x => Measurable.aemeasurable (by fun_prop)]
    exact tsum_congr fun x => lintegral_map hφ (measurable_const_mul _)
  have L2 : ∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ z, φ (ι z.2.2 * mm z.2.1 * z.1.1) ∂ρ =
      ∫⁻ k, ∫⁻ t, (∫⁻ u in D₁, φ (ι u * mm t * k.1) ∂μH) * χ t ∂μT ∂μK := fun φ hφ => by
    rw [hρ, lintegral_prod _ (Measurable.aemeasurable (by fun_prop))]
    refine lintegral_congr fun k => ?_
    rw [lintegral_prod _ (Measurable.aemeasurable (by fun_prop)), hwd,
      lintegral_withDensity_eq_lintegral_mul _ hχ (by fun_prop)]
    exact lintegral_congr fun t => mul_comm _ _
  have I1 : Integrable f (Measure.sum fun x => (ν.restrict D).map (r x * ·)) :=
    ⟨hm.aestronglyMeasurable, (L1 _ hm.enorm).trans_lt n2⟩
  have I2 : Integrable (fun z : K × T × H => f (ι z.2.2 * mm z.2.1 * z.1.1)) ρ :=
    ⟨(hm.comp hπ).aestronglyMeasurable, (L2 _ hm.enorm).trans_lt hfin⟩
  have e := integral_eq_of (μ₁ := Measure.sum fun x => (ν.restrict D).map (r x * ·))
    (μ₂ := (a / c) • ρ.map fun z : K × T × H => ι z.2.2 * mm z.2.1 * z.1.1) hm fun ψ hψ => by
      rw [L1 (fun g => ψ (f g)) (hψ.comp hm), lintegral_smul_measure, lintegral_map (f := fun g => ψ (f g)) (hψ.comp hm) hπ,
        smul_eq_mul]
      exact (key (fun g => ψ (f g)) (hψ.comp hm) (fun p g => congrArg ψ (i1 p g)) fun q hq g => congrArg ψ (i2 q hq g)).trans
        (congrArg _ (L2 (fun g => ψ (f g)) (hψ.comp hm)).symm)
  rw [integral_sum_measure I1, integral_smul_measure, integral_map hπ.aemeasurable hm.aestronglyMeasurable, hρ,
    integral_prod _ I2] at e
  rw [integral_tsum (fun x => (hx x).aestronglyMeasurable)
    (by rw [← lintegral_tsum fun x => (hx x).enorm.aemeasurable]; exact n2.ne)]
  refine Eq.trans (tsum_congr fun x => (integral_map (measurable_const_mul _).aemeasurable hm.aestronglyMeasurable).symm)
    (e.trans ?_)
  rw [Complex.real_smul]
  congr 1
  refine integral_congr_ae (I2.prod_right_ae.mono fun k hk => ?_)
  simp only at hk ⊢
  rw [integral_prod _ hk, hwd, integral_withDensity_eq_integral_smul h.cχ.measurable]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [NNReal.smul_def, Complex.real_smul, mul_comm]

end PositivityTheory.ThKCT.Unf
end

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr Unf
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def fixQ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {δ | δ ∈ ratU σ J ∧ mat δ *ᵥ incV F x = incV F x}
  one_mem' := ⟨Subgroup.one_mem _, Matrix.one_mulVec _⟩
  mul_mem' := fun ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by rw [mat_mul, ← Matrix.mulVec_mulVec, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by conv_lhs => rw [← ha.2, mat_cancel]⟩

theorem exists_iso {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J} (hg : g ∈ ratU σ J) {x : Fin n → E} (h0 : x ≠ 0)
    (hx : form σ J x x = 0) : ∃ z : Fin n → E, z ≠ 0 ∧ form σ J z z = 0 ∧ incV F z = mat g *ᵥ incV F x := by
  obtain ⟨M, hM⟩ := mem_ratU.1 hg
  have e : incV F (M *ᵥ x) = mat g *ᵥ incV F x := by
    rw [hM]
    exact funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) M x i
  have hU : Mᵀ * J * M.map σ = J := by
    apply Matrix.map_injective (inclR_inj (F := F))
    have := g.2
    change (mat g)ᵀ * _ * (mat g).map _ = _ at this
    rw [hM] at this
    simp only [Matrix.map_mul]
    exact this
  refine ⟨M *ᵥ x, fun h => h0 (funext fun i => inclR_inj (F := F) ?_), ?_, e⟩
  · have := mat_cancel g (incV F x)
    rw [← e, h, show incV F (0 : Fin n → E) = 0 from funext fun _ => map_zero _, Matrix.mulVec_zero] at this
    exact (congrFun this i).symm.trans (map_zero _).symm
  · have e2 : (fun i => σ ((M *ᵥ x) i)) = M.map σ *ᵥ fun i => σ (x i) := funext fun i => RingHom.map_mulVec (σ : E →+* E) M x i
    rw [← hx, form, form, e2]
    conv_rhs => rw [← hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

theorem unfold_of : Unfold := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s hB hX hH K μK μ ν D ν₁ D₁ lev hK _ _ _ hD _ hD₁ hlev
  have hY : X.IsHerm σ B r s ∨ X.IsSkew σ B r s := Or.inl hX
  obtain ⟨ε, A', hfr⟩ := isFr hB hY hH
  have hd : IsUnit X₁.J.det := hfr.isUnit_det (det_ne hY).isUnit
  have hJ : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX.herm]
  have hJ₁ : ∀ i j, σ (X₁.J j i) = (((1 : ℤˣ) : ℤ) : E) * X₁.J i j := fun i j => by
    have e : ∀ i j, X₁.J i j = form σ X.J (fun k => H.ι k i) (fun k => H.ι k j) := fun i j => by
      rw [← hH.gram, Matrix.mul_assoc]; rfl
    rw [e, e, form_eps (PositivityTheory.ThKG.Tow.Levi.sig_sig hB.cm) hJ]
  obtain ⟨_, _, _, _, _, -⟩ := PositivityTheory.ThKF.unimodLC hB.cm hJ (det_ne hY)
  obtain ⟨_, _, _, _, _, -⟩ := PositivityTheory.ThKF.unimodLC hB.cm hJ₁ hd.ne_zero
  obtain ⟨-, _, _, _, _, _, -⟩ := ideleTop F E
  haveI := PositivityTheory.ThKF.countable_ratU σ X.J
  haveI := PositivityTheory.ThKF.countable_ratU σ X₁.J
  haveI := PositivityTheory.ThKF.discrete_ratU hB.cm hJ (det_ne hY)
  obtain ⟨s1, s2, s3⟩ := stabDec_of F E σ B n n₁ X X₁ H j₀ j₁ r s hB hY hH
  obtain ⟨N, _, _, _, _, μN, _, _, nn, ι, mm, χ, hP, c1, c2, c3, -, C, hC, hcov⟩ := parEx hB hY hH
  have l1 : ∀ g, IsLevi H 1 g (ι g) := fun g => by simpa using c3 1 g
  have l2 : ∀ g ∈ ratU σ X₁.J, ι g ∈ ratU σ X.J := fun g hg => s2 1 g hg _ (by rw [map_one]; exact l1 g)
  have el : ∀ t g, lev (t, g) = ι g * mm t := fun t g => levi_uniq hfr (hlev t g) (c3 t g)
  have eχ : ∀ t, (absE F E t : ℝ) ^ (1 - (n : ℝ)) = χ t := fun t => by
    have h1 : (χ t : ℝ) * (absE F E t : ℝ) ^ (n₁ + 1) = 1 := by exact_mod_cast c1 t
    rw [eq_inv_of_mul_eq_one_left h1, ← Real.rpow_natCast, ← Real.rpow_neg (NNReal.coe_nonneg _), hH.rank]
    congr 1
    push_cast
    ring
  obtain ⟨κ, hκ, hmain⟩ := unfold_abs ν ν₁ μ hP hK.1 μK (Γ := ratU σ X.J) (Q := fixQ X.J H.x)
    (ΓN := ratU σ X.J ⊓ unip σ X H) (Γ₁ := ratU σ X₁.J) (fun g => by
      obtain ⟨p, k, l, hk, hp, rfl⟩ := hK.2 g
      obtain ⟨u, hu, g₁, m, hm, rfl, -⟩ := s1 p l hp
      obtain ⟨q, rfl⟩ := (c2 u).1 hu
      exact ⟨q, g₁, l, k, hk, by rw [levi_uniq hfr hm (c3 l g₁), ← mul_assoc (nn q)]⟩)
    (fun _ h => h.1) (fun δ h => ⟨h.1, (mem_unip.1 h.2).1⟩) (fun δ h => (c2 δ).1 h.2)
    (fun γ h => ⟨l2 γ h, (l1 γ).1.trans (one_smul _ _)⟩) (fun q hq => by
      obtain ⟨u, hu, g₁, m, hm, rfl, hr⟩ := s1 q 1 (hq.2.trans (one_smul _ _).symm)
      obtain rfl := levi_uniq hfr hm (l1 g₁)
      have key : ∀ z z' : ratU σ X₁.J × (ratU σ X.J ⊓ unip σ X H : Subgroup _), ι z.1 * z.2 = ι z'.1 * z'.2 → z = z' :=
        fun z z' e => by
          obtain ⟨p, hp⟩ := (c2 _).1 z.2.2.2
          obtain ⟨p', hp'⟩ := (c2 _).1 z'.2.2.2
          obtain ⟨L, -, hL⟩ := hP.h2 z.1
          obtain ⟨L', -, hL'⟩ := hP.h2 z'.1
          have e1 : z.1 = z'.1 := Subtype.ext (congrArg (fun w => w.2.1)
            (hP.emb.injective (a₁ := (L p, z.1.1, 1)) (a₂ := (L' p', z'.1.1, 1)) (by
              simp only [map_one, mul_one, ← hL, ← hL', ← hp, ← hp', e])))
          rw [e1] at e
          exact Prod.ext e1 (Subtype.ext (mul_left_cancel e))
      refine ⟨(⟨g₁, hr hq.1⟩, ⟨(ι g₁)⁻¹ * u * ι g₁, ?_, levi_conj hm hu⟩), by simp only; group, fun z hz => key _ _ ?_⟩
      · rw [mul_assoc]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (l2 _ (hr hq.1))) hq.1
      · rw [← hz]; simp only; group)
    hC (fun p => by
      obtain ⟨q, h1, h2⟩ := hcov p
      exact ⟨nn q, ⟨h1, (c2 _).2 ⟨q, rfl⟩⟩, h2⟩) hD₁ hD
  refine ⟨κ, hκ, fun γ hγ f hf i1 i2 hfin => ?_⟩
  simp only [el, eχ, ENNReal.ofReal_coe_nnreal] at hfin ⊢
  refine hmain _ γ (fun x => (hγ x).1) (fun g hg => ?_) f hf (fun p => i1 _ ((c2 _).2 ⟨p, rfl⟩)) (fun q hq => i2 q hq.1 hq.2) hfin
  have hx0 : H.x ≠ 0 := fun h => by
    have := hH.xy
    rw [h, form, zero_dotProduct] at this
    exact zero_ne_one this
  have k : ∀ x : IsoV σ X, g * (γ x)⁻¹ ∈ fixQ X.J H.x ↔ incV F x.1 = mat g⁻¹ *ᵥ incV F H.x := fun x => by
    have e : mat (g * (γ x)⁻¹) *ᵥ incV F H.x = mat g *ᵥ incV F x.1 := by
      rw [mat_mul, ← Matrix.mulVec_mulVec, ← (hγ x).2, mat_cancel]
    refine ⟨fun h => by rw [← h.2, e, mat_cancel], fun h => ⟨Subgroup.mul_mem _ hg (Subgroup.inv_mem _ (hγ x).1), ?_⟩⟩
    rw [e, h, mat_cancel']
  obtain ⟨z, z0, z1, z2⟩ := exists_iso (Subgroup.inv_mem _ hg) hx0 hH.xx
  exact ⟨⟨z, z0, z1⟩, (k _).2 z2, fun x hx => Subtype.ext (funext fun i => inclR_inj (F := F)
    (congrFun (((k x).1 hx).trans z2.symm) i))⟩

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.UnipEx
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr
open GlobalTheory.Doubling (absE)

theorem unipEx_of : UnipEx := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have G := PositivityTheory.ThKEnd.Grp.unipGood hB.cm (hY.imp (·.herm) (·.skew)) (det_ne hY)
    ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, (h.isUnit_det (det_ne hY).isUnit).ne_zero⟩
  refine ⟨G.ex, G.cov, G.closed, G.right, ?_, fun u hu => ⟨(mem_unip.1 hu).1, ?_⟩, ?_⟩
  · choose m h1 h2 using exists_levi hB.cm h
    let lev : (AE F E)ˣ × UA σ Y₁.J →* UA σ Y.J := MonoidHom.mk' (fun z => m z.1 z.2)
      fun a b => levi_uniq h (h1 _ _) (levi_mul (h1 _ _) (h1 _ _))
    have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    have c1 : Continuous fun z => mat (lev z) := by
      have e : (fun z => mat (lev z)) = fun z => _ := funext fun z => h2 z.1 z.2
      rw [e]
      refine (continuous_const.matrix_mul (continuous_matrix fun i j => ?_)).matrix_mul continuous_const
      rcases i with i | i <;> rcases j with j | j
      · exact (PositivityTheory.ThKEnd.Grp.continuous_mat.comp continuous_snd).matrix_elem i j
      · exact continuous_const
      · exact continuous_const
      · fin_cases i <;> fin_cases j
        exacts [Units.continuous_val.comp continuous_fst, continuous_const, continuous_const,
          hc.comp (Units.continuous_coe_inv.comp continuous_fst)]
    refine ⟨lev, Continuous.subtype_mk (f := fun z => (lev z).1) (Units.continuous_iff.2 ⟨c1, ?_⟩) _, h1,
      fun t g p hp => levi_uniq h hp (h1 t g)⟩
    have e : (fun z => mat (lev z)⁻¹) = (fun z => mat (lev z)) ∘ fun z => z⁻¹ := funext fun z => by simp
    exact (e ▸ c1.comp continuous_inv : Continuous fun z => mat (lev z)⁻¹)
  · exact h.ad.fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm) u.2 (mem_unip.1 hu).1
  · obtain ⟨t, ht⟩ : ∃ t, absE F E t = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := ⟨_, GlobalTheory.Eis.Conv.absE_halfE F E σ hB.cm⟩
    refine ⟨t⁻¹, ?_⟩
    rw [map_inv, ht, inv_inv, NNReal.coe_pow]
    exact one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.Leaves
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lawα {n d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {x y : ℝ} {T : UA σ W.J → ℂ}
    (_n : n = n) (h : HasLaw W₁ H' χ x T) (e1 : χ = χ') (e2 : x = y) : HasLaw W₁ H' χ' y T := by subst e1 e2; exact h

theorem splitEx_of (hB : GenBig) (hSm : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hZ : EvZero) (hU : UnipEx) (hL : Low) (hT : TriplePair) : SplitEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h d₁ W₁ H' i₀ i₁ hH'
  obtain ⟨hp, hp', hw⟩ := hT F E σ B a a' G X om om' h
  obtain ⟨h1, h2, hW₁⟩ := (hL F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ h.base hH').2 h.geo.hW
  have hlt := h.geo.lt
  have hev := h.geo.even
  have heB := h.geo.eBig
  have haB := h.geo.aBig
  obtain ⟨k, hk⟩ := hev
  have uniq : ∀ f fa fb, Split2 W₁ H' X f fa fb → ∃! x : (UA σ G.W.J → ℂ) × (UA σ G.W.J → ℂ), Split2 W₁ H' X f x.1 x.2 :=
    fun f fa fb hs => ⟨(fa, fb), hs, fun y hy => Prod.ext (split_uniq hU h hH' hy hs).1 (split_uniq hU h hH' hy hs).2⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V W₁ _ _ _ _ h.geo.hV hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp.hX hp.hW hp.resX (res_low hp.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp d₁ G.V W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + a') d₁ G.V G.W W₁ H' i₀ i₁ (a - G.p) G.p _ _ G.M M₁
      (by omega) ⟨(a - a') / 2, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om om₁ (IsPair.cast hp rfl rfl (by omega) (by omega)) hp₁ Φ hΦ (by simp)
    exact uniq _ A₁ A₀ ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V' W₁ _ _ _ _ h.geo.hV' hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp'.hX hp'.hW hp'.resX (res_low hp'.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp' d₁ G.V' W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anySmall hSm hA hK hS hI hP hPl hC F E σ B a' (a + a') d₁ G.V' G.W W₁ H' i₀ i₁ G.q (a' - G.q) _ _ G.M' M₁
      (by omega) ⟨(a - a') / 2 + 1, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om' om₁ (IsPair.cast hp' rfl rfl (by omega) (by omega)) hp₁ Φ hΦ.1 (fun _ => hΦ.2)
    exact uniq _ A₀ A₁ ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩

theorem ctBigZero_of (hB : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hU : UnipEx) (hT : TriplePair) : CTBigZero := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain ⟨eV, ep, eq, hH, hH'⟩ := hc
  dsimp only at eV ep eq hH hH' he
  subst eV ep
  by_cases hex : ∃ X om om', IsTriple B G X om om'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' _ _ h => absurd ⟨X, om, om', h⟩ hex⟩
  obtain ⟨X0, o, o', h0⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨C₀, hC₀, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + (b + 2)) (a + b) G.V G.W W₁ H' _ _ (a - G.p) G.p
    (a + b - (G.p + q₁)) (G.p + q₁) G.M M₁ (by omega) ⟨(a - (b + 2)) / 2, by omega, by omega⟩ hH' e he
  refine ⟨C₀, hC₀, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₁ (IsPair.cast (hT F E σ B _ _ G X om om' h).1 rfl rfl (by omega) (by omega))
    (hT F E σ B _ _ _ X om₁ om₁' h₁).1 Φ hΦ (by simp)
  have := split_uniq hU h hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.2]
  exact c4 g m hm x (by simp)

theorem ctSmallZero_of (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hT : TriplePair) : CTSmallZero := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he
  obtain ⟨C, hC, H0⟩ := hA F E σ B a' _ _ G.V' G.W G₁.W H' _ _ G.q (a' - G.q) (b + 2 + a' - (G.p + G.q)) (G.p + G.q)
    (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) G₁.V' G.M' G₁.M' hc.eV (by rw [hc.q0]; simp) hc.hH' e he
  refine ⟨C, hC, fun X om om' om₁ om₁' h h₁ Φ hΦ => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  obtain ⟨K, μK, μ, hK1, -⟩ := hS F E σ B _ G.V' _ _ h.base hp.herm
  obtain ⟨A₀, c1, c2, c3⟩ := H0 _ _ om' om₁' hp
    (IsPair.cast (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1 (by rw [hc.q0, hc.q1]) (by rw [hc.q0, hc.q1]) rfl rfl) Φ
    (hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ).1
  exact ⟨A₀, ⟨by rwa [add_zero], c2, fun t m _ h => by simp⟩, c3⟩

theorem ctBigCone_of (hB : GenBig) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTBigCone := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.q0
  have e3 := hc.q1
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V G₁.W _ _ _ _ h0.geo.hV h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ o _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).1 _ G.V G₁.W H' _ _ M₁ rfl hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ (b - G₁.p) G₁.p (b + a' - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M G₁.M hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM he₀ he ((b + 2 - a') / 2) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V _ _ H h0.base h0.geo.hV (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨hs1, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₂ om₁ (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hs1 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.1, (c4 g m hm x).1, inv_div]
  rfl

theorem ctSmallCone_of (hB : GenSmall) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTSmallCone := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.eq
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V' G₁.W _ _ _ _ h0.geo.hV' h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ o' _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).2.1 _ G.V' G₁.W H' _ _ M₁ rfl
    hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V' G.W G₁.V' G₁.W H H' _ _ _ _ G₁.q (b - G₁.q) (a + b - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M' G₁.M' hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM' he₀ he ((a - (b + 2)) / 2 + 1) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V' _ _ H h0.base h0.geo.hV' (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨-, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ.1
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om' om₂ om₁' (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hΦ.2 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₀) (fb' := A₁) ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩
  rw [this.2, (c4 g m hm x).1]
  rfl

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.SchInt
noncomputable section

namespace PositivityTheory.ThKCT

namespace SchI

open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cd (f : SchwartzMap V ℂ) (j : ℕ) : ContDiff ℝ j f := f.smooth j

def jet (k j : ℕ) (f : SchwartzMap V ℂ) : V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖x‖ ^ k • iteratedFDeriv ℝ j f x)
    ((continuous_norm.pow k).smul ((cd f j).continuous_iteratedFDeriv le_rfl)) (SchwartzMap.seminorm ℂ k j f) fun x => by
      rw [norm_smul, norm_pow, norm_norm]
      exact SchwartzMap.le_seminorm ℂ k j f x

theorem jet_apply (k j : ℕ) (f : SchwartzMap V ℂ) (x : V) : jet k j f x = ‖x‖ ^ k • iteratedFDeriv ℝ j f x := rfl

theorem norm_jet (k j : ℕ) (f : SchwartzMap V ℂ) : ‖jet k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  refine le_antisymm (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _) ?_
  refine SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _) fun x => ?_
  have := (jet k j f).norm_coe_le_norm x
  rwa [jet_apply, norm_smul, norm_pow, norm_norm] at this

def J (k j : ℕ) : SchwartzMap V ℂ →L[ℂ] V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (jet k j)
    (fun f g => by
      ext1 x
      rw [BoundedContinuousFunction.add_apply, jet_apply, jet_apply, jet_apply, ← smul_add]
      exact congrArg _ (iteratedFDeriv_add_apply (cd f j).contDiffAt (cd g j).contDiffAt))
    (fun a f => by
      ext1 x
      rw [BoundedContinuousFunction.smul_apply, jet_apply, jet_apply, RingHom.id_apply, smul_comm a]
      exact congrArg _ (iteratedFDeriv_const_smul_apply (cd f j).contDiffAt))
    ⟨{(k, j)}, 1, zero_le_one, fun f => by rw [norm_jet, Finset.sup_singleton, one_mul]; rfl⟩

variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)

include hG hI

theorem int_J (k j : ℕ) : Integrable (fun a => J k j (G a)) μ :=
  (hI k j).mono' ((J k j).continuous.comp hG).aestronglyMeasurable (.of_forall fun a => (norm_jet k j _).le)

omit hI in
theorem cont_D (j : ℕ) (x : V) : Continuous fun a => iteratedFDeriv ℝ j (G a) x := by
  have := (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp ((J 0 j).continuous.comp hG)
  refine this.congr fun a => ?_
  change jet 0 j (G a) x = _
  rw [jet_apply, pow_zero, one_smul]

omit hG hI in
theorem bd_D (f : SchwartzMap V ℂ) (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
  simpa using SchwartzMap.le_seminorm ℂ 0 j f x

theorem int_D (j : ℕ) (x : V) : Integrable (fun a => iteratedFDeriv ℝ j (G a) x) μ :=
  (hI 0 j).mono' (cont_D hG j x).aestronglyMeasurable (.of_forall fun a => bd_D _ j x)

theorem deriv_D (j : ℕ) (x : V) : HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ j (G a) y ∂μ)
    (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft x := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (s := Set.univ) (x₀ := x)
    (F := fun y a => iteratedFDeriv ℝ j (G a) y) (F' := fun y a => L (iteratedFDeriv ℝ (j + 1) (G a) y))
    (bound := fun a => SchwartzMap.seminorm ℂ 0 (j + 1) (G a)) univ_mem
    (.of_forall fun y => (cont_D hG j y).aestronglyMeasurable) (int_D hG hI j x)
    (L.continuous.comp (cont_D hG (j + 1) x)).aestronglyMeasurable
    (.of_forall fun a y _ => by rw [L.norm_map]; exact bd_D _ _ y) (hI 0 (j + 1))
    (.of_forall fun a y _ => ((cd (G a) (j + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j) y).hasFDerivAt)
  have e := L.toContinuousLinearEquiv.integral_comp_comm (μ := μ) fun a => iteratedFDeriv ℝ (j + 1) (G a) x
  exact h.congr_fderiv e

theorem taylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ :=
  ⟨fun x => ((continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.integral_comp_comm (μ := μ)
      fun a => iteratedFDeriv ℝ 0 (G a) x).symm,
    fun j _ x => deriv_D hG hI j x,
    fun j _ => continuous_iff_continuousAt.2 fun x => (deriv_D hG hI j x).continuousAt⟩

theorem eval_int (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by
  rw [← (taylor hG hI).eq_iteratedFDeriv (by exact_mod_cast le_top) x, ← integral_smul]
  exact ((BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm (int_J hG hI k j)).symm

theorem exists_int : ∃ f : SchwartzMap V ℂ, ∀ k j, J k j f = ∫ a, J k j (G a) ∂μ := by
  refine ⟨⟨fun x => ∫ a, G a x ∂μ, (taylor hG hI).contDiff, fun k j => ⟨‖∫ a, J k j (G a) ∂μ‖, fun x => ?_⟩⟩, fun k j => ?_⟩
  · have := (∫ a, J k j (G a) ∂μ).norm_coe_le_norm x
    rwa [eval_int hG hI, norm_smul, norm_pow, norm_norm] at this
  · ext1 x
    rw [eval_int hG hI]
    rfl

omit hG hI in
theorem factor (T : SchwartzMap V ℂ →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (T' : (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, T f = T' fun i => J i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  let j : SchwartzMap V ℂ →ₗ[ℂ] ∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ) := LinearMap.pi fun i => (J i.1.1 i.1.2).toLinearMap
  have hb : ∀ f, ‖T f‖ ≤ C * ‖j f‖ := fun f => by
    refine (h f).trans ?_
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_) C.2
    exact (norm_jet i.1 i.2 f).ge.trans (norm_le_pi_norm (j f) ⟨i, hi⟩)
  have hk : LinearMap.ker j ≤ LinearMap.ker T.toLinearMap := fun f hf => by
    have := hb f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let t : LinearMap.range j →ₗ[ℂ] ℂ := ((LinearMap.ker j).liftQ T.toLinearMap hk) ∘ₗ j.quotKerEquivRange.symm.toLinearMap
  have ht : ∀ f, t ⟨j f, f, rfl⟩ = T f := fun f => by
    simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [j.quotKerEquivRange_symm_apply_image f ⟨f, rfl⟩]
    rfl
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range j) (t.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [ht]
    exact hb f))
  exact ⟨s, g, fun f => ((hg ⟨j f, f, rfl⟩).trans (ht f)).symm⟩

end SchI

theorem schInt : SchInt := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT⟩ := SchI.factor T
  have hi : MeasureTheory.Integrable (fun a (i : s) => SchI.J i.1.1 i.1.2 (G a)) μ :=
    MeasureTheory.Integrable.of_eval fun i => SchI.int_J hG hI _ _
  simp only [hT]
  refine ⟨T'.integrable_comp hi, ?_⟩
  rw [T'.integral_comp_comm hi]
  congr 1
  funext i
  rw [hf]
  exact (ContinuousLinearMap.proj (R := ℂ) i).integral_comp_comm hi

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.IntegrableProdOfBound
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem integrable_prod_of_bound {G N : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] (μ : Measure G) [SFinite μ] (ν : Measure N) [IsFiniteMeasure ν]
    {f : G × N → ℂ} (hf : Continuous f) {K : ℝ} (hK : ∀ u, ∫⁻ g, ‖f (g, u)‖ₑ ∂μ ≤ ENNReal.ofReal K) : Integrable f (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hf.enorm.measurable.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono hK) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem ctFub_of (hU : UnipEx) (hT : ThetaBasic) (hG : GrpTop) (hE : EpsOf) : CTFub := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ ⟨C, k, hb⟩ c hc
  obtain ⟨⟨ν₀, 𝓕₀, a1, a2, a3⟩, ⟨Ω, hΩ, hcov⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH
  obtain ⟨b1, b2, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  obtain ⟨-, -, -, -, -, -, -, b3⟩ := hG F E σ hp.base.cm d W.J (hE F E σ B hp.base d W r' s' (Or.inr hp.skew)).1
  obtain ⟨t1, t2, -⟩ := (hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := hp.good.haar
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  have key : ∀ (ν : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), ν 𝓕 = 1 → ∀ h, SFinite (ν.restrict 𝓕) ∧
      Integrable (fun x : UA σ X.J × unip σ W H' => theta om Φ x.1 (x.2.1 * h)) ((M.μ.restrict M.dom).prod (ν.restrict 𝓕)) := by
    intro ν 𝓕 h1 h
    have hf : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
    have hcont : Continuous fun u : unip σ W H' => u.1 * h := continuous_subtype_val.mul continuous_const
    obtain ⟨D, hD⟩ := b3 _ (hΩ.image hcont)
    refine ⟨@instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite _), integrable_prod_of_bound _ _ (K := |C| * (D : ℝ) ^ k)
      (t1.comp (continuous_fst.prodMk (hcont.comp continuous_snd))) fun u => ?_⟩
    obtain ⟨γ, hγ, hu⟩ := hcov u
    have e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u).1 * h) := fun g => by
      rw [← t2 1 (one_mem _) γ.1 hγ g, one_mul, Subgroup.coe_mul, mul_assoc]
    simp only [e]
    refine (hb _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (ht ((γ * u).1 * h) : ℝ) ≤ D := hD _ ⟨_, hu, rfl⟩
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 k) (by positivity) (abs_nonneg C)
  refine ⟨fun h => ?_, fun ν 𝓕 c1 c2 c3 h => ?_⟩
  · obtain ⟨_, hi⟩ := key ν₀ 𝓕₀ a3 h
    simp only [fun g => hc g ν₀ 𝓕₀ a1 a2 a3 h]
    exact hi.integral_prod_left
  · obtain ⟨_, hi⟩ := key ν 𝓕 c3 h
    simp only [fun g => hc g ν 𝓕 c1 c2 c3 h]
    exact integral_integral_swap (f := fun (g : UA σ X.J) (u : unip σ W H') => theta om Φ g (u.1 * h)) hi

end PositivityTheory.ThKCT
end
end

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure Ext : Prop where
  mixW : MixW
  mixX : MixX
  basic : ThetaBasic
  evZero : EvZero
  evCone : EvCone
  stab : StabEx
  pair : PairEx
  plane : PlaneHerm
  top : GrpTop
  eps : EpsOf
  triple : TriplePair
  weil : WeilConv
  dom : DomWeil
  semi : SoSemi
  decay : SoDecay
  vol : FinVolU
  fin : SoFin

theorem thetaExp : ThetaExp := thetaExp_of slice_of

theorem evUniq : EvUniq := evUniq_of thetaExp

theorem Ext.kernel (h : Ext) : CTKernel :=
  ctKernel_of thetaExp evUniq slice_of evAdm_of h.mixW h.mixX h.basic h.pair low_of unipEx_of h.top h.eps

theorem Ext.fub (h : Ext) : CTFub := ctFub_of unipEx_of h.basic h.top h.eps

theorem Ext.mixAB (h : Ext) : MixAB := Ker.mixAB_of h.mixW h.mixX h.evZero h.pair thetaExp evUniq

theorem Ext.coneA (h : Ext) : ConeA :=
  coneA_of unfold_of unipEx_of stabDec_of h.basic h.top h.eps evAdm_of h.mixAB (lineInt_of slice_of schInt tateAbs) h.dom

theorem Ext.coneB (h : Ext) : ConeB :=
  coneB_of unfold_of unipEx_of stabDec_of h.basic h.top h.eps evAdm_of h.mixAB (lineInt_of slice_of schInt tateAbs) h.semi h.vol h.fin soStab_of
    (soEv_of linEx_of low_of)

theorem Ext.genAniso (h : Ext) : GenAniso := genAniso_of h.kernel h.fub h.mixW h.weil h.basic witt_of h.top h.eps

theorem Ext.genBig (h : Ext) : GenBig := genBig_of h.kernel h.fub h.coneA h.mixW h.weil h.basic witt_of h.top h.eps

theorem Ext.genSmall (h : Ext) : GenSmall :=
  genSmall_of h.kernel h.fub h.coneB (Ker.twoExp_of thetaExp) h.mixAB h.mixW h.evCone witt_of stabDec_of unipEx_of h.basic h.top h.eps
    h.decay h.vol h.fin soStab_of (soZeroA'_of linEx_of h.mixX thetaExp evUniq) (soEv_of linEx_of low_of)

theorem ct_all (h : Ext) : CTKernel ∧ SplitEx ∧ CTBigZero ∧ CTSmallZero ∧ CTBigCone ∧ CTSmallCone :=
  have k := kFinData_of h.stab
  have i := iwaEx_of h.stab
  ⟨h.kernel, splitEx_of h.genBig h.genSmall h.genAniso k h.stab i h.pair h.plane h.evCone h.evZero unipEx_of low_of h.triple,
    ctBigZero_of h.genBig h.genAniso k h.stab i h.pair h.plane h.evCone unipEx_of h.triple,
    ctSmallZero_of h.genAniso k h.stab h.triple, ctBigCone_of h.genBig k i h.pair h.evZero unipEx_of h.triple,
    ctSmallCone_of h.genSmall k i h.pair h.evZero unipEx_of h.triple⟩

end PositivityTheory.ThKCT

end
