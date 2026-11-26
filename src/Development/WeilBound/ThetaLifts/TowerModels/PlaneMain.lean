module

public import Development.WeilBound.ThetaLifts.TowerModels.ModelEx

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.PlanePair
section -- merged from Development.WeilBound.ThetaLifts.TowerModels.PlaneLat
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_partner (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D) (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (x : Fin n → E)
    (hxx : form σ J x x = 0) (z₀ : Fin n → E) (hz₀ : z₀ ∈ L) (hz₀x : form σ J z₀ x ≠ 0) :
    ∃ y, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hσε : σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have hεL : ∀ a ∈ L, ε • a ∈ L := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  let C₀ : Submodule (𝓞 E) E := L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))
  let C : FractionalIdeal (𝓞 E)⁰ E := ⟨C₀, FractionalIdeal.isFractional_of_fg (hfg.map _)⟩
  have hC : ∀ z ∈ L, form σ J z x ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hC0 : C ≠ 0 := fun e => hz₀x (by simpa [e] using hC z₀ hz₀)
  have hinv : C * C⁻¹ = 1 := mul_inv_cancel₀ hC0
  have key : ∀ t ∈ C * C⁻¹, ∃ y, form σ J y x = t ∧ ∀ c ∈ C, c • y ∈ L := fun t ht => by
    refine FractionalIdeal.mul_induction_on ht (fun a ha b hb => ?_) ?_
    · obtain ⟨z, hz, rfl⟩ := ha
      refine ⟨b • z, by rw [form_smul_left, mul_comm]; rfl, fun c hc => ?_⟩
      have := FractionalIdeal.mul_mem_mul hc hb
      rw [hinv, FractionalIdeal.mem_one_iff] at this
      obtain ⟨o, ho⟩ := this
      rw [smul_smul, ← ho, algebraMap_smul]
      exact L.smul_mem o hz
    · rintro _ _ ⟨y, rfl, hy⟩ ⟨y', rfl, hy'⟩
      exact ⟨y + y', form_add_left _ _ _ _, fun c hc => by rw [smul_add]; exact L.add_mem (hy c hc) (hy' c hc)⟩
  obtain ⟨y₁, hy₁, hy₁L⟩ := key 1 (by rw [hinv]; exact FractionalIdeal.one_mem_one _)
  obtain ⟨y₀, hy₀x, hy₀L⟩ : ∃ y₀, form σ J y₀ x = ε ∧ ∀ c ∈ C, c • y₀ ∈ L :=
    ⟨ε • y₁, by rw [form_smul_left, hy₁, mul_one], fun c hc => by rw [smul_comm]; exact hεL _ (hy₁L c hc)⟩
  have hxy₀ : form σ J x y₀ = 1 := by rw [sw, hy₀x, hσε, hεε]
  have crit : ∀ y, (∀ c ∈ C, c • y ∈ L) → ∀ z ∈ L, form σ J z y • x ∈ L := fun y hy z hz => by
    refine (hd _).2 fun z' hz' => ?_
    have := hεD _ ((hd z).1 hz _ (hy _ (hC z' hz')))
    rw [form_smul_right] at this
    rw [form_smul_left, sw z' x]
    convert this using 1
    ring
  set q := form σ J y₀ y₀ with hq
  have hqq : ε * σ q = q := (sw y₀ y₀).symm
  have hyL : ∀ c ∈ C, c • (y₀ - ((θ : E) * q) • x) ∈ L := fun c hc => by
    have := L.smul_mem θ (crit y₀ hy₀L _ (hy₀L c hc))
    rw [form_smul_left, ← algebraMap_smul E θ, smul_smul] at this
    rw [smul_sub, smul_smul]
    refine L.sub_mem (hy₀L c hc) ?_
    convert this using 2
    change _ = (θ : E) * _
    ring
  refine ⟨y₀ - ((θ : E) * q) • x, ?_, ?_, fun z hz => ⟨hyL _ (hC z hz), crit _ hyL z hz⟩⟩
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right, form_smul_right,
      hxx, hxy₀, hy₀x, ← hq, map_mul]
    linear_combination -q * hθ - σ θ * hqq
  · rw [form_sub_right, form_smul_right, hxx, hxy₀]; ring

theorem exists_max_val {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (L : Submodule (𝓞 E) V) (hfg : L.FG) (f : V →ₗ[E] E) (hf : ∃ z ∈ L, f z ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ z₀ ∈ L, f z₀ ≠ 0 ∧ ∀ w ∈ S, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f z₀) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
  · obtain ⟨z, hz, hz0⟩ := hf
    exact ⟨z, hz, hz0, by simp⟩
  have h1 : ∀ w : HeightOneSpectrum (𝓞 E), ∃ c ∈ L, ∀ z ∈ L, w.valuation E (f z) ≤ w.valuation E (f c) := fun w => by
    obtain ⟨G, rfl⟩ := hfg
    obtain ⟨c, hc, hmax⟩ := (insert 0 G).exists_max_image (fun z => w.valuation E (f z)) (by simp)
    refine ⟨c, ?_, fun z hz => ?_⟩
    · rcases Finset.mem_insert.1 hc with rfl | hc
      · exact zero_mem _
      · exact Submodule.subset_span hc
    · induction hz using Submodule.span_induction with
      | mem x hx => exact hmax x (Finset.mem_insert_of_mem hx)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
      | smul a x _ hx =>
        rw [← algebraMap_smul E a, map_smul, smul_eq_mul, map_mul]
        exact (mul_le_of_le_one_left' (w.valuation_le_one a)).trans hx
  choose c hcL hc using h1
  have hc0 : ∀ w : HeightOneSpectrum (𝓞 E), 0 < w.valuation E (f (c w)) := fun w => by
    obtain ⟨z, hz, hz0⟩ := hf
    exact lt_of_lt_of_le (zero_lt_iff.2 ((map_ne_zero _).2 hz0)) (hc w z hz)
  have h2 : ∀ w w' : HeightOneSpectrum (𝓞 E), ∃ p : 𝓞 E, p ∉ w.asIdeal ∧ (w' ≠ w → p ∈ w'.asIdeal) := fun w w' => by
    by_cases e : w' = w
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd e h⟩
    · have : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
        e (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
      obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 this
      exact ⟨p, hp', fun _ => hp⟩
  choose p hp hp' using h2
  let e : HeightOneSpectrum (𝓞 E) → 𝓞 E := fun w => ∏ w' ∈ S, p w w'
  have he : ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (algebraMap _ E (e w)) = 1 := fun w => by
    simp only [e, map_prod]
    exact Finset.prod_eq_one fun w' _ => (w.valuation_eq_one_iff_notMem (K := E)).2 (hp w w')
  have he' : ∀ w, ∀ w' ∈ S, w' ≠ w → w'.valuation E (algebraMap _ E (e w)) < 1 := fun w w' hw' hne =>
    (w'.valuation_lt_one_iff_mem (K := E) _).2 (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hw') (hp' w w' hne))
  have hval : ∀ w ∈ S, w.valuation E (f (∑ w' ∈ S, e w' • c w')) = w.valuation E (f (c w)) := fun w hw => by
    have t : ∀ w', f (e w' • c w') = algebraMap _ E (e w') * f (c w') := fun w' => by
      rw [← algebraMap_smul E (e w'), map_smul, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.add_sum_erase S _ hw, map_add (f := _), map_sum]
    have a1 : w.valuation E (f (e w • c w)) = w.valuation E (f (c w)) := by rw [t, map_mul, he, one_mul]
    rw [Valuation.map_add_eq_of_lt_left, a1]
    rw [a1]
    refine Valuation.map_sum_lt _ (hc0 w).ne' fun w' hw' => ?_
    rw [t, map_mul]
    calc _ ≤ w.valuation E (algebraMap _ E (e w')) * w.valuation E (f (c w)) := by
          gcongr; exact hc w _ (hcL w')
      _ < _ := mul_lt_of_lt_one_left (hc0 w) (he' w' w hw (Finset.ne_of_mem_erase hw').symm)
  refine ⟨∑ w' ∈ S, e w' • c w', L.sum_mem fun w _ => L.smul_mem _ (hcL w), fun h0 => ?_, fun w hw z hz => ?_⟩
  · have := hval w₀ hw₀
    rw [h0, map_zero] at this
    exact (hc0 w₀).ne this
  · rw [hval w hw]; exact hc w z hz

theorem exists_denom (C : Submodule (𝓞 E) E) (hfg : C.FG) (w : HeightOneSpectrum (𝓞 E))
    (hC : ∀ c ∈ C, w.valuation E c ≤ 1) : ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ ∀ c ∈ C, ∃ o : 𝓞 E, (d : E) * c = o := by
  classical
  obtain ⟨G, rfl⟩ := hfg
  have h1 : ∀ c : E, ∃ d : 𝓞 E, d ∉ w.asIdeal ∧ (w.valuation E c ≤ 1 → ∃ o : 𝓞 E, (d : E) * c = o) := fun c => by
    by_cases hc : w.valuation E c ≤ 1
    · obtain ⟨o, ⟨d, hd⟩, e⟩ := w.exists_primeCompl_mul_eq_of_integer c hc
      exact ⟨d, hd, fun _ => ⟨o, by rw [mul_comm]; exact e⟩⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, fun h => absurd h hc⟩
  choose d hd hd' using h1
  refine ⟨∏ c ∈ G, d c, fun hm => ?_, fun c hc => ?_⟩
  · obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hm
    exact hd c hc
  · induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨o, ho⟩ := hd' x (hC x (Submodule.subset_span hx))
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hx
      refine ⟨k * o, ?_⟩
      rw [hk]; push_cast; linear_combination (k : E) * ho
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by push_cast; rw [mul_add]; push_cast at ha hb; rw [ha, hb]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      refine ⟨a * b, ?_⟩
      change _ * ((a : E) * x) = (a : E) * (b : E)
      rw [← hb]
      ring

end PositivityTheory.ThKG.Tow.Pln

end
end

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_adapted_pair (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) {ε : E}
    (hε : ε = 1 ∨ ε = -1) (hJ : ∀ i j, σ (J j i) = ε * J i j) (D : Submodule (𝓞 E) E) (hD1 : (1 : E) ∈ D)
    (L : Submodule (𝓞 E) (Fin n → E)) (hlat : L.IsFullLattice E) (hd : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D)
    (θ : 𝓞 E) (hθ : (θ : E) + σ θ = 1) (P : Finset (Pl F)) (τ : ∀ v : P, E →ₐ[F] Fv F v)
    (hDτ : ∀ v, ∀ c ∈ D, Valued.v (τ v c) ≤ 1) (x₀ : Fin n → E) (hx₀ : x₀ ≠ 0) (hxx₀ : form σ J x₀ x₀ = 0) :
    ∃ x y : Fin n → E, form σ J x x = 0 ∧ form σ J y y = 0 ∧ form σ J x y = 1 ∧
      (∀ z ∈ L, form σ J z x • y ∈ L ∧ form σ J z y • x ∈ L) ∧
      ∀ v : P, ((∀ c : E, c • x ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ L → Valued.v (τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ v c) = 1) := by
  classical
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεv : ∀ v, Valued.v (τ v ε) = 1 := fun v => by rcases hε with rfl | rfl <;> simp
  have hεD : ∀ a ∈ D, ε * a ∈ D := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have sw : ∀ a b, form σ J b a = ε * σ (form σ J a b) := fun a b => by
    rw [form_swap h hJ, ← mul_assoc, hεε, one_mul]
  have hne : ∃ z ∈ L, formL (σ := σ) J x₀ z ≠ 0 := by
    by_contra H
    push Not at H
    have h0 : formL (σ := σ) J x₀ = 0 := LinearMap.ext_on hlat.span_eq_top fun z hz => H z hz
    have h1 : J *ᵥ (fun i => σ (x₀ i)) = 0 := by
      funext k
      have := LinearMap.congr_fun h0 (Pi.single k 1)
      simpa [formL, form] using this
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    exact hx₀ (funext fun i => by simpa using congrFun h2 i)
  let S : Finset (HeightOneSpectrum (𝓞 E)) :=
    Finset.univ.image (fun v : P => splitPrime (τ v)) ∪ Finset.univ.image (fun v : P => splitPrime ((τ v).comp σ))
  obtain ⟨z₀, hz₀, hc0, hmax⟩ := exists_max_val L hlat.fg (formL (σ := σ) J x₀) hne S
  change form σ J z₀ x₀ ≠ 0 at hc0
  set c₀ := form σ J z₀ x₀ with hc₀
  obtain ⟨x, hxx, hz₀x, hle⟩ : ∃ x, form σ J x x = 0 ∧ form σ J z₀ x = 1 ∧
      ∀ w ∈ S, ∀ z ∈ L, w.valuation E (form σ J z x) ≤ 1 := by
    refine ⟨σ c₀⁻¹ • x₀, by rw [form_smul_left, form_smul_right, hxx₀]; simp,
      by rw [form_smul_right, sigma_sigma h, inv_mul_cancel₀ hc0], fun w hw z hz => ?_⟩
    rw [form_smul_right, sigma_sigma h, map_mul, map_inv₀]
    exact inv_mul_le_one_of_le₀ (hmax w hw z hz) zero_le
  obtain ⟨y, hyy, hxy, hL⟩ := exists_partner h hε hJ D L hlat.fg hd θ hθ x hxx z₀ hz₀ (by rw [hz₀x]; exact one_ne_zero)
  have hyx : form σ J y x = ε := by rw [sw, hxy, map_one, mul_one]
  refine ⟨x, y, hxx, hyy, hxy, hL, fun v => ⟨⟨fun c hc => ?_, ?_⟩, fun c hc => ?_, 1, ?_, by simp⟩⟩
  · have := hεD _ ((hd _).1 hc z₀ hz₀)
    rw [form_smul_left, sw z₀ x, hz₀x, map_one, mul_one, mul_left_comm, hεε, mul_one] at this
    exact hDτ v c this
  · obtain ⟨d, hdw, hdC⟩ := exists_denom (L.map ((formL (σ := σ) J x).restrictScalars (𝓞 E))) (hlat.fg.map _)
      (splitPrime ((τ v).comp σ)) (by
        rintro _ ⟨z, hz, rfl⟩
        exact hle _ (by simp [S]) z hz)
    refine ⟨σ d, (hd _).2 fun z hz => ?_, ?_⟩
    · obtain ⟨o, ho⟩ := hdC _ ⟨z, hz, rfl⟩
      change (d : E) * form σ J z x = o at ho
      rw [form_smul_left, sw z x, mul_left_comm, ← map_mul, ho]
      refine hεD _ ?_
      have := D.smul_mem (conjInt σ o) hD1
      rwa [← algebraMap_smul E, smul_eq_mul, mul_one] at this
    · change Valued.v (((τ v).comp σ) d) = 1
      rw [valued_apply_eq_valuation]
      exact ((splitPrime ((τ v).comp σ)).valuation_eq_one_iff_notMem (K := E)).2 hdw
  · have := hle (splitPrime (τ v)) (by simp [S]) _ hc
    rwa [form_smul_left, hyx, ← valued_apply_eq_valuation, map_mul, map_mul, hεv, mul_one] at this
  · have := (hL z₀ hz₀).1
    rwa [hz₀x] at this

end PositivityTheory.ThKG.Tow.Pln

end
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.PlaneComp
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_compl (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (hn : n = n₁ + 2)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) (hyx : form σ J y x ≠ 0) :
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  let f : (Fin n → E) →ₗ[E] E × E := (formL (σ := σ) J x).prod (formL (σ := σ) J y)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨(a / form σ J y x) • y + b • x, Prod.ext ?_ ?_⟩
    · change form σ J _ x = a
      rw [form_add_left, form_smul_left, form_smul_left, hxx, div_mul_cancel₀ _ hyx, mul_zero, add_zero]
    · change form σ J _ y = b
      rw [form_add_left, form_smul_left, form_smul_left, hyy, hxy, mul_zero, mul_one, zero_add]
  have hk : Module.finrank E (LinearMap.ker f) = n₁ := by
    have := f.finrank_range_add_finrank_ker
    rw [hf, finrank_top] at this
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker f) hk
  let g : (Fin n₁ → E) →ₗ[E] (Fin n → E) := (LinearMap.ker f).subtype ∘ₗ b.equivFun.symm.toLinearMap
  obtain ⟨p, hp⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2
    ((LinearMap.ker f).injective_subtype.comp b.equivFun.symm.injective))
  refine ⟨LinearMap.toMatrix' g, LinearMap.toMatrix' p, by rw [← LinearMap.toMatrix'_comp, hp, LinearMap.toMatrix'_id],
    fun u => ?_, fun z h1 h2 => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    have := (b.equivFun.symm u).2
    exact Prod.mk_eq_zero.1 this
  · refine ⟨b.equivFun ⟨z, Prod.mk_eq_zero.2 ⟨h1, h2⟩⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    change z = (b.equivFun.symm (b.equivFun _) : LinearMap.ker f)
    rw [LinearEquiv.symm_apply_apply]

theorem fg_comap {V W : Type} [AddCommGroup V] [Module (𝓞 E) V] [AddCommGroup W] [Module (𝓞 E) W]
    (f : V →ₗ[𝓞 E] W) (hf : Function.Injective f) (L : Submodule (𝓞 E) W) (hL : L.FG) : (L.comap f).FG :=
  Submodule.fg_of_fg_map_injective f hf (hL.of_le (Submodule.map_comap_le f L))

theorem isLattice_comap (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * ι = 1) (hL : L.IsFullLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E :=
  Submodule.IsLattice.of_fg E (fg_comap _ (fun u u' e => by
    have := congrArg (P *ᵥ ·) (show ι *ᵥ u = ι *ᵥ u' from e)
    simpa [Matrix.mulVec_mulVec, hP] using this) L hL.fg)

theorem exists_ideal (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (x : Fin n → E) (hx : x ≠ 0) :
    ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L :=
  ⟨⟨L.comap ((LinearMap.toSpanSingleton E _ x).restrictScalars (𝓞 E)), FractionalIdeal.isFractional_of_fg
    (fg_comap _ (smul_left_injective E hx) L hL.fg)⟩, fun _ => Iff.rfl⟩

end PositivityTheory.ThKG.Tow.Pln

end
end

section -- merged from Development.WeilBound.ThetaLifts.TowerModels.PlaneBas
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {v : Pl F} (τ : E →ₐ[F] Fv F v)

theorem map_mem_splitLat {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) :
    (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, AddSubgroup.subset_closure ⟨1, one_mem _, z, hz, rfl⟩,
    funext fun i => by simp [splitVec, splitProj_tmul]⟩

theorem splitLat_le {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    (N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v)) (hN : ∀ z ∈ L, (fun i => τ (z i)) ∈ N) :
    splitLat τ L ≤ N := by
  rintro _ ⟨y, hy, rfl⟩
  refine latLoc_induction (p := fun y => splitVec τ y ∈ N) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · have := N.smul_mem ⟨a, ha⟩ (hN x hx)
    convert this using 1
    rfl
  · have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun _ => map_zero _
    rw [this]; exact zero_mem _
  · rw [splitVec_add]; exact add_mem hy hz
  · have : splitVec τ (-y) = -splitVec τ y := funext fun _ => map_neg _ _
    rw [this]; exact neg_mem hy

theorem map_mem_of_unit {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} {c : E} (hc : c • x ∈ L)
    (hv : Valued.v (τ c) = 1) {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    (a • fun i => τ (x i)) ∈ splitLat τ L := by
  have h0 : τ c ≠ 0 := fun e => by simp [e] at hv
  have h1 : a * (τ c)⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem ha (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one])
  have := (splitLat τ L).smul_mem ⟨_, h1⟩ (map_mem_splitLat τ hc)
  convert this using 1
  funext i
  change a * τ (x i) = a * (τ c)⁻¹ * τ (c * x i)
  rw [map_mul]
  field_simp

theorem exists_basis (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ) (hn : n = n₁ + 2) (h01 : i₀ < i₁) (h1n : i₁ < n) (hlat : L.IsFullLattice E)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y)
    (hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1)
    (hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1)
    (hβ₁ : IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁) :
    ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  classical
  have hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n := fun j => by
    have := j.2
    unfold skip; split_ifs <;> omega
  let f : Fin n₁ ⊕ Bool → Fin n := Sum.elim (fun j => ⟨skip i₀ i₁ j, hsk j⟩)
    fun b => cond b ⟨i₁, h1n⟩ ⟨i₀, h01.trans h1n⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [hn]⟩
    rintro (a | _ | _) (b | _ | _) e <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr, cond, Fin.mk.injEq, skip, Sum.inl.injEq, Fin.ext_iff] at e ⊢ <;>
      first | omega | (split_ifs at e <;> omega)
  let e := Equiv.ofBijective f hf
  let c : Fin n₁ ⊕ Bool → Fin n → Fv F v := Sum.elim (fun j r => (ι.map τ * β₁.1) r j)
    fun b => cond b (fun r => τ (y r)) fun r => τ (x r)
  let b : Matrix (Fin n) (Fin n) (Fv F v) := Matrix.of fun r i => c (e.symm i) r
  have hb : ∀ u : Fin n → Fv F v, b *ᵥ u = (u (e (.inr false)) • fun r => τ (x r)) +
      ι.map τ *ᵥ β₁.1 *ᵥ (fun j => u (e (.inl j))) + u (e (.inr true)) • fun r => τ (y r) := fun u => by
    funext r
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, b, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_bool, c, Sum.elim_inl, Sum.elim_inr, cond]
    ring
  have hmv : ∀ u : Fin n₁ → E, (fun i => τ ((ι *ᵥ u) i)) = ι.map τ *ᵥ fun j => τ (u j) := fun u =>
    funext fun i => RingHom.map_mulVec (τ : E →+* Fv F v) ι u i
  have hsurj : ∀ w ∈ splitLat τ L, ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w := by
    let N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v) :=
      { carrier := {w | ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w}
        zero_mem' := ⟨0, fun _ => zero_mem _, Matrix.mulVec_zero _⟩
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
          exact ⟨u + u', fun i => add_mem (hu i) (hu' i), Matrix.mulVec_add _ _ _⟩
        smul_mem' := by
          rintro a _ ⟨u, hu, rfl⟩
          exact ⟨(a : Fv F v) • u, fun i => mul_mem a.2 (hu i), Matrix.mulVec_smul _ _ _⟩ }
    refine fun w hw => splitLat_le τ N (fun z hz => ?_) hw
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hsplit z hz
    have hu' := hβ₁.mem_iff.1 (map_mem_splitLat τ (L := L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) hu)
    refine ⟨fun i => Sum.elim ((β₁⁻¹).1 *ᵥ fun j => τ (u j)) (fun b => cond b (τ t) (τ s)) (e.symm i), fun i => ?_, ?_⟩
    · beta_reduce
      rcases e.symm i with j | _ | _
      · exact hu' j
      · exact hx.1 s hs
      · exact hy.1 t ht
    · rw [hb]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, cond]
      rw [Matrix.mulVec_mulVec _ β₁.1, Units.mul_inv, Matrix.one_mulVec, ← hmv]
      funext r
      simp
  have hunit : IsUnit b := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    have h1 : ∀ z : Fin n → E, (fun i => τ (z i)) ∈ LinearMap.range b.mulVecLin := fun z => by
      have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hlat.span_eq_top]; trivial
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨u, -, hu⟩ := hsurj _ (map_mem_splitLat τ hz); exact ⟨u, hu⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem ha ha'
      | smul a z _ hz => simp only [Pi.smul_apply, smul_eq_mul, map_mul]; exact Submodule.smul_mem _ (τ a) hz
    intro w
    have : w = ∑ i, w i • fun k => τ ((Pi.single i 1 : Fin n → E) k) := by
      funext k
      simp [Pi.single_apply, apply_ite]
    rw [this]
    exact (Submodule.sum_mem (LinearMap.range b.mulVecLin) fun i _ => Submodule.smul_mem _ _ (h1 _))
  obtain ⟨β, hβ⟩ := hunit
  have col : ∀ k r, β.1 r (e k) = c k r := fun k r => by rw [hβ]; simp [b]
  refine ⟨β, fun i => ⟨fun hi r => ?_, fun hi r => ?_, fun j hi r => ?_⟩, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · rw [show i = e (.inr false) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inr true) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inl j) from Fin.ext hi, col]; rfl
  · rw [hβ, hb]
    obtain ⟨s, hs, hs'⟩ := hx.2
    obtain ⟨t, ht, ht'⟩ := hy.2
    refine add_mem (add_mem (map_mem_of_unit τ hs hs' (hu _)) ?_) (map_mem_of_unit τ ht ht' (hu _))
    refine splitLat_le τ ((splitLat τ L).comap ((ι.map τ).mulVecLin.restrictScalars (v.adicCompletionIntegers F)))
      (fun z hz => ?_) ((hβ₁ _).1 fun j => hu _)
    change ι.map τ *ᵥ (fun j => τ (z j)) ∈ splitLat τ L
    rw [← hmv]
    exact map_mem_splitLat τ hz
  · obtain ⟨u', hu', e'⟩ := hsurj _ hu
    rw [← hβ] at e'
    rw [← Matrix.mulVec_injective_iff_isUnit.2 β.isUnit e']
    exact hu'

end PositivityTheory.ThKG.Tow.Pln

end
end

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure IsEps (σ : E →ₐ[F] E) (B : Base F E) (ε : E) (κ : ℂ) (D : Submodule (𝓞 E) E) {n : ℕ} (X : Spc F E n)
    (r s : ℕ) : Prop where
  herm : ∀ i j, σ (X.J j i) = ε * X.J i j
  sig : ∀ w, HasSig (κ • X.J.map (B.emb w).1) r s
  lat : X.L.IsFullLattice E
  dual : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, form σ X.J y x ∈ D
  cartan : ∀ w, IsCartan (κ • X.J.map (B.emb w).1) (X.θ w)
  bas : ∀ v : B.P, IsSplitBasis (B.τ v) X.L (X.bas v)

private theorem full_of_self_dual {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (hcm : IsCMExt F E σ)
    {ε : E} (hεε : ε * ε = 1) (D : Submodule (𝓞 E) E)
    (hherm : ∀ i j, σ (J j i) = ε * J i j)
    (hlat : L.IsLattice E)
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, form σ J y x ∈ D) :
    L.IsFullLattice E := by
    let := hlat
    refine { span_eq_top := ?_ }
    let W := Submodule.span E (L : Set (Fin n → E))
    change W = ⊤
    by_contra hW
    let g : (Fin n → E) →ₗ[E] Module.Dual E W :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin Jᵀ)).domRestrict₂ W
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := fun i => σ (z i)
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      exact funext fun i => σ.injective ((congrFun hy i).trans (map_zero σ).symm)
    have horth (x : Fin n → E) (hx : x ∈ L) : form σ J y x = 0 := by
      have hz' : z ⬝ᵥ Jᵀ *ᵥ x = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have hzero : form σ J x y = 0 := by
        rw [Matrix.dotProduct_transpose_mulVec] at hz'
        simpa only [form, y, sigma_sigma hcm] using hz'
      have hs := form_swap hcm hherm x y
      rw [hzero, map_zero] at hs
      exact (mul_eq_zero.mp hs.symm).resolve_left (left_ne_zero_of_mul_eq_one hεε)
    have hline (a : E) : a • y ∈ L := (hdual _).2 fun x hx => by
      rw [form_smul_left, horth x hx, mul_zero]
      exact D.zero_mem
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict L hline
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hlat.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

theorem exists_plane {B : Base F E} (hB : B.IsGood σ) {ε : E} (hε : ε = 1 ∨ ε = -1) {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) (D : Submodule (𝓞 E) E) (hD1 : (1 : E) ∈ D)
    (hDτ : ∀ v : B.P, ∀ c ∈ D, Valued.v (B.τ v c) ≤ 1) (n n₁ : ℕ) (hn : n = n₁ + 2) (hn₁ : 1 ≤ n₁) (Y : Spc F E n)
    (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hY : IsEps σ B ε κ D Y r s) (i₀ i₁ : ℕ) (h01 : i₀ < i₁) (h1n : i₁ < n) :
    ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsEps σ B ε κ D (GlobalTheory.ThK.reS Y Y') r s ∧
      IsEps σ B ε κ D Y₁ (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  classical
  have hcm : IsCMExt F E σ := hB.cm
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul_eq_one hκ1
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεL : ∀ a ∈ Y.L, ε • a ∈ Y.L := fun a ha => by
    rcases hε with rfl | rfl
    · simpa using ha
    · simpa using ha
  have hdet : Y.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine det_ne_zero_of_hasSig (hY.sig w) ?_
    rw [Matrix.det_smul, show (Y.J.map (B.emb w).1).det = (B.emb w).1 Y.J.det from (RingHom.map_det _ _).symm, h0,
      map_zero, mul_zero]
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
    exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
  have hFull : Y.L.IsFullLattice E := hY.lat
  obtain ⟨x₀, hx₀, hx₀x₀⟩ := exists_isotropic hcm B.emb (by omega) hr hs hdet hε hY.herm hκ0 hκ hY.sig
  obtain ⟨x, y, hxx, hyy, hxy, hL, hP⟩ := exists_adapted_pair hcm hdet hε hY.herm D hD1 Y.L hFull hY.dual θ₀ hθ₀ B.P B.τ
    hDτ x₀ hx₀ hx₀x₀
  have hyx : form σ Y.J y x = ε := by
    have := form_swap hcm hY.herm x y
    rw [hxy, map_one] at this
    linear_combination -ε * this - form σ Y.J y x * hεε
  obtain ⟨ι, P, hPι, horth, hcomp⟩ := exists_compl (σ := σ) n n₁ Y.J x y hn hxx hyy hxy
    (by rw [hyx]; exact left_ne_zero_of_mul_eq_one hεε)
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ ι *ᵥ u ∈ Y.L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - (ε * form σ Y.J z x) • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]
        linear_combination -form σ Y.J z x * hεε) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    have ht : (ε * form σ Y.J z x) • y ∈ Y.L := by rw [mul_smul]; exact hεL _ (hL z hz).1
    refine ⟨_, _, u, (hL z hz).2, ht, ?_, ?_⟩
    · rw [← hu]; exact Y.L.sub_mem (Y.L.sub_mem hz (hL z hz).2) ht
    · rw [← hu]; abel
  set L₁ := Y.L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsLattice E := by
    apply Submodule.IsLattice.of_fg E
    apply Submodule.fg_of_fg_map_injective _ _ (hY.lat.fg.of_le (Submodule.map_comap_le _ _))
    intro u u' e
    have he := congrArg (P *ᵥ ·) (show ι *ᵥ u = ι *ᵥ u' from e)
    simpa [Matrix.mulVec_mulVec, hPι] using he
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := exists_ideal n Y.L hY.lat.toIsLattice x hx0
  set J₁ := ιᵀ * Y.J * ι.map σ with hJ₁
  have hform₁ : ∀ u u', form σ J₁ u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hreal : ∀ w, HasSig (κ • J₁.map (e w)) (r - 1) (s - 1) ∧ ∃ θ θ₁, IsCartan (κ • Y.J.map (e w)) θ ∧
      IsCartan (κ • J₁.map (e w)) θ₁ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ ∧
      (κ • fun i => e w (y i)) = (2 : ℂ) • θ *ᵥ fun i => e w (x i) := fun w => by
    have cg : (ι.map (e w))ᵀ * (κ • Y.J.map (e w)) * (ι.map (e w)).map star = κ • J₁.map (e w) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm]
    rw [← cg]
    refine real_plane _ _ _ _ (P.map (e w)) hn (map_herm hcm _ (hκ _) hY.herm) ?_ ?_ ?_ ?_ ?_ ?_ (hY.sig w)
    · rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hxx, map_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hyy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hxy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J ι x (fun u => (horth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J ι y (fun u => (horth u).2), smul_zero, smul_zero]
    · rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  choose hsig₁ θ θ₁ hθ hθ₁ hθι hθx using hreal
  have hherm₁ : ∀ i j, σ (J₁ j i) = ε * J₁ i j := by
    intro i j
    rw [← form_single (σ := σ) J₁ j i, ← form_single (σ := σ) J₁ i j, hform₁, hform₁,
      form_swap hcm hY.herm]
  have hdual₁ : ∀ u, u ∈ L₁ ↔ ∀ u' ∈ L₁, form σ J₁ u u' ∈ D := by
    intro u
    refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
    · rw [hform₁]; exact (hY.dual _).1 hu _ hu'
    · show ι *ᵥ u ∈ Y.L
      refine (hY.dual _).2 fun z hz => ?_
      obtain ⟨_, _, u', -, -, hu', hz'⟩ := hsplit z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
        (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
      exact H u' hu'
  haveI hfull₁ : L₁.IsFullLattice E := full_of_self_dual J₁ L₁ hcm hεε D hherm₁ hlat₁ hdual₁
  have hb₁ : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) L₁ β := fun v => exists_isSplitBasis (B.τ v) L₁ hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : Pl F, GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  choose β hβ using fun v : B.P => exists_basis (B.τ v) n n₁ Y.L x y ι (β₁ v) i₀ i₁ hn h01 h1n hFull hsplit
    (hP v).1 (hP v).2 (hβ₁ v)
  let bas : ∀ v : Pl F, GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y₁ : Spc F E n₁ := ⟨J₁, L₁, θ₁, bas₁⟩
  let Y' : Spc F E n := ⟨Y.J, Y.L, θ, bas⟩
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hY.lat, dual := hY.dual, cartan := hθ
            bas := fun v => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v]
              exact (hβ v).2 }
  · exact { herm := hherm₁
            sig := hsig₁
            lat := hfull₁
            dual := hdual₁
            cartan := hθ₁
            bas := fun v => by
              rw [show Y₁.bas v = β₁ v from hbas₁ v]
              exact hβ₁ v }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := rfl, low := fun u => Iff.rfl
            split := hsplit
            ideal := h𝔟
            cartan := fun w => ⟨hθι w, κ⁻¹ * 2, mul_ne_zero (inv_ne_zero hκ0) two_ne_zero, by
              rw [mul_smul]
              exact (eq_inv_smul_iff₀ hκ0).2 (hθx w)⟩
            bas := fun v i => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show Y₁.bas v = β₁ v from hbas₁ v]
              exact (hβ v).1 i }

theorem isHerm_iff {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} : X.IsHerm σ B r s ↔ IsEps σ B 1 1 (intE E) X r s :=
  ⟨fun h => ⟨by simpa using h.herm, by simpa using h.sig, h.lat, h.dual, by simpa using h.cartan, h.bas⟩,
    fun h => ⟨by simpa using h.herm, by simpa using h.sig, h.lat, h.dual, by simpa using h.cartan, h.bas⟩⟩

theorem isSkew_iff {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} :
    X.IsSkew σ B r s ↔ IsEps σ B (-1) Complex.I (codE E) X r s :=
  ⟨fun h => ⟨by simpa using h.skew, h.sig, h.lat, h.dual, h.cartan, h.bas⟩,
    fun h => ⟨by simpa using h.herm, h.sig, h.lat, h.dual, h.cartan, h.bas⟩⟩

end PositivityTheory.ThKG.Tow.Pln

end
