module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem mem_ideal_of_locally (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, app_resG] at this
  rw [← germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem appLE_mem_ideal_comap (J : X.IdealSheafData) (g : W ⟶ X) (V : X.affineOpens) (A : W.affineOpens)
    (h : A.1 ≤ g ⁻¹ᵁ V.1) {a : Γ(X, V.1)} (ha : a ∈ J.ideal V) :
    (g.appLE V.1 A.1 h).hom a ∈ (J.comap g).ideal A :=
  (comap_le_iff J g _).1 le_rfl V a ha A h

theorem exists_affine_pair (g : W ⟶ X) (U : X.Opens) (A : W.Opens) (y : W) (hy : y ∈ A) (hU : g y ∈ U) :
    ∃ (V : X.affineOpens) (B : W.affineOpens), V.1 ≤ U ∧ B.1 ≤ A ∧ B.1 ≤ g ⁻¹ᵁ V.1 ∧ y ∈ B.1 := by
  obtain ⟨_, ⟨V, hV', rfl⟩, hyV, hV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  obtain ⟨_, ⟨B, hB', rfl⟩, hyB, hB⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ A ⊓ g ⁻¹ᵁ V from ⟨hy, hyV⟩) (A ⊓ g ⁻¹ᵁ V).isOpen
  exact ⟨⟨V, hV'⟩, ⟨B, hB'⟩, hV, fun x hx => (hB hx).1, fun x hx => (hB hx).2, hyB⟩

theorem Generates.ideal_comap_top_le [IsAffine W] {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) (k : L.ι) (h : ⊤ ≤ g ⁻¹ᵁ L.U k) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤
      Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) := by
  set K : Ideal Γ(W, ⊤) := Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) with hK
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop K := by
    refine (comap_le_iff _ _ _).2 fun U a ha A hA => mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (U.1 ⊓ L.U k) A.1 y hy ⟨hA hy, h trivial⟩
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X (hV.trans inf_le_left) a ∈ J.ideal V :=
      J.ideal_le_comap_ideal (U := V) (V := U) (hV.trans inf_le_left) ha
    rw [hJ.2 k V (hV.trans inf_le_right)] at h1
    have h2 : resG W hB (resG W hA ((g.app U.1).hom a)) =
        (g.appLE V.1 B.1 hBV).hom (resG X (hV.trans inf_le_left) a) := by
      rw [appLE_resG, resG_resG]
      rfl
    rw [h2]
    rw [← Ideal.mem_comap]
    refine Ideal.span_le.2 ?_ h1
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, appLE_resG, ← resG_appLE g h le_top]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  refine (key _).trans ?_
  simp

theorem Generates.generatesAlong_comap {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) : GeneratesAlong (J.comap g) σ g := by
  refine ⟨by rw [← Scheme.Hom.preimage_iSup, hJ.1, Scheme.Hom.preimage_top], fun k A h => le_antisymm ?_ ?_⟩
  · intro s hs
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := appLE_mem_ideal_comap (J.comap g) A.1.ι A ⟨⊤, isAffineOpen_top _⟩ hA hs
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := hJ.ideal_comap_top_le (A.1.ι ≫ g) k (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.span _), Ideal.mem_comap, Ideal.map_span,
      ← Set.range_comp]
    convert h2 using 3
    funext j
    exact appLE_appLE _ _ h hA _
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (L.U k) A.1 y hy (h hy)
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X hV ((σ j).f k) ∈ J.ideal V := by
      rw [hJ.2 k V hV]
      exact Ideal.subset_span ⟨j, rfl⟩
    have h2 := appLE_mem_ideal_comap J g V B hBV h1
    rw [appLE_resG] at h2
    rwa [resG_appLE]

theorem generatesAlong_comap_of_generates (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (hJ : Generates J σ) : GeneratesAlong (J.comap g) σ g :=
  hJ.generatesAlong_comap g

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwistedStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted : ∀ (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X), Generates J σ → GeneratesAlong (J.comap g) σ g := by
  first | exact @GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | exact GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates | (intros; apply GlobalTheory.ProjBlowup.generatesAlong_comap_of_generates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.Cong

open GlobalTheory.LastSteps

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h : IsUnit (redP P (1 : E)) := by
    rw [GlobalTheory.TopStep.reduction_one₂]
    exact isUnit_one
  have h1 : h.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, GlobalTheory.TopStep.reduction_one₂, Units.val_one])
  unfold LocE.unitV
  rw [dite_eq_left h, h1, map_one, Units.val_one]

omit [StarRing E] in
theorem unitV_det_delta (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} {A : Fin t → Fin t → E}
    (hA : ∀ s s', A s s' = if s = s' then 1 else 0) : LocE.unitV χ (Matrix.det (Matrix.of fun s s' => A s s')) = 1 := by
  have : (Matrix.of fun s s' => A s s') = 1 := by
    ext s s'
    rw [Matrix.of_apply, hA, Matrix.one_apply]
  rw [this, Matrix.det_one, unitV_one]


omit [NumberField E] [StarRing E] in
theorem entB_id (q : ℕ) {k₀ c n : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) {p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) :
    LocE.entB q k₀ c n c n ex ex (LinearMap.id : HomE E (n + c) (n + c)) p p' = if p = p' then 1 else 0 := by
  have h1 : LocE.fIdx k₀ c n p < n + c := by
    unfold LocE.fIdx
    split_ifs <;> omega
  have h2 : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' ↔ p = p' := by
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    unfold LocE.fIdx at h
    split_ifs at h <;> omega
  unfold LocE.entB Loc.atN
  rw [dite_eq_left h1, LinearMap.id_apply]
  unfold Loc.eN
  by_cases h : p = p'
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (h2.1 h')), zero_mul]

variable (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

omit [StarRing E] in
theorem blocks_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i)
      (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => unitV_det_delta _ fun s s' => ?_
  have h1 : ∀ s : Fin t, r + i * t + s.1 < r + j * t := fun s => by
    have := Finset.mem_range.1 hi
    have := s.2
    nlinarith
  rw [hM _ _ (h1 s) (h1 s')]
  simp [Fin.ext_iff]

omit [StarRing E] in
theorem int_delta {N : ℕ} {M : ℕ → ℕ → E} (hM : ∀ p p', p < N → p' < N → M p p' = if p = p' then 1 else 0)
    (p p' : ℕ) (h : p < N) (h' : p' < N) : IntAt P (M p p') := by
  rw [hM _ _ h h']
  split_ifs
  · exact GlobalTheory.TopStep.intAt_one
  · exact GlobalTheory.TopStep.intAt_zero

omit [StarRing E] in
theorem lamGv_delta {r t j : ℕ} {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, GlobalTheory.TopStep.reduction_zero, AddChar.map_zero_eq_one]
  intro i hi
  have := Finset.mem_range.1 hi
  rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

omit [StarRing E] in
theorem lamGvS_delta {k₀ r t j : ℕ} (hk : k₀ ≤ r) {M : ℕ → ℕ → E}
    (hM : ∀ p p', p < r + j * t → p' < r + j * t → M p p' = if p = p' then 1 else 0) :
    LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  rw [blocks_delta χ hM, mul_one, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, GlobalTheory.TopStep.reduction_zero,
    AddChar.map_zero_eq_one]
  all_goals
    intro i hi
    have := Finset.mem_range.1 hi
    rw [hM _ _ (by omega) (by omega), if_neg (by omega)]

theorem lamQB_cong (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {y : HomE E (n + c) (n + c)}
    (hy : y ∈ homS (LocE.lamY P (qOf P) n c 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.lamQB ξ kj n (LinearMap.id + (qOf P : E) • y) = 1 := by
  unfold LocE.lamQB
  have hl : ∀ s : Fin (n - kj), kj + s.1 < n + c := fun s => by
    have := s.2
    omega
  have e : (fun s t : Fin (n - kj) => Loc.atN ((LinearMap.id + (qOf P : E) • y : HomE E (n + c) (n + c))
      (Loc.eN E (n + c) (kj + t.1))) (kj + s.1)) =
      fun s t : Fin (n - kj) => (if s = t then 1 else 0) + (qOf P : E) * y (Pi.single ⟨_, hl t⟩ 1) ⟨_, hl s⟩ := by
    funext s t
    unfold Loc.atN
    rw [dite_eq_left (hl s), eN_eq (hl t)]
    simp [Pi.single_apply, Fin.ext_iff]
  rw [e, unitV_congr ξ (redP_det_add_q (A := fun s t => if s = t then 1 else 0) (fun s t => ?_) fun s t => ?_),
    unitV_det_delta ξ fun _ _ => rfl, inv_one]
  · split_ifs
    · exact GlobalTheory.TopStep.intAt_one
    · exact GlobalTheory.TopStep.intAt_zero
  · simpa [LocE.scE] using mem_homS_sclLat.1 hy ⟨_, hl s⟩ ⟨_, hl t⟩

end Loc

theorem lamRow_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hj y hy
  have hN : R.N j + cOf R j = R.r + j * R.t := by
    unfold Ranks.N cOf Ranks.r
    rw [mul_add, mul_one]
    omega
  have hk : R.k ≤ R.N j := Nat.le_add_right _ _
  have hr : R.k ≤ R.r := by
    unfold Ranks.r
    omega
  unfold lamYat at hy
  unfold lamRow
  by_cases hP : P ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    have hZ := entB_int R.k (x := y) hy
    have hM : ∀ p p', p < R.r + j * R.t → p' < R.r + j * R.t →
        LocE.entB (qOf P) R.k (cOf R j) (R.N j) (cOf R j) (R.N j) (fun i => i + 1) (fun i => i + 1)
          (LinearMap.id : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) p p' = if p = p' then 1 else 0 :=
      fun p p' h h' => entB_id _ hk _ (hN ▸ h) (hN ▸ h')
    split_ifs
    · unfold LocE.lamGBS
      rw [entB_add_smul, lamGvS_congr _ _ (int_delta hM) hZ, lamGvS_delta _ _ hr hM]
    · unfold LocE.lamGB
      rw [entB_add_smul, lamGv_congr _ _ (int_delta hM) hZ, lamGv_delta _ _ hM]
  · rw [if_neg hP] at hy ⊢
    exact lamQB_cong _ _ _ _ hy

end GlobalTheory.Mem.Col2.IdxEx.Cong

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowType_one_add_prime_smul_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), j < R.m → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | exact GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong | (intros; apply GlobalTheory.Mem.Col2.IdxEx.Cong.lamRow_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinf
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf_of_density {p q : ℕ} (μ : Measure (UpqT p q)) (hμ : μ.IsHaarMeasure) (c : ℝ≥0∞)
    (h0 : c ≠ 0) (ht : c ≠ ⊤) (hc : OmegaDensity μ c) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  haveI : IsTopologicalGroup (UpqT p q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  have hm0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))
  have hmt : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hne0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hm0, ht⟩
  have hnet : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top hmt h0
  lift minfDensity (p + q) / c to ℝ≥0 using hnet with t htc
  refine ⟨t • μ, Measure.IsHaarMeasure.nnreal_smul μ (by exact_mod_cast hne0), ?_⟩
  have h := GlobalTheory.CompactDualUnique.omegaDensity_smul t hc
  rwa [htc, ENNReal.div_mul_cancel h0 ht] at h

theorem exists_isMinf_of_cd (h : Nonempty CDHaar) (p q : ℕ) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  obtain ⟨cd⟩ := h
  obtain ⟨c, h0, ht, hc, -⟩ := cd.trick p q
  exact exists_isMinf_of_density _ (cd.haar p q) c h0 ht hc

end GlobalTheory.MinfMeasure
end

open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd GlobalTheory.T.nonempty_compactDualHaar

end GlobalTheory.MinfMeasure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdLatGmap
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

noncomputable section

namespace GlobalTheory.Mem.Col2.ChiFacLaw

open GlobalTheory.PeriodTransport GlobalTheory.IdealTransport

theorem detId_image (D : D7) {n : ℕ} (L₀ L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (G G' : Matrix (Fin n) (Fin n) D.host.E) (hu : G * G' = 1)
    (h : ∀ x ∈ L, G.mulVec x ∈ L') (h' : ∀ x ∈ L', G'.mulVec x ∈ L) :
    TaylorLogMetric.detId D L₀ L' = Submodule.span (𝓞 D.host.E) {G.det} * TaylorLogMetric.detId D L₀ L := by
  unfold TaylorLogMetric.detId
  rw [Submodule.span_mul_span, Set.singleton_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨(G' * A).det, ⟨_, fun v hv => ?_, rfl⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec]
      exact h' _ (hA v hv)
    · show G.det * (G' * A).det = A.det
      rw [← Matrix.det_mul, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨G * A, fun v hv => ?_, (Matrix.det_mul _ _).symm⟩
    rw [← Matrix.mulVec_mulVec]
    exact h _ (hA v hv)

theorem norm_one_span (D : D7) (z : D.host.E) (hz : z * D.host.conj z = 1) :
    TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {z}) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← hst] at hz
  have key : ∀ w x : D.host.E, x ∈ Submodule.span (𝓞 D.host.E) {w} → star x ∈ Submodule.span (𝓞 D.host.E) {star w} := by
    intro w x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Submodule.mem_span_singleton.2 ⟨⟨star (r : D.host.E), r.2.map (starRingEnd D.host.E).toIntAlgHom⟩, ?_⟩
    exact (star_mul' (r : D.host.E) w).symm
  refine ⟨Submodule.span (𝓞 D.host.E) {star z}, fun x => ?_, ?_⟩
  · rw [← hst]
    exact ⟨fun h => by simpa using key _ _ h, fun h => by simpa using key _ _ h⟩
  · rw [Submodule.span_mul_span, Set.singleton_mul_singleton, hz, Submodule.one_eq_span]

theorem star_det_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    star ((LinearEquiv.det γ.1 : Eˣ) : E) * ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  set M : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) with hM
  have hd : ((LinearEquiv.det γ.1 : Eˣ) : E) = M.det := by
    rw [LinearEquiv.coe_det, hM, LinearMap.det_toMatrix']
  have hu : M.conjTranspose * M = 1 := by
    ext i j
    have h := γ.2 (Pi.single i 1) (Pi.single j 1)
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hM, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    refine h.trans ?_
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  rw [hd, ← Matrix.det_conjTranspose, ← Matrix.det_mul, hu, Matrix.det_one]

theorem matT_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n : ℕ}
    (x : HomE E n n) : matT e n n x = (e : E →+* E').mapMatrix (LinearMap.toMatrix' x) := rfl

variable {D : D7} {X : Fields} (s : Seam D X)

theorem detId_lat_gmap {n : ℕ} (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D L₀ (s.lat (gmap g N)) =
      Submodule.span (𝓞 D.host.E) {s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)} * TaylorLogMetric.detId D L₀ (s.lat N) := by
  have hd : s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) = (matT s.iE n n g.toLinearMap).det := by
    rw [matT_eq, ← RingHom.map_det, LinearMap.det_toMatrix', LinearEquiv.coe_det]
    rfl
  rw [hd]
  refine detId_image D L₀ _ _ _ (matT s.iE n n g.symm.toLinearMap) ?_
    ((matT_carries s.iE N (gmap g N) _).2 fun y hy => ⟨y, hy, rfl⟩) ((matT_carries s.iE (gmap g N) N _).2 ?_)
  · rw [matT_eq, matT_eq, ← map_mul, ← LinearMap.toMatrix'_comp]
    simp
  · rintro _ ⟨y, hy, rfl⟩
    simpa using hy

theorem chi_lat_gmap (hs : s.Ok) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {n : ℕ} (γ : UF X.E n)
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat (gmap γ.1 N))) =
      (∏ τ, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h1 : star (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) * s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 := by
    rw [hst, ← hs.2, ← map_mul, star_det_mul, map_one]
  let z : unitary D.host.E := ⟨s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E), h1, by rw [mul_comm]; exact h1⟩
  have hL := sd_lat s hs hN
  rw [detId_lat_gmap, hχ.1 _ _ (norm_one_span D z.1 (by rw [← hst, mul_comm]; exact h1))
    (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (GlobalTheory.ThetaMove.Moved.sd_stdL D n) hL hL).1, hχ.2 z,
    Finset.prod_inv_distrib, ← s.iT.prod_comp]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (hs.1 τ _).symm

theorem chiLaw_ambOf : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → TaylorLogMetric.IsChi D χ → (ambOf s B χ cD).ChiLaw a b := by
  intro D X s cc δ B χ cD a b hs hχ γ γ' N N' hN hN'
  change Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) =
    (∏ τ, X.embC s.σ₀ τ _) ^ _ * (∏ τ, X.embC s.σ₀ τ _) ^ _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  unfold Base.chiFac
  rw [chi_lat_gmap s hs hχ γ hN, chi_lat_gmap s hs hχ γ' hN', mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg]
  ring

end GlobalTheory.Mem.Col2.ChiFacLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApplyEqOfNormal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.RayMono

theorem exists_apply_eq_of_normal {K A Ω : Type} [Field K] [Field A] [Field Ω] [Algebra K A] [Algebra K Ω]
    [Normal K A] (i j : A →ₐ[K] Ω) (x : A) : ∃ y, j y = i x := by
  let _ := j.toRingHom.toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨i.restrictNormal A x, i.restrictNormal_commutes A x⟩

theorem le_of_isRayFieldIn_of_dvd : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (𝔪 𝔪' : Ideal (𝓞 E))
    (M M' : IntermediateField ℚ ℂ), 𝔪' ≠ ⊥ → 𝔪 ∣ 𝔪' → IsRayFieldIn φ 𝔪 M → IsRayFieldIn φ 𝔪' M' → M ≤ M' := by
  rintro E _ _ φ 𝔪 𝔪' M M' hn hd ⟨h, _, hM⟩ ⟨h', _, hM'⟩ z hz
  let _ := algOf φ M h
  let _ := algOf φ M' h'
  let _ := φ.toAlgebra
  have := hM.1
  have := hM'.1
  obtain ⟨f⟩ := nonempty_algHom_of_isRay_of_dvd hn hd hM'.2 hM.2
  let i : M →ₐ[E] ℂ := { M.val.toRingHom with commutes' := fun _ => rfl }
  let i' : M' →ₐ[E] ℂ := { M'.val.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := exists_apply_eq_of_normal i (i'.comp f) ⟨z, hz⟩
  have hy' : ((f y : M') : ℂ) = z := hy
  exact hy' ▸ (f y).2

end GlobalTheory.Mem.RayMono
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxEx

theorem jat_le_stab_lamY {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ)
    (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Pr.vGs) (g : AutY X R j) (hg : g ∈ Jat (Pr := Pr) sharp j P) :
    g ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) := by
  unfold Jat at hg
  rw [if_pos hP] at hg
  unfold lamYat
  rw [if_pos hP]
  split_ifs at hg
  · exact hg.1
  · exact hg.1

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  intro X Pr R sharp j P hP h hh g hg
  obtain ⟨r, ⟨-, hr⟩, hrg⟩ := hg
  have e : (MulAut.conj h⁻¹).toMonoidHom r = h⁻¹ * r * h := by simp
  have hr' : (MulAut.conj h⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) sharp j P := hr
  rw [e] at hr'
  have h1 := jat_le_stab_lamY sharp j P hP _ hr'
  have h2 := mul_mem (mul_mem hh h1) (inv_mem hh)
  have e2 : h * (h⁻¹ * r * h) * h⁻¹ = r := by group
  rw [e2] at h2
  unfold lamYat at h2
  rw [if_pos hP] at h2
  have key : ∀ x : Sp X.E (R.N j), Loc.inX X.E (R.N j) (cOf R j) x ∈
      LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) ↔ x ∈ stdAt X.E (R.N j) P := fun x =>
    ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
      GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩
  intro x
  have h3 := h2 (Loc.inX X.E (R.N j) (cOf R j) x)
  rw [hrg x] at h3
  exact (key _).symm.trans (h3.trans (key _))

end GlobalTheory.Mem.Col2.IdxEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projConjLevel_le_integralGL_at_typePrime : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | exact GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint | (intros; apply GlobalTheory.Mem.Col2.IdxEx.prCat_le_GLint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetPosFinite
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolUnique

theorem haar_eq_of_eq_on_set {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] (S : Set G) (h : μ S = μ' S)
    (h0 : μ' S ≠ 0) (ht : μ' S ≠ ⊤) : μ = μ' := by
  have hμ := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hc : ((Measure.haarScalarFactor μ μ' : NNReal) : ENNReal) = 1 := by
    have h1 : μ S = (Measure.haarScalarFactor μ μ' : ENNReal) * μ' S := by
      conv_lhs => rw [hμ]
      simp
    rw [h] at h1
    exact ((ENNReal.mul_left_inj h0 ht).1 (by rw [one_mul]; exact h1)).symm
  have hc' : Measure.haarScalarFactor μ μ' = 1 := by exact_mod_cast hc
  rw [hμ, hc', one_smul]

theorem exists_set_pos_finite (cd : CDHaar) (P Q : ℕ) :
    ∃ B : Set (UpqT P Q), MeasurableSet B ∧ cd.cd P Q B ≠ 0 ∧ cd.cd P Q B ≠ ⊤ := by
  obtain ⟨_, _, _, _, _, _⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI := cd.haar P Q
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : UpqT P Q)
  exact ⟨K, hK.measurableSet, (Measure.measure_pos_of_mem_nhds _ hK1).ne', hK.measure_lt_top.ne⟩

theorem volMeas_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∀ μ μ', IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ → IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ' → μ = μ' := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W _ _ μ μ' hμ hμ'
  obtain ⟨hH, ⟨θ, hθ⟩, hall⟩ := hμ
  obtain ⟨hH', -, hall'⟩ := hμ'
  obtain ⟨⟨A, hA⟩, hB⟩ := hall θ hθ
  have hB' := (hall' θ hθ).2 A hA
  have hB := hB A hA
  choose B hBm hB0 hBt using fun ρ : I => exists_set_pos_finite cd (W.sig (τ ρ)).1 (W.sig (τ ρ)).2
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E cm.sig W.rank W.gram
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) cm.sig W.gram) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) cm.sig W.gram))
  haveI : BorelSpace (HA (AF F) cm.sig W.gram) := ⟨rfl⟩
  refine haar_eq_of_eq_on_set μ μ' _ ((hB B hBm).trans (hB' B hBm).symm) ?_ ?_
  · rw [hB' B hBm]
    exact Finset.prod_ne_zero_iff.2 fun ρ _ => hB0 ρ
  · rw [hB' B hBm]
    exact ENNReal.prod_ne_top fun ρ _ => hBt ρ

end GlobalTheory.Mem.VolUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardFilterLeLogClassNumber
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem prod_orderOf_le_card_of_indep {G ι : Type} [CommGroup G] [Fintype G] [Fintype ι] (x : ι → G)
    (hx : ∀ a : ι → ℤ, ∏ i, x i ^ a i = 1 → ∀ i, x i ^ a i = 1) : ∏ i, orderOf (x i) ≤ Fintype.card G := by
  classical
  have hinj : Function.Injective (fun a : (∀ i, Fin (orderOf (x i))) => ∏ i, x i ^ (a i : ℕ)) := by
    intro a a' h
    have h1 := hx (fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ)) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 h)
    funext i
    have h2 := h1 i
    rw [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at h2
    exact Fin.ext (pow_injOn_Iio_orderOf (a i).2 (a' i).2 h2)
  simpa using Fintype.card_le_of_injective _ hinj

theorem card_filter_le_log_classNumber {E : Type} [Field E] [NumberField E] (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis E) :
    (Finset.univ.filter fun i => b.h i ≠ 1).card ≤ Nat.log 2 (classNumber E) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
  refine le_trans ?_ h1
  rw [← Finset.prod_filter_ne_one]
  refine Finset.pow_card_le_prod _ _ _ fun i hi => ?_
  have h2 := (Finset.mem_filter.1 hi).2
  have h3 := b.h_pos i
  omega

theorem exists_kPsiField_generators (R : Ranks) (H : Host R) (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis H.E) (p q : ℕ) :
    ∃ S : Finset ℂ, S.card ≤ Nat.log 2 (classNumber H.E) ∧
      (∀ y ∈ S, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber H.E ∧ y ^ n ∈ imField H.φ₀) ∧
      kPsiField H b p q = imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔ IntermediateField.adjoin ℚ (S : Set ℂ) := by
  classical
  choose ψ hψ using fun i : Fin b.k =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (typeNorm H p q (b.γ i : H.E))) (b.h_pos i)
  refine ⟨(Finset.univ.filter fun i => b.h i ≠ 1).image ψ,
    Finset.card_image_le.trans (card_filter_le_log_classNumber b), fun y hy => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨b.h i, b.h_pos i, orderOf_dvd_card, _, (hψ i).symm⟩
  · rw [kPsiField_eq H b p q ψ hψ]
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      by_cases h : b.h i = 1
      · have h1 : ψ i ∈ imField H.φ₀ := ⟨_, by have := hψ i; rw [h, pow_one] at this; exact this.symm⟩
        exact (le_sup_left.trans le_sup_left : imField H.φ₀ ≤ _) h1
      · exact (le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _
          (Finset.mem_coe.2 (Finset.mem_image_of_mem ψ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))))
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨i, rfl⟩

end GlobalTheory.Mem.Fld
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInIffDifferentIdealEqTop
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.NT

namespace GlobalTheory.UnramDiscr

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem not_dvd_iff_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) ↔ P.inertia (L ≃ₐ[K] L) = ⊥ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  rw [not_dvd_differentIdeal_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P,
    Subgroup.card_eq_one]

theorem unramIn_iff_differentIdeal_eq_top :
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔ differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  let _ : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  unfold UnramIn InInertia
  constructor
  · intro h
    by_contra hD
    obtain ⟨M, hM, hDM⟩ := Ideal.exists_le_maximal _ hD
    haveI := hM
    have hMb : M ≠ ⊥ := by
      rintro rfl
      exact hD0 (le_bot_iff.mp hDM)
    have hMu : M.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hMb
    have hb : M.inertia (L ≃ₐ[K] L) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      exact h ⟨M.under (𝓞 K), inferInstance, hMu⟩ σ ⟨M, inferInstance, ⟨rfl⟩, fun x => hσ x⟩
    exact (not_dvd_iff_inertia K L M hMb).mpr hb (Ideal.dvd_iff_le.mpr hDM)
  · rintro hD 𝔭 σ ⟨P, hP, hPo, hσ⟩
    haveI := hP
    haveI := hPo
    have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
    have hnd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
      rw [hD]
      exact fun hd => hP.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hd))
    have hb := (not_dvd_iff_inertia K L P hPb).mp hnd
    have hmem : σ ∈ P.inertia (L ≃ₐ[K] L) := fun x => hσ x
    rw [hb] at hmem
    exact Subgroup.mem_bot.mp hmem


omit K L in
theorem unramIn_iff_natAbs_discr :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn L 𝔭) ↔
        (discr L).natAbs = (discr K).natAbs ^ Module.finrank K L := by
  intro K L _ _ _ _ _ _
  rw [unramIn_iff_differentIdeal_eq_top K L,
    natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  have h0 : 0 < (discr K).natAbs ^ Module.finrank K L :=
    pow_pos (Int.natAbs_pos.mpr (discr_ne_zero K)) _
  constructor
  · intro h
    rw [h, Ideal.absNorm_top, one_mul]
  · intro h
    apply Ideal.absNorm_eq_one_iff.mp
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [h, one_mul]

end GlobalTheory.UnramDiscr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSections
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSections
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ProjSpace GlobalTheory.Cartier

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

theorem exists_unit_appLE_sec (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (k l : L.ι) {T : W.Opens}
    (hk : T ≤ g ⁻¹ᵁ L.U k) (hl : T ≤ g ⁻¹ᵁ L.U l) : ∃ u : Γ(W, T)ˣ, ∀ j,
      (g.appLE (L.U k) T hk).hom ((σ j).f k) = u * (g.appLE (L.U l) T hl).hom ((σ j).f l) := by
  have hT : T ≤ g ⁻¹ᵁ (L.U k ⊓ L.U l) := le_inf hk hl
  refine ⟨Units.map (g.appLE (L.U k ⊓ L.U l) T hT).hom.toMonoidHom (L.g k l), fun j => ?_⟩
  have := congrArg (g.appLE (L.U k ⊓ L.U l) T hT).hom
    (sec_compat (σ j) k l (inf_le_left : L.U k ⊓ L.U l ≤ _) inf_le_right)
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  exact this

theorem exists_quot_of_span_eq {B : Type} [CommRing B] {ι : Type} [Fintype ι] {f : B} (hf : f ∈ nonZeroDivisors B)
    {s : ι → B} (h : Ideal.span {f} = Ideal.span (Set.range s)) :
    ∃ a c : ι → B, (∀ j, s j = a j * f) ∧ ∑ j, c j * a j = 1 := by
  have h1 : ∀ j, ∃ a, a * f = s j := fun j =>
    Ideal.mem_span_singleton'.1 (h ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha using h1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (h ▸ Ideal.mem_span_singleton_self f)
  refine ⟨a, c, fun j => (ha j).symm, (mul_cancel_right_mem_nonZeroDivisors hf).1 ?_⟩
  rw [one_mul, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc
  rw [mul_assoc, ha]

theorem exists_mem_basicOpen_of_sum {A : W.Opens} {a c : Fin (m + 1) → Γ(W, A)} (h : ∑ j, c j * a j = 1)
    {y : W} (hy : y ∈ A) : ∃ j, y ∈ W.basicOpen (a j) := by
  by_contra hne
  have h1 : (W.presheaf.germ A y hy).hom (∑ j, c j * a j) ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ fun hu => hne ⟨j, (W.mem_basicOpen _ y hy).2 hu⟩
  rw [h, map_one] at h1
  exact h1 isUnit_one

theorem exists_proportional (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R) (hσ : GeneratesAlong I σ g) (hI : FinalTheorems.EffCartier I) :
    ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  obtain ⟨D, rfl⟩ := EffCartierData.exists_idealSheaf_eq hI
  have loc : ∀ y : W, ∃ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : D.ι) (hi : A ≤ D.U i)
      (a c : Fin (m + 1) → Γ(W, A)), y ∈ A ∧
      (∀ j, (g.appLE (L.U k) A hk).hom ((σ j).f k) = a j * resG W hi (D.f i)) ∧ ∑ j, c j * a j = 1 := by
    intro y
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hσ.1.ge (Set.mem_univ y))
    obtain ⟨i, hi⟩ := D.exists_mem y
    obtain ⟨A, hy, hA⟩ := EffCartierData.exists_affine_le (V := g ⁻¹ᵁ L.U k ⊓ D.U i) (x := y) ⟨hk, hi⟩
    obtain ⟨a, c, h⟩ := exists_quot_of_span_eq (D.regular i _ (hA.trans inf_le_right))
      ((D.ideal_idealSheaf A i (hA.trans inf_le_right)).symm.trans (hσ.2 k A (hA.trans inf_le_left)))
    exact ⟨A.1, k, _, i, _, a, c, hy, h⟩
  choose A k hk i hi a c hy ha hc using loc
  have ha' : ∀ y {T : W.Opens} (hT : T ≤ A y) j, (g.appLE (L.U (k y)) T (hT.trans (hk y))).hom ((σ j).f (k y)) =
      resG W hT (a y j) * resG W (hT.trans (hi y)) (D.f (i y)) := fun y T hT j => by
    have := congrArg (resG W hT) (ha y j)
    rwa [map_mul, resG_appLE, resG_resG] at this
  have tr : ∀ y z, ∃ u : Γ(W, A y ⊓ A z)ˣ, ∀ j,
      resG W (inf_le_left : A y ⊓ A z ≤ A y) (a y j) =
        (u : Γ(W, A y ⊓ A z)) * resG W (inf_le_right : A y ⊓ A z ≤ A z) (a z j) := fun y z => by
    obtain ⟨u, hu⟩ := exists_unit_appLE_sec σ g (k y) (k z) (T := A y ⊓ A z)
      (inf_le_left.trans (hk y)) (inf_le_right.trans (hk z))
    have hy' : A y ⊓ A z ≤ D.U (i y) := inf_le_left.trans (hi y)
    have hz' : A y ⊓ A z ≤ D.U (i z) := inf_le_right.trans (hi z)
    refine ⟨u * Units.map (resG W (le_inf hz' hy')).toMonoidHom (D.trans (i z) (i y)), fun j => ?_⟩
    refine ((D.regular (i y)).resG hy').mul_right_cancel ?_
    have e := hu j
    rw [ha' y inf_le_left, ha' z inf_le_right, D.trans_spec_on (i z) (i y) hz' hy'] at e
    rw [e]
    change _ = (u : Γ(W, A y ⊓ A z)) * resG W (le_inf hz' hy') (D.trans (i z) (i y)) * _ * _
    ring
  choose u hu using tr
  let B : LB W := { ι := W, U := A, g := u }
  let t : Fin (m + 1) → B.Sec := fun j => { f := fun y => a y j, compat := fun y z => hu y z j }
  have ht : ⨆ j, Out.nonzeroLocus (t j) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := exists_mem_basicOpen_of_sum (hc y) (hy y)
    exact Opens.mem_iSup.2 ⟨j, (mem_nonzeroLocus_iff (t j) y (hy y)).2 hj⟩
  refine ⟨toProj q t ht, toProj_str q t ht, fun V l hl p hp j => ext_germ fun y hyV => ?_⟩
  have hm : y ∈ V ⊓ A y := ⟨hyV, hy y⟩
  have key : resG W (inf_le_left : V ⊓ A y ≤ V) ((g.appLE (L.U l) V hl).hom ((σ j).f l)) =
      resG W inf_le_left (pullRatio (toProj q t ht) V p hp j * (g.appLE (L.U l) V hl).hom ((σ p).f l)) := by
    obtain ⟨v, hv⟩ := exists_unit_appLE_sec σ g l (k y) (T := V ⊓ A y)
      (inf_le_left.trans hl) (inf_le_right.trans (hk y))
    have e : resG W inf_le_right (a y j) = _ * resG W inf_le_right (a y p) :=
      sec_eq_pullRatio_toProj_mul q t ht p j y (W := V ⊓ A y) (inf_le_left.trans hp) inf_le_right
    rw [map_mul, resG_appLE, resG_appLE, resG_pullRatio, hv, hv, ha' y inf_le_right, ha' y inf_le_right, e]
    ring
  have := congrArg (W.presheaf.germ _ y hm).hom key
  rwa [germ_resG, germ_resG] at this

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSectionsStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proj_map_proportional_sections : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R), GeneratesAlong I σ g → FinalTheorems.EffCartier I → ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  first | exact @GlobalTheory.ProjBlowup.exists_proportional | exact GlobalTheory.ProjBlowup.exists_proportional | (intros; apply GlobalTheory.ProjBlowup.exists_proportional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingCharArgMulLeftUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingCharArgMulLeftUnipotent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent

theorem chArg_left : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  intro F _ n' c' n c hc hc' r hr xj t
  obtain ⟨-, -, h3⟩ := (GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic F n' c' n c hc hc' xj (Loc.xx1 xj t)).1 ⟨t, rfl⟩
  generalize Loc.xx1 xj t = x at h3
  have e : Loc.n1Arg r = ∑ i ∈ Finset.range c, Loc.atN (r (Loc.eN F (n + c) (n + (i + 1)))) (n + i) := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    rw [Finset.sum_range_succ, GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_zero (F := F) (N := n + (d + 1)) (i := n + (d + 1)) (by omega),
      map_zero]
    have z : Loc.atN (0 : Fin (n + (d + 1)) → F) (n + d) = 0 := by
      unfold Loc.atN
      split_ifs <;> rfl
    rw [z, add_zero]
    rfl
  rw [e]
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have b3 := atN_of_R1cond hr.1 (h3 (i + 1))
  have b4 : Loc.atN (Loc.eN F (n + c) (n + (i + 1))) (n + i) = 0 := GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.atN_eN_succ _ _
  simp only [map_sub, atN_sub, b4] at b3
  change Loc.atN (r (x (Loc.eN F (n' + c') (n' + (i + 1))))) (n + i) =
    Loc.atN (x (Loc.eN F (n' + c') (n' + (i + 1)))) (n + i) + _
  linear_combination b3

end GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingCharArgMulLeftUnipotentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingCharArg_mul_left_unipotent : ∀ (F : Type) [Field F] (n' c' n c : ℕ), 1 ≤ c → c' = c + 1 → ∀ r ∈ Loc.R1 F n c, ∀ (xj : (Fin n' → F) →ₗ[F] (Fin n → F)) (t : Loc.FC n' c' n c → F), Loc.chArg (r.toLinearMap ∘ₗ Loc.xx1 xj t) = Loc.chArg (Loc.xx1 xj t) + Loc.n1Arg r := by
  first | exact @GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | exact GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left | (intros; apply GlobalTheory.Proof.unfoldingCharArg_mul_left_unipotent.chArg_left <;> assumption)
end
end
