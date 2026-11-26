module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantOfRightInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientTranslation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOfBounded
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSplit
open PositivityTheory.Rg.BcB.G8

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarProd

theorem haarSplit : HaarSplit := by
  intro G A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ α _ e
  have : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let β₀ : Measure B := Measure.haar
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map e) (α.prod β₀)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) (α.prod β₀)
  refine ⟨Measure.haarScalarFactor (μ.map e) (α.prod β₀) • β₀, ?_, ?_⟩
  · exact Measure.IsHaarMeasure.nnreal_smul _ hpos.ne'
  · rw [Measure.prod_smul_right]
    exact hc

end GlobalTheory.CompanionTheory.HaarProd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.CompIsoProof

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R →+* S) (hf : Continuous f) (a : ℕ) :
    Continuous (GeneralLinearGroup.map f : GL (Fin a) R →* GL (Fin a) S) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) (a : ℕ) :
    Continuous (cornerGL a s) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

variable {E : Type} [Field E] {a : ℕ}

def glOf (y : InfinitePlace E → GL (Fin a) ℂ) : GL (Fin a) (Cinf E) where
  val := Matrix.of fun i j v => (y v).val i j
  inv := Matrix.of fun i j v => (y v).inv i j
  val_inv := by
    ext i j v
    have h := congrFun (congrFun (y v).val_inv i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h
  inv_val := by
    ext i j v
    have h := congrFun (congrFun (y v).inv_val i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h

theorem map_eval_glOf (y : InfinitePlace E → GL (Fin a) ℂ) (v : InfinitePlace E) :
    GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (glOf y) = y v := by
  ext i j
  rfl

theorem continuous_glOf : Continuous (glOf : (InfinitePlace E → GL (Fin a) ℂ) → GL (Fin a) (Cinf E)) := by
  have h2 : Continuous fun x : GL (Fin a) ℂ => ((x⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) :=
    (Units.continuous_iff.1 (continuous_id (X := GL (Fin a) ℂ))).2
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => continuous_pi fun v => ?_,
    continuous_matrix fun i j => continuous_pi fun v => ?_⟩
  · exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply v)
  · exact (h2.matrix_elem i j).comp (continuous_apply v)

variable [NumberField E]

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

variable [_root_.NumberField.IsTotallyComplex E]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coordinate (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (continuous_apply v).comp continuous_pInf

theorem map_cV (v : InfinitePlace E) (g : GA E a) :
    GeneralLinearGroup.map (cV v) g =
      GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (GeneralLinearGroup.map (pInf E) g) := by
  ext i j
  rfl

def parts (g : GA E a) : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E) :=
  (fun v => GeneralLinearGroup.map (cV v) g, GeneralLinearGroup.map (pFin E) g)

def glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : GA E a :=
  infGL E a (glOf p.1) * finGL E a p.2

theorem glue_parts (g : GA E a) : glue (parts g) = g := by
  have h : glOf (fun v => GeneralLinearGroup.map (cV v) g) = GeneralLinearGroup.map (pInf E) g := by
    ext i j v
    rfl
  rw [glue, parts]
  simp only [h]
  exact infGL_mul_finGL g

theorem parts_glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : parts (glue p) = p := by
  refine Prod.ext (funext fun v => ?_) ?_
  · change GeneralLinearGroup.map (cV v) (glue p) = p.1 v
    rw [map_cV, glue, map_mul, pInf_infGL, pInf_finGL, mul_one, map_eval_glOf]
  · change GeneralLinearGroup.map (pFin E) (glue p) = p.2
    rw [glue, map_mul, pFin_infGL, pFin_finGL, one_mul]

theorem continuous_parts : Continuous (parts : GA E a → _) :=
  (continuous_pi fun v => continuous_glMap (cV v) (continuous_coordinate v) a).prodMk
    (continuous_glMap (pFin E) continuous_snd a)

theorem continuous_glue : Continuous (glue : _ → GA E a) :=
  ((continuous_cornerGL (sInf E) continuous_sInf a).comp (continuous_glOf.comp continuous_fst)).mul
    ((continuous_cornerGL (sFin E) continuous_sFin a).comp continuous_snd)

theorem compIso : CompIso := by
  intro E _ _ _ a b
  refine ⟨{ toFun := comps
            invFun := fun p => (glue (fun v => (p.1 v).1, p.2.1), glue (fun v => (p.1 v).2, p.2.2))
            left_inv := fun x => Prod.ext (glue_parts x.1) (glue_parts x.2)
            right_inv := fun p => ?_
            map_mul' := fun x y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ => rfl⟩
  · have h1 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))) v
    have h2 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))) v
    have h3 := congrArg Prod.snd (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))
    have h4 := congrArg Prod.snd (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))
    exact Prod.ext (funext fun v => Prod.ext (h1 v) (h2 v)) (Prod.ext h3 h4)
  · refine Prod.ext (funext fun v => Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> exact map_mul _ _ _
  · have p1 : Continuous fun x : GA E a × GA E b => parts x.1 := continuous_parts.comp continuous_fst
    have p2 : Continuous fun x : GA E a × GA E b => parts x.2 := continuous_parts.comp continuous_snd
    exact (continuous_pi fun v => ((continuous_apply v).comp p1.fst).prodMk ((continuous_apply v).comp p2.fst)).prodMk
      (p1.snd.prodMk p2.snd)
  · have q1 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).1, p.2.1) :
        (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).fst).prodMk continuous_snd.fst
    have q2 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).2, p.2.2) :
        (InfinitePlace E → GL (Fin b) ℂ) × GL (Fin b) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).snd).prodMk continuous_snd.snd
    exact (continuous_glue.comp q1).prodMk (continuous_glue.comp q2)

end GlobalTheory.CompanionTheory.CompIsoProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjugateEquivalence
noncomputable section

open NumberField Matrix
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj TwConjugate)

namespace GlobalTheory.CompanionTheory.ClassBij

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjE_conjE (x : E) : conjE E (conjE E x) = x := by
  simp [PositivityTheory.Rg.BcB.conjE, NumberField.IsCMField.complexConj_apply_apply]

theorem thetaE_thetaE (g : GL (Fin n) E) : thetaE E n (thetaE E n g) = g := by
  apply Units.ext
  ext i j
  simp only [PositivityTheory.Rg.BcB.thetaE, PositivityTheory.Rg.BcB.thetaR_val, ← map_inv, inv_inv, Matrix.transpose_apply,
    Matrix.map_apply]
  exact conjE_conjE _

theorem nrm_twConj (g d : GL (Fin n) E) : nrm (twConj (thetaE E n) g d) = g⁻¹ * nrm d * g := by
  simp only [PositivityTheory.Rg.BcB.nrm, twConj, map_mul, map_inv, thetaE_thetaE]
  group

theorem charpoly_nrm_twConj (g d : GL (Fin n) E) :
    (nrm (twConj (thetaE E n) g d)).val.charpoly = (nrm d).val.charpoly := by
  rw [nrm_twConj, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem isRegEll_twConj (g d : GL (Fin n) E) : IsRegEll (twConj (thetaE E n) g d) ↔ IsRegEll d := by
  simp only [PositivityTheory.Rg.BcB.IsRegEll, PositivityTheory.Rg.BcB.IsRegD, charpoly_nrm_twConj]

theorem twConjugate_equivalence : Equivalence (TwConjugate (thetaE E n)) := by
  refine ⟨fun x => ⟨1, by simp [twConj]⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp only [twConj, map_inv, inv_inv]
    group
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    simp only [twConj, map_mul, _root_.mul_inv_rev]
    group

theorem exists_out (y : GL (Fin n) E) :
    ∃ g, y = twConj (thetaE E n) g (Quot.out (Quot.mk (TwConjugate (thetaE E n)) y)) :=
  twConjugate_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq _))

theorem classBij : PositivityTheory.Rg.BcB.G8.ClassBij := by
  intro F _ _ _ m u hu
  have hθ : ∀ g : GL (Fin m) F, thE F m g = u * thetaE F m g * u⁻¹ := by
    obtain ⟨h, -⟩ := hu
    exact h
  let e : TwCl (thE F m) ≃ TwClass F m :=
    { toFun := Quot.map (fun x => x * u) (by
        rintro x y ⟨g, rfl⟩
        exact ⟨g, by simp only [twConj, hθ]; group⟩)
      invFun := Quot.map (fun x => x * u⁻¹) (by
        rintro x y ⟨g, rfl⟩
        exact ⟨g, by simp only [twConj, hθ]; group⟩)
      left_inv := by
        intro c
        induction c using Quot.ind with
        | mk x => exact congrArg (Quot.mk _) (mul_inv_cancel_right x u)
      right_inv := by
        intro c
        induction c using Quot.ind with
        | mk x => exact congrArg (Quot.mk _) (inv_mul_cancel_right x u) }
  refine ⟨e, fun c => ?_⟩
  have he : e c = Quot.mk (TwConjugate (thetaE F m)) (c.rep * u) := by
    have hc : c = Quot.mk _ c.rep := (Quot.out_eq c).symm
    calc e c = e (Quot.mk _ c.rep) := congrArg (⇑e) hc
      _ = _ := rfl
  obtain ⟨g, hg⟩ := exists_out (E := F) (n := m) (c.rep * u)
  have key := isRegEll_twConj g (Quot.out (Quot.mk (TwConjugate (thetaE F m)) (c.rep * u)))
  rw [← hg] at key
  rw [he]
  exact ⟨g, hg, key.symm⟩

end GlobalTheory.CompanionTheory.ClassBij

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormaliserUnconj
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QConjug

variable {G : Type} [Group G]

def conjEquiv {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H) : H' ≃ H where
  toFun x := ⟨g * x * g⁻¹, (hH' x).1 x.2⟩
  invFun y := ⟨g⁻¹ * y * g, (hH' _).2 (by
    have : g * (g⁻¹ * (y : G) * g) * g⁻¹ = y := by group
    rw [this]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp only []; group)
  right_inv y := Subtype.ext (by simp only []; group)

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSingletonClass G]

theorem normaliser_conj {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H Measure.count ρ) :
    IsQuotNormaliser H' Measure.count (fun x => ρ (g * x)) := by
  unfold IsQuotNormaliser at hρ ⊢
  refine ⟨hρ.1.comp (measurable_const_mul g), fun y => ?_⟩
  have h1 := hρ.2 (g * y)
  rw [lintegral_count] at h1 ⊢
  rw [← h1, ← (conjEquiv hH').tsum_eq]
  refine tsum_congr fun x => ?_
  show ρ (g * ((x : G) * y)) = ρ (g * (x : G) * g⁻¹ * (g * y))
  congr 1
  group

theorem normaliser_unconj {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H' Measure.count ρ) :
    IsQuotNormaliser H Measure.count (fun x => ρ (g⁻¹ * x)) := by
  have h2 : ∀ x, x ∈ H ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ H' := by
    intro x
    rw [hH', show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group]
  exact normaliser_conj h2 hρ

theorem qConjOf_holds : QConjOf := by
  intro hI G _ _ _ _ _ μ _ _ H H' _ F g hF hFH hH'
  haveI : Countable H' := Countable.of_equiv _ (conjEquiv hH').symm
  by_cases hex : ∃ ρ, IsQuotNormaliser H Measure.count ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' := normaliser_conj hH' hρ
    have hmeas : Measurable fun x => F (g * x) := hF.comp (measurable_const_mul g)
    have hinv : ∀ h ∈ H', ∀ x, F (g * (h * x)) = F (g * x) := by
      intro h hh x
      have := hFH (g * h * g⁻¹) ((hH' h).1 hh) (g * x)
      rw [← this]
      congr 1
      group
    rw [hI G μ H' (fun x => F (g * x)) (fun x => ρ (g * x)) hmeas hinv hρ',
      hI G μ H F ρ hF hFH hρ]
    exact integral_mul_left_eq_self (fun x => F x * ((ρ x).toReal : ℂ)) g
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' Measure.count ρ := by
      rintro ⟨ρ, hρ⟩
      exact hex ⟨_, normaliser_unconj hH' hρ⟩
    unfold quotIntegral
    rw [dite_eq_right hex, dite_eq_right hex']

end GlobalTheory.CompanionTheory.QConjug

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj twConj_mul_left mem_twCent)

namespace GlobalTheory.CompanionTheory.OrbInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  have h : ∀ g : GL (Fin n) E, (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := fun _ => rfl
  apply Units.ext
  rw [thetaR_val, ← map_inv, h, h, thetaR_val]
  ext i j
  exact conjAd_algebraMap _

theorem twConj_ratGL (g d : GL (Fin n) E) (x : GA E n) :
    twConj (thetaA E n) x (ratGL E n (twConj (thetaE E n) g d)) =
      twConj (thetaA E n) (ratGL E n g * x) (ratGL E n d) := by
  simp only [twConj, map_mul, map_inv, thetaA_ratGL]
  group

theorem mem_ratCent_twConj (g d : GL (Fin n) E) (x : GA E n) :
    x ∈ ratCent (twConj (thetaE E n) g d) ↔ ratGL E n g * x * (ratGL E n g)⁻¹ ∈ ratCent d := by
  simp only [ratCent, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := (mem_twCent _ _ _).1 hc
    simp only [twConj] at hc'
    refine ⟨g * c * g⁻¹, (mem_twCent _ _ _).2 ?_, by simp only [map_mul, map_inv]⟩
    simp only [map_mul, map_inv]
    calc (g * c * g⁻¹)⁻¹ * d * (thetaE E n g * thetaE E n c * (thetaE E n g)⁻¹)
        = g * (c⁻¹ * (g⁻¹ * d * thetaE E n g) * thetaE E n c) * (thetaE E n g)⁻¹ := by group
      _ = g * (g⁻¹ * d * thetaE E n g) * (thetaE E n g)⁻¹ := by rw [hc']
      _ = d := by group
  · rintro ⟨c, hc, h⟩
    have hc' := (mem_twCent _ _ _).1 hc
    refine ⟨g⁻¹ * c * g, (mem_twCent _ _ _).2 ?_, ?_⟩
    · simp only [twConj, map_mul, map_inv]
      calc (g⁻¹ * c * g)⁻¹ * (g⁻¹ * d * thetaE E n g) *
            ((thetaE E n g)⁻¹ * thetaE E n c * thetaE E n g)
          = g⁻¹ * (c⁻¹ * d * thetaE E n c) * thetaE E n g := by group
        _ = g⁻¹ * d * thetaE E n g := by rw [hc']
    · simp only [map_mul, map_inv, h]
      group

theorem twConj_ratCent (d : GL (Fin n) E) {h : GA E n} (hh : h ∈ ratCent d) (x : GA E n) :
    twConj (thetaA E n) (h * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
  have hc' := (mem_twCent _ _ _).1 hc
  refine twConj_mul_left _ _ ((mem_twCent _ _ _).2 ?_) x
  rw [thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul, hc']

theorem countable_ratCent [Countable (GL (Fin n) E)] (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)).Countable :=
  (Set.countable_range (ratGL E n)).mono (by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩)

theorem orbInvOf : OrbInvOf := by
  intro hQ hT E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ φ d₁ g₁ d₂ g₂ hc
  obtain ⟨⟨lc₁, sc₁, t₁⟩, -, -, cn₁, -, -⟩ := hT E a
  obtain ⟨⟨lc₂, sc₂, t₂⟩, -, -, cn₂, -, -⟩ := hT E b
  have hcnt : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) :
      Set (GA E a × GA E b)).Countable := by
    rw [Subgroup.coe_prod]
    exact (countable_ratCent d₁).prod (countable_ratCent d₂)
  have : Countable ((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) := hcnt.to_subtype
  set F : GA E a × GA E b → ℂ := fun x =>
    φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂)) with hF
  set_option synthInstance.maxHeartbeats 400000 in
  have key := hQ (GA E a × GA E b) (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
    ((ratCent (twConj (thetaE E a) g₁ d₁)).prod (ratCent (twConj (thetaE E b) g₂ d₂))) F
    (ratGL E a g₁, ratGL E b g₂) hc.measurable
    (fun h hh x => by
      simp only [hF, Prod.fst_mul, Prod.snd_mul]
      rw [twConj_ratCent d₁ hh.1, twConj_ratCent d₂ hh.2])
    (fun x => by
      simp only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        mem_ratCent_twConj])
  simp only [hF, Prod.fst_mul, Prod.snd_mul] at key
  simp only [orbTerm2, twConj_ratGL]
  exact key

end GlobalTheory.CompanionTheory.OrbInv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
open Matrix Polynomial
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticTwist

theorem exists_eigenbasis {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hs : N.charpoly.Separable) :
    ∃ (h : GL (Fin n) ℂ) (γ : Fin n → ℂ), Function.Injective γ ∧ (∀ i, N.charpoly.IsRoot (γ i)) ∧
      N * h.val = h.val * diagonal γ := by
  have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
  have hcard : N.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := Finset.equivFinOfCardEq hcard
  let γ : Fin n → ℂ := fun i => (e.symm i).1
  have hinj : Function.Injective γ := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hroot : ∀ i, N.charpoly.IsRoot (γ i) := fun i =>
    (mem_roots hne).1 (Multiset.mem_toFinset.1 (e.symm i).2)
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ (scalar (Fin n) (γ i) - N) *ᵥ v = 0 := fun i =>
    exists_mulVec_eq_zero_iff.2 (by rw [← eval_charpoly]; exact hroot i)
  choose v hv0 hv using hev
  have hNv : ∀ i, N *ᵥ v i = γ i • v i := fun i => by
    have h1 := hv i
    rw [sub_mulVec, sub_eq_zero] at h1
    rw [← h1]
    ext k
    simp [scalar_apply, mulVec_diagonal]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' N) γ hinj v
      (fun i => Module.End.hasEigenvector_iff.2
        ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hNv i), hv0 i⟩)
  have hu : IsUnit (Matrix.of v)ᵀ := linearIndependent_cols_iff_isUnit.1 hli
  obtain ⟨h, hh⟩ := hu
  refine ⟨h, γ, hinj, hroot, ?_⟩
  have hh' : h.val = (Matrix.of v)ᵀ := hh
  rw [hh']
  ext i j
  have h2 := congrFun (hNv j) i
  rw [mul_diagonal]
  simpa [Matrix.mul_apply, mulVec, dotProduct, mul_comm] using h2

variable {n : ℕ}

theorem theta_val (g : GL (Fin n) ℂ) :
    (thetaR (starRingEnd ℂ) n g).val = (g⁻¹).valᴴ := by
  ext i j
  simp [thetaR_val, conjTranspose_apply]

theorem theta_inv_val (g : GL (Fin n) ℂ) :
    ((thetaR (starRingEnd ℂ) n g)⁻¹).val = g.valᴴ := by
  rw [← map_inv, theta_val, inv_inv]

theorem theta_theta (g : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g :=
  Units.ext (by rw [theta_val, theta_inv_val, conjTranspose_conjTranspose])

theorem offDiag_eq_zero (D : Matrix (Fin n) (Fin n) ℂ) (γ : Fin n → ℂ) (hγ : ∀ i, ‖γ i‖ = 1)
    (hinj : Function.Injective γ) (hD : D = diagonal γ * Dᴴ) {i j : Fin n} (hij : i ≠ j) : D i j = 0 := by
  have h2 : Dᴴ = D * diagonal (star γ) := by
    conv_lhs => rw [hD]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  have h3 : D i j = γ i * (D i j * star (γ j)) := by
    conv_lhs => rw [hD, h2]
    rw [diagonal_mul, mul_diagonal]
    rfl
  by_contra hne
  have h4 : γ i * star (γ j) = 1 := by
    apply mul_left_cancel₀ hne
    linear_combination -h3
  have h5 : star (γ j) * γ j = 1 := by
    have := Complex.conj_mul' (γ j)
    rw [hγ j] at this
    simpa using this
  apply hij
  apply hinj
  linear_combination -γ i * h5 + γ j * h4

theorem ellDiag : EllDiag := by
  intro n d hd
  obtain ⟨hs, hn⟩ := hd
  obtain ⟨h, γ, hinj, hroot, hN⟩ := exists_eigenbasis _ hs
  have hγ : ∀ i, ‖γ i‖ = 1 := fun i => hn _ (hroot i)
  set θ := thetaR (starRingEnd ℂ) n with hθ
  let d₁ : GL (Fin n) ℂ := twConj θ h d
  have hnorm : (d₁ * θ d₁).val = diagonal γ := by
    have h1 : d₁ * θ d₁ = h⁻¹ * (d * θ d) * h := by
      simp [d₁, twConj, map_mul, map_inv, hθ, theta_theta, mul_assoc]
    rw [h1, Units.val_mul, Units.val_mul, mul_assoc, hN, ← mul_assoc, ← Units.val_mul]
    simp
  have hD : d₁.val = diagonal γ * d₁.valᴴ := by
    rw [← hnorm, ← theta_inv_val, ← Units.val_mul]
    simp [hθ]
  let b : Fin n → ℂ := fun i => d₁.val i i
  have hdiag : d₁.val = diagonal b := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [b]
    · rw [offDiag_eq_zero _ γ hγ hinj hD hij, diagonal_apply_ne _ hij]
  have hb0 : ∀ i, b i ≠ 0 := by
    intro i hi
    have h0 : d₁.val.det = 0 := by
      rw [hdiag, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 d₁.isUnit
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hbγ : ∀ i, b i = γ i * (starRingEnd ℂ) (b i) := by
    intro i
    have h1 := congrFun (congrFun hD i) i
    rw [diagonal_mul] at h1
    simpa [conjTranspose_apply] using h1
  let s : Fin n → ℂ := fun i => ((Real.sqrt ‖b i‖ : ℝ) : ℂ)
  have hnb : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (hb0 i)
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hnb i)).ne'
  have hss : ∀ i, s i * s i = (‖b i‖ : ℂ) := fun i => by
    simp only [s]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnb i).le]
  let t : GL (Fin n) ℂ := ⟨diagonal s, diagonal fun i => (s i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hs0 i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hs0 i)⟩
  have htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹ := rfl
  have htθ : (θ t).val = diagonal fun i => (s i)⁻¹ := by
    rw [hθ, theta_val, htinv, diagonal_conjTranspose]
    congr 1
    ext i
    simp [s]
  let z : Fin n → ℂ := fun i => b i / (‖b i‖ : ℂ)
  have hz2 : ∀ i, z i ^ 2 = γ i := by
    intro i
    have hne : (‖b i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hnb i).ne'
    have h1 := Complex.mul_conj' (b i)
    simp only [z]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hne), ← h1]
    conv_lhs => rw [sq]; enter [1]; rw [hbγ i]
    ring
  refine ⟨(h * t)⁻¹, twConj θ t d₁, z, ?_, ?_, ?_, ?_⟩
  · change (t⁻¹ * d₁ * θ t).val = _
    rw [Units.val_mul, Units.val_mul, htinv, hdiag, htθ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    have := hss i
    have h0 := hs0 i
    simp only [z]
    rw [← this]
    field_simp
  · intro i
    simp only [z]
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hnb i).ne']
  · intro i j hij
    apply hinj
    have := hz2 i
    have := hz2 j
    simp only at hij
    rw [← hz2 i, ← hz2 j, hij]
  · simp [twConj, d₁, map_mul, map_inv, mul_assoc]

end GlobalTheory.CompanionTheory.EllipticTwist

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotNorm

theorem count_isInvInvariant {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    [MeasurableSingletonClass G] (H : Subgroup G) : (Measure.count : Measure H).IsInvInvariant := by
  have hinv : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  ext s hs
  rw [Measure.inv_apply, Measure.count_apply hs, Measure.count_apply hs.inv, ← Set.image_inv_eq_inv]
  exact congrArg ((↑) : ℕ∞ → ℝ≥0∞) (inv_injective.encard_image s)

theorem qIndep : PositivityTheory.Rg.BcB.G8.QIndep := by
  intro G _ _ _ _ _ μ _ _ H _ F ρ hF hFH hρ
  have := count_isInvInvariant H
  exact quotIntegral_eq (μG := μ) hF hFH hρ

end GlobalTheory.CompanionTheory.QuotNorm
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PWeylAt
noncomputable section

open NumberField Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem weylat_weylChar_eq_gtChar {n : ℕ} (l : DomWeight n) (γ : Fin n → ℂ) (h0 : ∀ i, γ i ≠ 0)
    (hinj : Function.Injective γ) :
    PositivityTheory.RgBcC.weylChar l.w γ = ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar n l.w γ := by
  have hA : (Matrix.of fun i j : Fin n => γ i ^ (l.w j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (l.w + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    congr 1
    have := j.isLt
    omega
  have hV : (Matrix.of fun i j : Fin n => γ i ^ (n - 1 - (j : ℕ))).det =
      ReciprocityTheory.ChartRestriction.TR.Weyl.alt n (0 + ReciprocityTheory.ChartRestriction.TR.Weyl.delta n) γ := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.alt
    congr 1
    ext i j
    simp only [Matrix.of_apply, Pi.add_apply, Pi.zero_apply, zero_add, ReciprocityTheory.ChartRestriction.TR.Weyl.delta]
    rw [← zpow_natCast]
    congr 1
    have := j.isLt
    omega
  have h1 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n l.w l.anti γ h0
  have h2 := ReciprocityTheory.ChartRestriction.TR.Weyl.weylGT ℂ n 0 antitone_const γ h0
  have hzero : ∀ (m : ℕ) (t : Fin m → ℂ), ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar m 0 t = 1 := by
    intro m
    induction m with
    | zero => intro t; simp [ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar]
    | succ m ih =>
      intro t
      have h : ReciprocityTheory.ChartRestriction.TR.Weyl.interl (0 : Fin (m + 1) → ℤ) = {(0 : Fin m → ℤ)} := by
        ext mu
        simp only [ReciprocityTheory.ChartRestriction.TR.Weyl.interl, Fintype.mem_piFinset,
          Pi.zero_apply, Finset.Icc_self, Finset.mem_singleton]
        exact ⟨fun h => funext h, fun h i => congrFun h i⟩
      rw [ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar, h, Finset.sum_singleton, ih]
      simp [ReciprocityTheory.ChartRestriction.TR.Weyl.wsum]
  rw [hzero, mul_one] at h2
  have hw : ReciprocityTheory.ChartRestriction.TR.Weyl.wden n γ ≠ 0 := by
    unfold ReciprocityTheory.ChartRestriction.TR.Weyl.wden
    refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
    split_ifs with h
    · exact sub_ne_zero.2 fun e => (ne_of_lt h) (hinj e)
    · exact one_ne_zero
  unfold PositivityTheory.RgBcC.weylChar
  rw [hA, hV, ← h1, ← h2, mul_div_cancel_left₀ _ hw]

theorem weylAt_holds : WeylAt := by
  intro n l γ h0 hinj
  let D : GL (Fin n) ℂ := Formalism.BasicNotions.diagGL ℂ n fun i => Units.mk0 _ (h0 i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal γ := by
    change diagonal (fun a => ((Units.mk0 _ (h0 a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hex : ∃ g : GL (Fin n) ℂ, g.val.charpoly = (diagonal γ).charpoly := ⟨D, by rw [hD]⟩
  unfold chAt
  rw [dite_eq_left hex, GlobalTheory.ContraChar.trace_sqRep_eq_of_charpoly_eq l _ D (hex.choose_spec.trans (by rw [hD])),
    GlobalTheory.ContraChar.trace_sqRep_diag l D γ hD, weylat_weylChar_eq_gtChar l γ h0 hinj]

end PositivityTheory.Rg.BcB.G8

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfHolds
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem mul_finsum_eq {α : Type*} (r : ℂ) (f : α → ℂ) : ∑ᶠ i, r * f i = r * ∑ᶠ i, f i := by
  have h := smul_finsum (R := ℂ) (M := ℂ) r f
  simpa only [smul_eq_mul] using h.symm

theorem global_character_of_holds : GlobalCharacterOfInputs := by
  intro hT hO hA hC hP E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨c, hc0, hc⟩ := hT E hU a b μ₁ μ₂ ν₁ ν₂
  refine ⟨c, hc0, ?_⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂
  obtain ⟨e₁, he₁⟩ := hC E a u₁ hu₁
  obtain ⟨e₂, he₂⟩ := hC E b u₂ hu₂
  have hψ : ∀ v, Continuous (ψ v) := fun v => (hL v).1
  unfold ellSum2 geomRat2
  rw [← finsum_comp_equiv (e₁.prodCongr e₂), ← mul_finsum_eq]
  refine finsum_congr fun x => ?_
  obtain ⟨x₁, x₂⟩ := x
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
  obtain ⟨g₁, hg₁, hr₁⟩ := he₁ x₁
  obtain ⟨g₂, hg₂, hr₂⟩ := he₂ x₂
  have hiff : (IsRegEll (Quot.out (e₁ x₁)) ∧ IsRegEll (Quot.out (e₂ x₂))) ↔ (pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b) := by
    rw [hr₁, hr₂, (hP E a u₁ hu₁ _).1, (hP E b u₂ hu₂ _).1, mul_inv_cancel_right, mul_inv_cancel_right]
    exact Iff.rfl
  have horb : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (Quot.out (e₁ x₁)) (Quot.out (e₂ x₂)) =
      orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) (x₁.rep * u₁) (x₂.rep * u₂) := by
    rw [hg₁, hg₂, hO E a b μ₁ μ₂ _ _ g₁ _ g₂ (hA E hU a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ hψ hφ₁ hφ₂ _ _)]
  rw [finsum_eq_if]
  by_cases h : pol x₁ ∈ Ell E a ∧ pol x₂ ∈ Ell E b
  · rw [if_pos (hiff.2 h), if_pos h, horb]
    have ht := hc S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hL hφ₁ hφ₂ (x₁.rep * u₁) (x₂.rep * u₂)
      (hr₁.1 (hiff.2 h).1) (hr₂.1 (hiff.2 h).2)
    simp only [mul_inv_cancel_right] at ht
    exact ht
  · rw [if_neg (mt hiff.1 h), if_neg h, mul_zero]

end PositivityTheory.Rg.BcB.G8

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTermOf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj)

theorem termof_twConj_cont {n : ℕ} (hθ : Continuous (thetaR (starRingEnd ℂ) n)) (d : GL (Fin n) ℂ) :
    Continuous fun x : GL (Fin n) ℂ => twConj (thetaR (starRingEnd ℂ) n) x d := by
  show Continuous fun x : GL (Fin n) ℂ => x⁻¹ * d * thetaR (starRingEnd ℂ) n x
  exact (continuous_inv.mul continuous_const).mul hθ

theorem termof_hcs {a b : ℕ} (hEP : EllProper) (ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ) (hψ : HasCompactSupport ψ)
    (d₁ : GL (Fin a) ℂ) (d₂ : GL (Fin b) ℂ) (h₁ : EllC d₁) (h₂ : EllC d₂) :
    HasCompactSupport fun y : GL (Fin a) ℂ × GL (Fin b) ℂ =>
      ψ (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) := by
  have hK := (hEP a d₁ h₁ _ (hψ.isCompact.image continuous_fst)).prod
    (hEP b d₂ h₂ _ (hψ.isCompact.image continuous_snd))
  refine HasCompactSupport.intro hK fun y hy => ?_
  by_contra hne
  apply hy
  have hm : (twConj (thetaR (starRingEnd ℂ) a) y.1 d₁, twConj (thetaR (starRingEnd ℂ) b) y.2 d₂) ∈ tsupport ψ :=
    subset_tsupport _ hne
  exact ⟨⟨_, hm, rfl⟩, ⟨_, hm, rfl⟩⟩

theorem termOf_holds : TermOf := by
  intro hQS hHS hTopo hCI hKf hFL hFH hAE hCE hPE hEP
  intro E _ _ _ hU a b _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ ν₁ _ ν₂ _
  obtain ⟨⟨hlcA, hscA, ht2A⟩, ⟨hlcfA, hscfA, ht2fA⟩, ⟨hlcCA, hscCA⟩, hcntA, -, hθA⟩ := hTopo E a
  obtain ⟨⟨hlcB, hscB, ht2B⟩, ⟨hlcfB, hscfB, ht2fB⟩, ⟨hlcCB, hscCB⟩, hcntB, -, hθB⟩ := hTopo E b
  letI mB : MeasurableSpace (Gf E a b) := borel _
  haveI : BorelSpace (Gf E a b) := ⟨rfl⟩
  obtain ⟨e, he⟩ := hCI E a b
  let e' : (GA E a × GA E b) →* (Gi E a b × Gf E a b) := e.toMulEquiv.toMonoidHom
  have he' : ∀ x, e' x = comps x := he
  have hνH : (ν₁.prod ν₂).IsHaarMeasure := inferInstance
  have hνS : SigmaFinite (ν₁.prod ν₂) := inferInstance
  have hαH : (Measure.pi fun _ : InfinitePlace E => ν₁.prod ν₂).IsHaarMeasure := inferInstance
  let α : Measure (Gi E a b) := Measure.pi fun _ => ν₁.prod ν₂
  set_option synthInstance.maxHeartbeats 100000 in
  obtain ⟨β, hβ, hmap⟩ := hHS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α e
  haveI := hβ
  obtain ⟨hKo₁, hKc₁⟩ := hKf E a
  obtain ⟨hKo₂, hKc₂⟩ := hKf E b
  have hKo : IsOpen (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKo₁.prod hKo₂
  have hKc : IsCompact (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) := by
    rw [Subgroup.coe_prod]; exact hKc₁.prod hKc₂
  refine ⟨(β.real (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b)) : ℂ), ?_, ?_⟩
  · rw [Complex.ofReal_ne_zero, measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hKo.measure_ne_zero β ⟨1, Subgroup.one_mem _⟩, hKc.measure_lt_top.ne⟩
  intro S hS u₁ u₂ hu₁ hu₂ l₁ l₂ val ψ φ₁ φ₂ hLef hφ₁ hφ₂ d₁ d₂ hd₁ hd₂
  obtain ⟨hP₁, hPv₁⟩ := hPE E a u₁ hu₁ d₁
  obtain ⟨hP₂, hPv₂⟩ := hPE E b u₂ hu₂ d₂
  have hCE' := hCE E a b u₁ u₂ hu₁ hu₂ d₁ d₂
  let f : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ := fun v y =>
    ψ v (twConj (thetaR (starRingEnd ℂ) a) y.1 (GeneralLinearGroup.map v.embedding d₁),
      twConj (thetaR (starRingEnd ℂ) b) y.2 (GeneralLinearGroup.map v.embedding d₂))
  let F₁ : Gi E a b → ℂ := fun y => ∏ v, f v (y v)
  let F₂ : Gf E a b → ℂ := orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)
  have hfc : ∀ v, Continuous (f v) := fun v =>
    (hLef v).1.comp (((termof_twConj_cont hθA _).comp continuous_fst).prodMk
      ((termof_twConj_cont hθB _).comp continuous_snd))
  have hfs : ∀ v, HasCompactSupport (f v) := fun v =>
    termof_hcs hEP (ψ v) (hLef v).2.1 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂)
  have hint : ∀ v, Integrable (f v) (ν₁.prod ν₂) := fun v => (hfc v).integrable_of_hasCompactSupport (hfs v)
  have hF₁i : Integrable F₁ α := Integrable.fintype_prod hint
  have hF₁m : Measurable F₁ :=
    (continuous_finsetProd _ fun v _ => (hfc v).comp (continuous_apply v)).measurable
  haveI : Countable ↥((ratCent d₁).prod (ratCent d₂)) := by
    have hsub : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) : Set (GA E a × GA E b)) ⊆
        Set.range (fun p : GL (Fin a) E × GL (Fin b) E => (ratGL E a p.1, ratGL E b p.2)) := by
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_prod] at hx
      obtain ⟨g₁, -, hg₁⟩ := Subgroup.mem_map.1 hx.1
      obtain ⟨g₂, -, hg₂⟩ := Subgroup.mem_map.1 hx.2
      exact ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩
    exact ((Set.countable_range _).mono hsub).to_subtype
  have hΓ : ((ratCent d₁).prod (ratCent d₂)).map ((MonoidHom.snd _ _).comp e') = gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) := by
    ext y
    rw [Subgroup.mem_map, hCE'.1 y]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, (congrArg Prod.snd (he' γ)).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, congrArg Prod.snd (he' γ)⟩
  have hinj : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), (e' γ).2 = 1 → γ = 1 := by
    intro γ hγ h1
    rw [he'] at h1
    exact (hCE'.2 γ hγ).1 h1
  have hF₁inv : ∀ γ ∈ (ratCent d₁).prod (ratCent d₂), ∀ x, F₁ ((e' γ).1 * x) = F₁ x := by
    intro γ hγ x
    have hc := (hCE'.2 γ hγ).2
    rw [he']
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [f, Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]
    rw [PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).1, PositivityTheory.Rg.Tf.Loc.twConj_mul_left _ _ (hc v).2]
  have hF₂inv : ∀ γ ∈ gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹), ∀ y, F₂ (γ * y) = F₂ y := by
    intro γ hγ y
    have h : γ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) =
        (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b γ := (Subgroup.mem_inf.1 hγ).2
    simp only [F₂, orbFn]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ at h ⊢
    rw [(thP E a b).map_mul γ y, show (γ * y)⁻¹ * δ * (thP E a b γ * thP E a b y) =
      y⁻¹ * (γ⁻¹ * (δ * thP E a b γ)) * thP E a b y by group, ← h]
    group
  obtain ⟨U, hUo, hUinv⟩ := hFL E hU a b S φ₁ φ₂ hφ₁ hφ₂
  have hF₂U : ∀ u ∈ U, ∀ y, F₂ (y * u) = F₂ y := by
    intro u hu y
    simp only [F₂, orbFn]
    rw [← hUinv u hu (y⁻¹ * (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) * thP E a b y)]
    congr 1
    generalize (ratF E a (d₁ * u₁⁻¹), ratF E b (d₂ * u₂⁻¹)) = δ
    rw [(thP E a b).map_mul y u]
    group
  obtain ⟨hfin, hstab, hdc⟩ :=
    hFH E hU a b S hS φ₁ φ₂ hφ₁ hφ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (hP₁.1 hd₁) (hP₂.1 hd₂)
  set_option synthInstance.maxHeartbeats 400000 in
  have hQ := hQS (GA E a × GA E b) (Gi E a b) (Gf E a b) (μ₁.prod μ₂) α β e' (map_continuous e).measurable hmap
    ((ratCent d₁).prod (ratCent d₂)) (gam (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) ((Kf E a).prod (Kf E b)) U hΓ hinj hKo hKc hUo
    F₁ F₂ hF₁m hF₁i hF₁inv hF₂inv hF₂U hfin hstab
  have hEq : orbTerm2 μ₁ μ₂ (adel S u₁ u₂ ψ φ₁ φ₂) d₁ d₂ = quotIntegral (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
      Measure.count (fun x => F₁ (e' x).1 * F₂ (e' x).2) := by
    unfold orbTerm2
    congr 1
    funext x
    rw [hAE E a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ d₁ d₂ x, he' x]
  have hI : ∫ x, F₁ x ∂α = ∏ v, (val v * starRingEnd ℂ (chAt (l₁ v) ((polE (d₁ * u₁⁻¹)).map v.embedding)) *
      starRingEnd ℂ (chAt (l₂ v) ((polE (d₂ * u₂⁻¹)).map v.embedding))) := by
    rw [integral_fintype_prod_eq_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hLef v).2.2 _ _ ((hPv₁ v).2 hd₁) ((hPv₂ v).2 hd₂), (hPv₁ v).1, (hPv₂ v).1]
  rw [hEq, hQ, hI, hdc, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [chW]
  ring

end PositivityTheory.Rg.BcB.G8

end
end

namespace PositivityTheory.Rg.BcB.G8

open GlobalTheory.CompanionTheory

theorem translation_existence_holds : TranslEx := LocalThetaTranslation.translEx

theorem lefschetz_pair_holds : LefPair := GlobalTheory.CompanionTheory.LefPair.lefPairOf EllipticTwist.ellDiag weylAt_holds LocalThetaTopology.topo

theorem global_character_of_finite_inputs (hK : KfOC) (hL : FinLevel) (hF : FinHalf) : G4 :=
  have hA : AdelEq := AdelEqProof.adelEqOf TranslAdele.translAd
  global_character_of_holds
    (termOf_holds (QSplitPf.qSplitOf QuotNorm.qIndep) HaarProd.haarSplit LocalThetaTopology.topo CompIsoProof.compIso hK hL hF hA
      TwistCent.centEq NormPoly.polEq (EllProp.ellProperOf EllipticTwist.ellDiag DiagProperProof.diagProper LocalThetaTopology.topo))
    (GlobalTheory.CompanionTheory.OrbInv.orbInvOf (QConjug.qConjOf_holds QuotNorm.qIndep) LocalThetaTopology.topo)
    (GlobalTheory.CompanionTheory.AdelCont.adelContOf hA hL CompIsoProof.compIso LocalThetaTopology.topo) GlobalTheory.CompanionTheory.ClassBij.classBij NormPoly.polEq

end PositivityTheory.Rg.BcB.G8
