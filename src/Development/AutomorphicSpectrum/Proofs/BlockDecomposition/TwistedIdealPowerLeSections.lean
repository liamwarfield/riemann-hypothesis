module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import GroundTheory.AutomorphicForms.GeometricLemma

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

attribute [local instance] algebraOfOver

lemma toFunctions_top_eq {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (a : A) :
    toFunctions (X := X) (A := A) ⊤ a = algebraMap A Γ(X, ⊤) a := by
  change (X.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op).hom _ = _
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id, X.presheaf.map_id]
  rfl

lemma twist_map_smulHom_app {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (r : Γ(X, ⊤)) (c : Γ(GlobalTheory.twist P L, ⊤)) :
    (GlobalTheory.Twist.map L (GroundTheory.Arith.SchemeCoh.smulHom P r)).app ⊤ c = r • c := by
  apply GlobalTheory.Twist.sec_ext
  intro i
  rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]

lemma smul_mem_twSecs {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ)
    {a : A} (ha : a ∈ I ^ m) (c : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    toFunctions (X := X) (A := A) ⊤ a • c ∈ twSecs H n (powSub I P m) := by
  let g : P ⟶ (powSub I P m : X.Modules) :=
    idealPowOfMem I P a ha ≫ (Subobject.underlyingIso (idealPowι I P m)).inv
  have hg : g ≫ (powSub I P m).arrow = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    simp only [g, powSub, Category.assoc]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Iso.inv_hom_id_assoc, idealPowOfMem_ι]
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) g).app ⊤ c, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, ← GlobalTheory.Twist.map_comp, hg,
    twist_map_smulHom_app, toFunctions_top_eq]

def twSecsSub {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules}
    (S : Subobject P) : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤) where
  carrier := twSecs H n S
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro r _ ⟨x, rfl⟩
    exact ⟨r • x, Scheme.Modules.Hom.app_smul _ _ _⟩

theorem twPow_subset_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ),
      twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  intro A _ _ I X _ H _ P _ n m
  have key : (Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ :
      Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) ≤ twSecsSub H n (powSub I P m) := by
    rw [Submodule.smul_le]
    intro r hr c _
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact smul_mem_twSecs I H n P m ha c
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul x y _ hy => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hy
  exact key

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_ideal_power_le_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ), twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  first | exact @GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs | exact GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs | (intros; apply GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentPreservesFlag
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.FlagCent

variable {K : Type} [Field K] {n : ℕ}

theorem img_mul (g h : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img (g * h) W = img g (img h W) := by
  simp only [img, Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem img_one (W : Submodule K (Fin n → K)) : img (1 : GL (Fin n) K) W = W := by
  simp [img]

theorem mem_img_iff (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) (y : Fin n → K) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) K).val *ᵥ y ∈ W := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (g⁻¹ : GL (Fin n) K).val * g.val = 1 := by rw [← Units.val_mul]; simp
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, this] using hx
  · intro h
    refine ⟨_, h, ?_⟩
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]

theorem form_mulVec (σ : K →+* K) (A : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    ∑ i, σ ((A *ᵥ x) i) * y i = ∑ j, σ (x j) * ((A.map σ)ᵀ *ᵥ y) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, transpose_apply,
    map_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem perp_img (σ : K →+* K) (g : GL (Fin n) K) (X : Submodule K (Fin n → K)) :
    perp σ (img g X) = img (thetaR σ n g) (perp σ X) := by
  ext y
  rw [mem_img_iff]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  constructor
  · intro h x hx
    rw [← form_mulVec]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, form_mulVec]
    exact h x hx

theorem le_perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    W ≤ perp σ (perp σ W) := fun z hz y hy => by
  have h2 := congrArg σ (hy z hz)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hσ, map_zero] at h2
  simpa [mul_comm] using h2

theorem perp_perp (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (W : Submodule K (Fin n → K)) :
    perp σ (perp σ W) = W := by
  refine le_antisymm (fun z hz => ?_) (le_perp_perp σ hσ W)
  by_contra hn
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hn
  let a : Fin n → K := fun i => f fun j => if i = j then 1 else 0
  have hfa : ∀ x, f x = ∑ i, x i * a i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]; rfl
  have hy : (fun i => σ (a i)) ∈ perp σ W := fun x hx => by
    have h0 : f x = 0 := hf hx
    rw [hfa] at h0
    have := congrArg σ h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, map_zero] using this
  have h1 := hz _ hy
  simp only [hσ] at h1
  exact hf0 (by rw [hfa]; simpa [mul_comm] using h1)

theorem perpD_perpD (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (W : Submodule K (Fin n → K)) :
    perpD σ d (perpD σ d W) = img (d * thetaR σ n d) W := by
  simp only [perpD]
  rw [perp_img, perp_perp σ hσ, img_mul]

theorem thetaR_thetaR (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (g : GL (Fin n) K) :
    thetaR σ n (thetaR σ n g) = g := by
  apply Units.ext
  rw [thetaR_val]
  have hinv : ((thetaR σ n g)⁻¹ : GL (Fin n) K).val = (g.val.map σ)ᵀ := rfl
  rw [hinv]
  ext i j
  simp [hσ]

theorem commute_norm (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) {d t : GL (Fin n) K}
    (ht : t ∈ twCent (thetaR σ n) d) :
    t * (d * thetaR σ n d) = (d * thetaR σ n d) * t := by
  have h1 : t⁻¹ * d * thetaR σ n t = d := ht
  have h2 : thetaR σ n d = (thetaR σ n t)⁻¹ * thetaR σ n d * t := by
    conv_lhs => rw [← h1]
    rw [map_mul, map_mul, map_inv, thetaR_thetaR σ hσ]
  have h3 : t * d = d * thetaR σ n t := by
    calc t * d = t * (t⁻¹ * d * thetaR σ n t) := by rw [h1]
      _ = d * thetaR σ n t := by group
  have h4 : thetaR σ n t * thetaR σ n d = thetaR σ n d * t := by
    calc thetaR σ n t * thetaR σ n d
        = thetaR σ n t * ((thetaR σ n t)⁻¹ * thetaR σ n d * t) := by rw [← h2]
      _ = thetaR σ n d * t := by group
  rw [← mul_assoc, h3, mul_assoc, h4, ← mul_assoc]

theorem map_le_of_commute [IsAlgClosed K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f t : Module.End K V) (hs : LinearMap.charpoly f |>.Separable)
    (hc : Commute f t) (W : Submodule K V) (hW : ∀ x ∈ W, f x ∈ W) : W.map t ≤ W := by
  have hW' : W = ⨆ μ, W ⊓ f.maxGenEigenspace μ := by
    have h := Submodule.inf_iSup_genEigenspace (p := W) (f := f) hW ⊤
    rw [show ⨆ μ, f.genEigenspace μ ⊤ = ⊤ from Module.End.iSup_maxGenEigenspace_eq_top f,
      inf_top_eq] at h
    exact h
  rw [Submodule.map_le_iff_le_comap]
  conv_lhs => rw [hW']
  refine iSup_le fun μ x hx => ?_
  have hdim : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq]
    exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
  have htx : t x ∈ f.maxGenEigenspace μ := Module.End.mapsTo_maxGenEigenspace_of_comm hc μ hx.2
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hdim
  obtain ⟨a, ha⟩ := hv ⟨x, hx.2⟩
  obtain ⟨b, hb⟩ := hv ⟨t x, htx⟩
  have ha' : a • (v : V) = x := congrArg Subtype.val ha
  have hb' : b • (v : V) = t x := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx0 (by simpa using ha'.symm)
  change t x ∈ W
  rw [← hb', show b • (v : V) = (b / a) • x by rw [← ha', smul_smul, div_mul_cancel₀ _ ha0]]
  exact W.smul_mem _ hx.1

theorem img_eq_of_commute [IsAlgClosed K] (γ t : GL (Fin n) K) (hs : γ.val.charpoly.Separable)
    (hc : t * γ = γ * t) (W : Submodule K (Fin n → K)) (hW : img γ W = W) : img t W = W := by
  have key : ∀ s : GL (Fin n) K, s * γ = γ * s → img s W ≤ W := fun s hcs => by
    refine map_le_of_commute (Matrix.toLin' γ.val) (Matrix.toLin' s.val)
      (by rwa [Matrix.charpoly_toLin']) ?_ W fun x hx => ?_
    · change Matrix.toLin' γ.val * Matrix.toLin' s.val = Matrix.toLin' s.val * Matrix.toLin' γ.val
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← Units.val_mul, ← Units.val_mul, hcs]
    · rw [← hW]; exact ⟨x, hx, rfl⟩
  refine le_antisymm (key t hc) ?_
  have hinv : t⁻¹ * γ = γ * t⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, hc]
  calc W = img t (img t⁻¹ W) := by rw [← img_mul, mul_inv_cancel, img_one]
    _ ≤ img t W := Submodule.map_mono (key t⁻¹ hinv)

theorem twCent_preserves_flag [IsAlgClosed K] (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (d : GL (Fin n) K) (hd : (d * thetaR σ n d).val.charpoly.Separable)
    (W₁ W₂ : Submodule K (Fin n → K)) (h₁ : perpD σ d W₁ = W₂) (h₂ : perpD σ d W₂ = W₁)
    {t : GL (Fin n) K} (ht : t ∈ twCent (thetaR σ n) d) : img t W₁ = W₁ ∧ img t W₂ = W₂ := by
  have hc := commute_norm σ hσ ht
  refine ⟨img_eq_of_commute _ t hd hc _ ?_, img_eq_of_commute _ t hd hc _ ?_⟩
  · rw [← perpD_perpD σ hσ, h₁, h₂]
  · rw [← perpD_perpD σ hσ, h₂, h₁]

end GlobalTheory.CompanionTheory.FlagCent
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslation
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegMoveProof

theorem log_step {a b c : ℝ} {k n : ℕ} (hkn : k ≤ n) (ha : 0 < a) (hb : 0 < b) (h : a ≤ c ^ k * b) :
    Real.log a ≤ n * Real.posLog c + Real.log b := by
  have hp : 0 < c ^ k * b := lt_of_lt_of_le ha h
  have hck : c ^ k ≠ 0 := fun h0 => by simp [h0] at hp
  have h1 : Real.log a ≤ Real.log (c ^ k * b) := Real.log_le_log ha h
  rw [Real.log_mul hck hb.ne', Real.log_pow] at h1
  have h2 : Real.log c ≤ Real.posLog c := le_max_right 0 (Real.log c)
  have h3 : (0 : ℝ) ≤ Real.posLog c := Real.posLog_nonneg
  have h4 : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h5 : (k : ℝ) * Real.log c ≤ n * Real.posLog c :=
    (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)).trans (mul_le_mul_of_nonneg_right h4 h3)
  linarith

theorem finsum_bound {α : Type} {f g s : α → ℝ} {c : ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (hs : (Function.support s).Finite) (h : ∀ a, f a ≤ c * s a + g a) :
    ∑ᶠ a, f a ≤ c * ∑ᶠ a, s a + ∑ᶠ a, g a := by
  classical
  let T : Finset α := hf.toFinset ∪ hg.toFinset ∪ hs.toFinset
  rw [finsum_eq_sum_of_support_subset f (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset g (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset s (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => h a

theorem sz_sq_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : sz g ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖g p.1 p.2‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n × Fin n) with he | hne
  · simp [sz, Real.iSup_of_isEmpty]
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖)
    rw [sz, ← hp]
    exact le_ciSup (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖ ^ 2) (Set.finite_range _).bddAbove p

theorem nI_nonneg {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  open ComplexOrder in
  have h : 0 ≤ (Aᴴ * A).det := (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg
  exact (Complex.le_def.1 h).1

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem exists_left_inv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ N : Matrix (Fin k) (Fin n) K, N * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_iff.2 h
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h1 : LinearMap.toMatrix' (f ∘ₗ M.mulVecLin) = 1 := by rw [hf]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n k : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem inf_step (hI : MulI) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (v : InfinitePlace E) (h0 : nI ((h * A).map (cV v)) ≠ 0) (h1 : nI (A.map (cV v)) ≠ 0) :
    Real.log (nI ((h * A).map (cV v))) ≤
      n * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2)) +
        Real.log (nI (A.map (cV v))) := by
  have hm : (h * A).map (cV v) = h.map (cV v) * A.map (cV v) := Matrix.map_mul
  have hle := (hI (Fin n) (Fin n) (Fin k) (A.map (cV v))).1 (h.map (cV v))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  have hs := log_step hkn (lt_of_le_of_ne (nI_nonneg _) h0.symm) (lt_of_le_of_ne (nI_nonneg _) h1.symm) hle
  refine hs.trans ?_
  have h2 : Real.posLog ((n : ℝ) * n * sz (h.map (cV v)) ^ 2) ≤
      Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2) :=
    Real.posLog_mul.trans (add_le_add le_rfl (Real.posLog_le_posLog (by nlinarith [sq_nonneg (sz (h.map (cV v)))]) (sz_sq_le _)))
  have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem fin_step (hF : MulF) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (w : HeightOneSpectrum (𝓞 E)) (h0 : nF ((h * A).map (cW w)) ≠ 0) (h1 : nF (A.map (cW w)) ≠ 0) :
    Real.log (nF ((h * A).map (cW w))) ≤
      n * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h p.1 p.2)‖) + Real.log (nF (A.map (cW w))) := by
  haveI := ultra w
  have hm : (h * A).map (cW w) = h.map (cW w) * A.map (cW w) := Matrix.map_mul
  have hle := (hF (w.adicCompletion E) (Fin n) (Fin n) (Fin k) (A.map (cW w))).1 (h.map (cW w))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  exact log_step hkn (lt_of_le_of_ne (nF_nonneg _) h0.symm) (lt_of_le_of_ne (nF_nonneg _) h1.symm) hle

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem frame_move (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) :
    (x⁻¹ * ratGL E n g * x : GA E n).val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) =
      (x⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) := by
  have h1 : (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := rfl
  rw [Matrix.map_mul, ← h1, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem core (hF : MulF) (hI : MulI) (hSz : SzFin) (hFS : FinSupp) (hkn : k ≤ n) (h : GA E n)
    (A : Matrix (Fin n) (Fin k) (Ad E)) (Y : Matrix (Fin k) (Fin n) (Ad E)) (hY : Y * A = 1) :
    ∑ v, Real.log (nI ((h.val * A).map (cV v))) + ∑ᶠ w, Real.log (nF ((h.val * A).map (cW w))) ≤
      (∑ v, Real.log (nI (A.map (cV v))) + ∑ᶠ w, Real.log (nF (A.map (cW w)))) +
        n * ((Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)) + n * logSizeM h.val := by
  have hY' : (Y * (h⁻¹ : GA E n).val) * (h.val * A) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹ : GA E n).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, hY]
  obtain ⟨a1, a2, a3⟩ := hFS E (Fin n) (Fin k) A Y hY
  obtain ⟨b1, b2, b3⟩ := hFS E (Fin n) (Fin k) (h.val * A) _ hY'
  have hinf := Finset.sum_le_sum (s := Finset.univ) fun v (_ : v ∈ Finset.univ) =>
    inf_step (E := E) hI hkn h.val A v (b1 v) (a1 v)
  have hfin := finsum_bound (c := (n : ℝ))
    (f := fun w => Real.log (nF ((h.val * A).map (cW w))))
    (g := fun w => Real.log (nF (A.map (cW w))))
    (s := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖))
    (b3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    (a3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    ((hSz E (Fin n) (Fin n) h.val).subset fun w hw => by
      by_contra hc
      apply hw
      exact max_eq_left (Real.log_nonpos (Real.iSup_nonneg fun _ => norm_nonneg _) (not_lt.1 hc)))
    fun w => fin_step hF hkn h.val A w (b2 w) (a2 w)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hinf
  have hS : logSizeM h.val = ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h.val p.1 p.2)‖ ^ 2) +
      ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖) := rfl
  rw [hS]
  nlinarith [hinf, hfin]

theorem lin_basisMat (W : Submodule E (Fin n → E)) : LinearIndependent E (basisMat W)ᵀ ∧
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  have hM : (basisMat W)ᵀ = W.subtype ∘ (Module.finBasis E W) := by
    funext j i
    rfl
  rw [hM]
  refine ⟨(Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem linearIndependent_image_span (g : GL (Fin n) E) (f : Fin k → Fin n → E) (hf : LinearIndependent E f) :
    LinearIndependent E (Matrix.toLin' g.val ∘ f) ∧
      Submodule.span E (Set.range (Matrix.toLin' g.val ∘ f)) = img g (Submodule.span E (Set.range f)) := by
  have inj : Function.Injective (Matrix.toLin' g.val) := fun a b hab => by
    have h1 := congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  refine ⟨hf.map' _ (LinearMap.ker_eq_bot.2 inj), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span]
  rfl

theorem lin_moved (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) (hM : LinearIndependent E Mᵀ) :
    LinearIndependent E (g.val * M)ᵀ ∧
      Submodule.span E (Set.range (g.val * M)ᵀ) = img g (Submodule.span E (Set.range Mᵀ)) := by
  have hG : (Matrix.toLin' g.val ∘ (Mᵀ : Fin k → Fin n → E)) = ((g.val * M)ᵀ : Fin k → Fin n → E) := by
    funext j i
    change (Matrix.toLin' g.val (fun i' => M i' j)) i = (g.val * M) i j
    rw [Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h1 := linearIndependent_image_span g Mᵀ hM
  rw [hG] at h1
  exact h1

theorem degMove_of : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  intro hF hI hSz hFS hB E _ _ _ n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), fun x g W => ?_⟩
  obtain ⟨hLI, hspan⟩ := lin_basisMat W
  obtain ⟨hLI', hspan'⟩ := lin_moved g (basisMat W) hLI
  rw [hspan] at hspan'
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have e1 : deg x (img g W) = degG x (g.val * basisMat W) := by rw [hB E n _ x _ hLI', hspan']
  have e2 : deg x W = degG x (basisMat W) := rfl
  have hY : (N.map (algebraMap E (Ad E)) * x.val) * ((x⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn (x⁻¹ * ratGL E n g * x) _ _ hY
  rw [frame_move] at hc
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg (x⁻¹ * ratGL E n g * x : GA E n).val
  have hS' := logSizeM_nonneg ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val
  have hL : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hsz : logSize (x⁻¹ * ratGL E n g * x) = logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val +
    logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val = S at *
  generalize logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 ≤ (n : ℝ) * (1 + S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegMoveProof

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslationStatement
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_under_translation : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  first | exact @GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | exact GlobalTheory.CompanionTheory.DegMoveProof.degMove_of | (intros; apply GlobalTheory.CompanionTheory.DegMoveProof.degMove_of <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLevi
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLevi
set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.DeltaLevi

open GroundTheory.Automorphic.Measures

theorem prod_pairs_le {α G : Type} [Fintype α] [LinearOrder α] [CommGroup G] (n : α → ℕ) (x : α → G) :
    ∏ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      ∏ a, x a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
  have hz : ∀ (y : G) (f : α → ℤ), ∏ b, y ^ f b = y ^ ∑ b, f b := by
    intro y f
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  have h1 : ∀ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      x c.1 ^ (if c.1 ≤ c.2 then (n c.2 : ℤ) else 0) *
        x c.2 ^ (-(if c.1 ≤ c.2 then (n c.1 : ℤ) else 0)) := by
    intro c
    split_ifs <;> simp
  simp only [h1]
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type, Fintype.prod_prod_type,
    Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a b => x b ^ (-(if a ≤ b then (n a : ℤ) else 0))), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  dsimp only
  rw [hz, hz, ← zpow_add, Finset.sum_neg_distrib, Finset.sum_filter, Finset.sum_filter,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.le, h.not_ge, h.not_gt]
  · simp [h]
  · simp [h, h.le, h.not_ge, h.not_gt]

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)]

theorem leviEmb_eq_zero (e : (Σ i, m i) ≃ Fin N) (g : Levi k m) {i j : Fin N}
    (h : blk e i ≠ blk e j) : (leviEmb k e g : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  exact leviEmb_apply_ne k e g (by simpa using h) i j

theorem det_adLie_pairs (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    (LinearEquiv.det (adLie k N β p) : k) =
      ∏ c : α × α, if c.1 ≤ c.2 then
        ((g c.1 : GL (m c.1) k) : Matrix (m c.1) (m c.1) k).det ^ Fintype.card (m c.2) *
          ((((g c.2)⁻¹ : GL (m c.2) k)) : Matrix (m c.2) (m c.2) k).det ^ Fintype.card (m c.1)
      else 1 := by
  classical
  set P : Matrix (Fin N) (Fin N) k := ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hPdef
  set Q : Matrix (Fin N) (Fin N) k :=
    (((p : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hQdef
  have hP : P = (leviEmb k e g : Matrix (Fin N) (Fin N) k) := by rw [hPdef, hp]
  have hQ : Q = (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) := by rw [hQdef, hp, map_inv]
  let A : (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k) :=
    (((parabolicCoord k N β).symm.trans ((adLie k N β p).trans (parabolicCoord k N β))) :
      (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k))
  have hdet : (LinearEquiv.det (adLie k N β p) : k) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLie k N β p) (parabolicCoord k N β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLie k N β p ((parabolicCoord k N β).symm (Pi.single t 1)) : lieParabolic k N β) :
      Matrix (Fin N) (Fin N) k) s.1.1 s.1.2 = _
    rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]
  let κ : ParabolicIndex N β → α ×ₗ α := fun s => toLex (blk e s.1.1, blk e s.1.2)
  have hzero : ∀ s t, κ s ≠ κ t → LinearMap.toMatrix' A s t = 0 := by
    intro s t hst
    rw [hM]
    by_cases h1 : blk e s.1.1 = blk e t.1.1
    · have h2 : blk e t.1.2 ≠ blk e s.1.2 := by
        intro h2
        exact hst (by simp only [κ, h1, h2])
      rw [hQ, leviEmb_eq_zero e _ h2, mul_zero]
    · rw [hP, leviEmb_eq_zero e _ h1, zero_mul]
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := fun s t hts => hzero s t hts.ne'
  have hblock : ∀ a b : α, ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).det =
      if a ≤ b then
        ((g a : GL (m a) k) : Matrix (m a) (m a) k).det ^ Fintype.card (m b) *
          ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det ^ Fintype.card (m a)
      else 1 := by
    intro a b
    by_cases hab : a ≤ b
    · rw [if_pos hab]
      have hmem : ∀ (i : m a) (j : m b), ¬ β (e ⟨b, j⟩) < β (e ⟨a, i⟩) := by
        intro i j
        rw [hβ]
        simpa using hab
      let f : m a × m b → {t : ParabolicIndex N β // κ t = toLex (a, b)} := fun x =>
        ⟨⟨(e ⟨a, x.1⟩, e ⟨b, x.2⟩), hmem x.1 x.2⟩, by simp [κ]⟩
      have hf : Function.Bijective f := by
        constructor
        · rintro ⟨i, j⟩ ⟨i', j'⟩ h
          have h1 := congrArg (fun t => t.1.1.1) h
          have h2 := congrArg (fun t => t.1.1.2) h
          simp only [f] at h1 h2
          have h1' := e.injective h1
          have h2' := e.injective h2
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h1' h2'
          rw [h1', h2']
        · rintro ⟨⟨⟨i, j⟩, hij⟩, hκ⟩
          obtain ⟨⟨a', i⟩, rfl⟩ := e.surjective i
          obtain ⟨⟨b', j⟩, rfl⟩ := e.surjective j
          have h3 : a' = a ∧ b' = b := by simpa [κ] using hκ
          obtain ⟨rfl, rfl⟩ := h3
          exact ⟨(i, j), rfl⟩
      rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf)]
      have hk : ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).submatrix
          (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
          Matrix.kroneckerMap (· * ·) ((g a : GL (m a) k) : Matrix (m a) (m a) k)
            ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).transpose := by
        ext ⟨i, j⟩ ⟨i', j'⟩
        show LinearMap.toMatrix' A (f (i, j)).1 (f (i', j')).1 = _
        rw [hM, hP, hQ]
        show (leviEmb k e g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, i'⟩) *
          (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) (e ⟨b, j'⟩) (e ⟨b, j⟩) = _
        rw [leviEmb_apply_same, leviEmb_apply_same]
        rfl
      rw [hk, Matrix.det_kronecker, Matrix.det_transpose]
    · rw [if_neg hab]
      have : IsEmpty {t : ParabolicIndex N β // κ t = toLex (a, b)} := by
        refine ⟨fun t => hab ?_⟩
        have h3 : blk e t.1.1.1 = a ∧ blk e t.1.1.2 = b := by simpa [κ] using t.2
        have h4 := t.1.2
        rw [hβ, h3.1, h3.2] at h4
        exact not_lt.1 h4
      exact Matrix.det_isEmpty
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun c _ hc => by
    have : IsEmpty {t : ParabolicIndex N β // κ t = c} :=
      ⟨fun t => hc (Finset.mem_image.2 ⟨t.1, Finset.mem_univ _, t.2⟩)⟩
    exact Matrix.det_isEmpty)]
  rw [← Equiv.prod_comp toLex]
  exact Finset.prod_congr rfl fun c _ => hblock c.1 c.2

theorem det_adLie_levi (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    LinearEquiv.det (adLie k N β p) = ∏ a, Matrix.GeneralLinearGroup.det (g a) ^ modExp m a := by
  have h := prod_pairs_le (fun a => Fintype.card (m a))
    (fun a => Matrix.GeneralLinearGroup.det (g a))
  have hd : ∀ b, ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det =
      (((Matrix.GeneralLinearGroup.det (g b))⁻¹ : kˣ) : k) := fun b => by
    rw [← map_inv]
    rfl
  have hd' : ∀ a, ((g a : GL (m a) k) : Matrix (m a) (m a) k).det =
      ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) := fun a => rfl
  refine Units.ext ?_
  rw [det_adLie_pairs e β hβ p g hp]
  change _ = ((∏ a, Matrix.GeneralLinearGroup.det (g a) ^
    ((∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)) : kˣ) : k)
  rw [← h, Units.coe_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  split_ifs with hc
  · simp only [hd, hd', zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  · rfl

theorem deltaHalf_eq_sqrtModular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ),
    (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β),
    (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) →
    ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ g
  have hp : ((leviIncl (φ g) : blockUpper k N β) : GL (Fin N) k) = leviEmb k e g := hφ g
  have h := modularCharacter_blockUpper (leviIncl (φ g))
  have hs : sqrtModular k N β (leviIncl (φ g)) = ((NNReal.sqrt (MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g))))) : ℝ) : ℂ) := by
    rw [← h]
    rfl
  have hm : modulus k m g = ((MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g)))) : NNReal) : ℝ) := by
    unfold GlobalTheory.SmGL.modulus
    rw [det_adLie_levi e β hβ _ g hp, map_prod, NNReal.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_zpow, NNReal.coe_zpow]
    rfl
  rw [hs, val_deltaHalf, hm, Real.coe_sqrt]

end

end GlobalTheory.CompanionTheory.DeltaLevi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLeviStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  first | exact @GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular | exact GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular | (intros; apply GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrder
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrder
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.Twist

theorem exists_nat_labelling_blk : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  intro α _ _ N m _ _ e
  let o := (Fintype.orderIsoFinOfCardEq α rfl).symm
  refine ⟨fun x => (o (blk e x)).val, fun x y => ?_⟩
  exact Fin.lt_def.symm.trans (OrderIso.lt_iff_lt o)

end GlobalTheory.CompanionTheory.Twist
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictBlockOrderStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strict_block_order : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N), ∃ β : Fin N → ℕ, ∀ x y, β x < β y ↔ blk e x < blk e y := by
  first | exact @GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | exact GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk | (intros; apply GlobalTheory.CompanionTheory.Twist.exists_nat_labelling_blk <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquiv
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.JacquetEquiv

theorem nonempty_jacquetRep_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  intro F _ _ _ _ n γ V V' _ _ _ _ π π' φ
  let e : V ≃ₗ[ℂ] V' := φ.toLinearEquiv
  have he : ∀ g, (e : V →ₗ[ℂ] V') ∘ₗ π g = π' g ∘ₗ (e : V →ₗ[ℂ] V') := by
    intro g
    rw [Representation.Equiv.toLinearEquiv_toLinearMap]
    exact φ.toIntertwiningMap.isIntertwining' g
  have he' := LinearEquiv.isIntertwining_symm_isIntertwining he
  let f : Representation.IntertwiningMap (MonoidHom.comp π (unipotentRadical F n γ).subtype) (MonoidHom.comp π' (unipotentRadical F n γ).subtype) :=
    ⟨(e : V →ₗ[ℂ] V'), fun x => he x⟩
  let g : Representation.IntertwiningMap (MonoidHom.comp π' (unipotentRadical F n γ).subtype) (MonoidHom.comp π (unipotentRadical F n γ).subtype) :=
    ⟨(e.symm : V' →ₗ[ℂ] V), fun x => he' x⟩
  let M := Representation.Coinvariants.map _ _ f
  let M' := Representation.Coinvariants.map _ _ g
  have hMM' : M ∘ₗ M' = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.apply_symm_apply v
  have hM'M : M' ∘ₗ M = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.symm_apply_apply v
  let E := LinearEquiv.ofLinearMap (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) M M' hMM' hM'M
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro m
  apply Representation.Coinvariants.hom_ext
  ext u
  have hc : f ((π (m : GL (Fin n) F)) u) = (π' (m : GL (Fin n) F)) (f u) := LinearMap.congr_fun (he m) u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.coe_ofLinearMap, jacquetRep,
    GroundTheory.Automorphic.Parabolic.twist_apply, map_smul, GroundTheory.Automorphic.Parabolic.jacquetAction,
    MonoidHom.coe_mk, OneHom.coe_mk, GroundTheory.Automorphic.coinvariantsTranslate_mk, M,
    Representation.Coinvariants.map_mk]
  rw [hc]

end GlobalTheory.CompanionTheory.JacquetEquiv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleEquivStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_module_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  first | exact @GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv | exact GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv | (intros; apply GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationBlockCounts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationBlockCounts
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellSizes

theorem card_blk_fiber {α : Type} {N : ℕ} {m : α → Type} [DecidableEq α] [∀ i, Fintype (m i)]
    (e : (Σ i, m i) ≃ Fin N) (i : α) :
    (Finset.univ.filter fun x : Fin N => blk e x = i).card = Fintype.card (m i) := by
  have h : (Finset.univ.filter fun x : Fin N => blk e x = i) =
      (Finset.univ : Finset (m i)).map
        ⟨fun y => e ⟨i, y⟩, fun a b hab => by simpa using e.injective hab⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨(e.symm x).2, e.apply_symm_apply x⟩
    · rintro ⟨y, rfl⟩
      exact blk_apply e i y
  rw [h, Finset.card_map, Finset.card_univ]

theorem sizes_sum : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' w
  constructor
  · intro i
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e x = i)
      (t := (Finset.univ : Finset β')) (f := fun x => blk e' (w.symm x))
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    rw [← h]
    exact card_blk_fiber e i
  · intro j
    have h := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j)
      (t := (Finset.univ : Finset α)) (f := fun x => blk e x)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simp only [Finset.filter_filter] at h
    have h2 : (Finset.univ.filter fun x : Fin N => blk e' (w.symm x) = j).card =
        (Finset.univ.filter fun y : Fin N => blk e' y = j).card :=
      Finset.card_equiv w.symm (by simp)
    simp only [and_comm (a := blk e _ = _)]
    rw [← h, h2]
    exact card_blk_fiber e' j

end GlobalTheory.CompanionTheory.CellSizes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationBlockCountsStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.permutation_block_counts : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (w : Equiv.Perm (Fin N)), (∀ i, ∑ j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m i)) ∧ ∀ j, ∑ i, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = Fintype.card (m' j) := by
  first | exact @GlobalTheory.CompanionTheory.CellSizes.sizes_sum | exact GlobalTheory.CompanionTheory.CellSizes.sizes_sum | (intros; apply GlobalTheory.CompanionTheory.CellSizes.sizes_sum <;> assumption)
end
end
