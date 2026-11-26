module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRational
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DeepStep

theorem ofFn_prod_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) :
    ∀ (n : ℕ) (g : Fin n → M) (k : Fin n → ℕ), (∀ i, p (g i) (k i)) → p (List.ofFn g).prod (∑ i, k i) := by
  intro n
  induction n with
  | zero => intro g k _; simpa using h1
  | succ n ih =>
    intro g k hg
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact hmul _ _ _ _ (hg 0) (ih _ _ fun i => hg i.succ)

theorem pow_induct {M : Type} [Monoid M] (p : M → ℕ → Prop) (h1 : p 1 0)
    (hmul : ∀ a b k l, p a k → p b l → p (a * b) (k + l)) (a : M) (ha : p a 1) : ∀ n, p (a ^ n) n := by
  intro n
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hmul _ _ _ _ ih ha

section Inter

variable {F E A A' : Type} [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A']
  (ι : A →ₛₗ[algebraMap F E] A')

theorem ofFn_prod_comm : ∀ (n : ℕ) (g' : Fin n → Module.End E A') (g : Fin n → Module.End F A),
    (∀ i x, g' i (ι x) = ι (g i x)) → ∀ x, (List.ofFn g').prod (ι x) = ι ((List.ofFn g).prod x) := by
  intro n
  induction n with
  | zero => intro g' g _ x; simp
  | succ n ih =>
    intro g' g hg x
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, mul_apply_eq_comp, mul_apply_eq_comp,
      ih _ _ (fun i => hg i.succ), hg 0]

theorem pow_comm (f' : Module.End E A') (f : Module.End F A) (h : ∀ x, f' (ι x) = ι (f x)) :
    ∀ (n : ℕ) x, (f' ^ n) (ι x) = ι ((f ^ n) x) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih => intro x; rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, h, ih]

theorem mem_span_image (Y : Set A) : ∀ y ∈ Submodule.span F Y, ι y ∈ Submodule.span E (ι '' Y) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end Inter

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A]

def Up (S : Sys F A) (f : Module.End F A) (k : ℕ) : Prop := ∀ j, j + k ≤ S.T → ∀ x ∈ S.V j, f x ∈ S.V (j + k)

theorem up_one (S : Sys F A) : Up S 1 0 := fun j _ x hx => by simpa using hx

theorem up_mul (S : Sys F A) : ∀ a b k l, Up S a k → Up S b l → Up S (a * b) (k + l) := by
  intro a b k l ha hb j hj x hx
  have h1 := hb j (by omega) x hx
  have h2 := ha (j + l) (by omega) _ h1
  rw [mul_apply_eq_comp]
  have e : j + (k + l) = j + l + k := by omega
  rw [e]; exact h2

theorem up_mul_gen (S : Sys F A) (hS : S.Hyp) (u : Fin S.N → F) : Up S (S.mul u) 1 := by
  intro j hj x hx
  have := (GlobalTheory.T.productOfVectorMultiplications_mem_filtration_lattice F A S hS j 1 hj).1 (fun _ => u) x hx
  simpa [word] using this

theorem up_pw (S : Sys F A) (hS : S.Hyp) (s : Fin S.D → Fin S.N → F) (α : Fin S.D →₀ ℕ) :
    Up S (pw S.mul s α) α.degree := by
  rw [Finsupp.degree_eq_sum]
  exact ofFn_prod_induct (Up S) (up_one S) (up_mul S) S.D _ _
    fun i => pow_induct (Up S) (up_one S) (up_mul S) _ (up_mul_gen S hS (s i)) (α i)

end GlobalTheory.HSShort.DeepStep


open GlobalTheory.HSShort.DeepStep in
theorem GlobalTheory.HSShort.deepStep_finrank : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ), FiniteDimensional E (Φ.U (S.T - S.D)) ∧ Module.finrank E (Φ.U (S.T - S.D)) = S.deepRank s ∧ S.deepRank s ≤ Module.finrank F (S.V S.T) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ
  set P : Submodule F A := ⨆ α : MonoDeg (Fin S.D) (S.T - S.D), (S.V S.D).map (pw S.mul s α.1) with hP
  have hle := hS.le_T
  have hPT : P ≤ S.V S.T := iSup_le fun α => by
    rintro _ ⟨x, hx, rfl⟩
    have h := up_pw S hS s α.1 S.D (by rw [α.2]; omega) x hx
    have e : S.D + α.1.degree = S.T := by rw [α.2]; omega
    rw [e] at h
    exact h
  haveI : FiniteDimensional F (S.V S.T) := by
    obtain ⟨r, b, -⟩ := hS.shortT
    exact Module.Finite.of_basis b
  haveI : FiniteDimensional F P := Submodule.finiteDimensional_of_le hPT
  have hdeep : S.deepRank s = Module.finrank F P := rfl
  let b := Module.finBasis F P
  let v : Fin (Module.finrank F P) → A := fun i => (b i : A)
  have hv : Submodule.span F (Set.range v) = P := by
    have : Set.range v = (P.subtype) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hli : LinearIndependent E (fun i => Φ.ι (v i)) := by
    refine Φ.indep _ (fun i => (⟨v i, hPT (b i).2⟩ : S.V S.T)) ?_
    refine LinearIndependent.of_comp (S.V S.T).subtype ?_
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hcomm : ∀ (α : Fin S.D →₀ ℕ) (x : A),
      pw Φ.mul (fun i k => algebraMap F E (s i k)) α (Φ.ι x) = Φ.ι (pw S.mul s α x) := fun α x =>
    ofFn_prod_comm Φ.ι _ _ _ (fun i y => pow_comm Φ.ι _ _ (fun z => Φ.mul_ι (s i) z) (α i) y) x
  have hU : Φ.U (S.T - S.D) = Submodule.span E (Set.range fun i => Φ.ι (v i)) := by
    rw [Φ.div]
    apply le_antisymm
    · refine iSup_le fun α => ?_
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, hcomm]
      have h1 : pw S.mul s α.1 x ∈ P := Submodule.mem_iSup_of_mem α ⟨x, hx, rfl⟩
      rw [← hv] at h1
      have h2 := mem_span_image Φ.ι _ _ h1
      rwa [← Set.range_comp] at h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hvi : v i ∈ P := (b i).2
      exact Submodule.iSup_induction (fun α : MonoDeg (Fin S.D) (S.T - S.D) => (S.V S.D).map (pw S.mul s α.1))
        (motive := fun y => Φ.ι y ∈ ⨆ α : MonoDeg (Fin S.D) (S.T - S.D),
          (Submodule.span E (Φ.ι '' S.V S.D)).map (pw Φ.mul (fun i k => algebraMap F E (s i k)) α.1)) hvi
        (fun α y hy => by
          obtain ⟨x, hx, rfl⟩ := hy
          rw [← hcomm]
          exact Submodule.mem_iSup_of_mem α (Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩)))
        (by simp only [map_zero]; exact zero_mem _)
        (fun y z hy hz => by simp only [map_add (f := _)]; exact add_mem hy hz)
  refine ⟨?_, ?_, ?_⟩
  · rw [hU]; exact FiniteDimensional.span_of_finite E (Set.finite_range _)
  · rw [hU, finrank_span_eq_card hli, Fintype.card_fin, hdeep]
  · rw [hdeep]; exact Submodule.finrank_mono hPT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDeepestFiltrationStepEqRationalStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_deepestFiltrationStep_eq_rational : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → F) (δ : ℕ) (Φ : S.Flat E A' (fun i k => algebraMap F E (s i k)) δ), FiniteDimensional E (Φ.U (S.T - S.D)) ∧ Module.finrank E (Φ.U (S.T - S.D)) = S.deepRank s ∧ S.deepRank s ≤ Module.finrank F (S.V S.T) := by
  first | exact @GlobalTheory.HSShort.deepStep_finrank | exact GlobalTheory.HSShort.deepStep_finrank | (intros; apply GlobalTheory.HSShort.deepStep_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArc
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem exists_mat_at {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mat_eq_zero {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (D : Matrix m k (AE F E)) (hD : At (evI F) D) (h0 : ∀ w, D.map (piInf (τ w)) = 0) : D = 0 := by
  ext i j
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm τ (D i j) (fun u hu => ?_) (fun w => ?_)
  · have := congrFun (congrFun (hD u hu) i) j
    simpa using this
  · have := congrFun (congrFun (h0 w) i) j
    simpa using this

theorem at_add {m k : Type} {D D' : Matrix m k (AE F E)} (hD : At (evI F) D) (hD' : At (evI F) D') :
    At (evI F) (D + D') := by
  intro u hu; rw [smul_add, hD u hu, hD' u hu, add_zero]

theorem at_mul_left {m k l : Type} [Fintype k] {D : Matrix m k (AE F E)} (hD : At (evI F) D) (N : Matrix k l (AE F E)) :
    At (evI F) (D * N) := by
  intro u hu; rw [← Matrix.smul_mul, hD u hu, Matrix.zero_mul]

theorem at_mul_right {m k l : Type} [Fintype k] {D : Matrix k l (AE F E)} (hD : At (evI F) D) (N : Matrix m k (AE F E)) :
    At (evI F) (N * D) := by
  intro u hu; rw [← Matrix.mul_smul, hD u hu, Matrix.mul_zero]

theorem at_transpose {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) : At (evI F) Dᵀ := by
  intro u hu; rw [← Matrix.transpose_smul, hD u hu, Matrix.transpose_zero]

theorem at_map_cA (σ : E →ₐ[F] E) {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) :
    At (evI F) (D.map (cA σ)) := by
  intro u hu
  ext i j
  have := congrFun (congrFun (hD u hu) i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, Matrix.map_apply] at this ⊢
  rw [← map_smul, this, map_zero]

theorem map_cA_piInf {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {m k : Type}
    (D : Matrix m k (AE F E)) : (D.map (cA σ)).map (piInf τ) = (D.map (piInf τ)).map star := by
  ext i j
  simp [GlobalTheory.RealLift.KLineProof.piInf_cA hcm]

theorem cartan_conj {n r s : ℕ} (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ) (hs : HasSig M r s) (h₁ : IsCartan M θ₁)
    (h₂ : IsCartan M θ₂) :
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  obtain ⟨A₁, hF₁, hA₁⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₁ hs h₁
  obtain ⟨A₂, hF₂, hA₂⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₂ hs h₂
  obtain ⟨A₁', h11, h12⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₁
  obtain ⟨A₂', h21, h22⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₂
  refine ⟨A₂ * A₁', A₁ * A₂', ?_, ?_, ?_⟩
  · calc A₂ * A₁' * (A₁ * A₂') = A₂ * (A₁' * A₁) * A₂' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h12, Matrix.mul_one, h21]
  · have e1 := hF₁.1
    have e2 := hF₂.1
    rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]
    calc A₁'ᵀ * A₂ᵀ * M * (A₂.map star * A₁'.map star)
        = A₁'ᵀ * (A₂ᵀ * M * A₂.map star) * A₁'.map star := by simp only [Matrix.mul_assoc]
      _ = A₁'ᵀ * (A₁ᵀ * M * A₁.map star) * A₁'.map star := by rw [e2, e1]
      _ = (A₁ * A₁')ᵀ * M * (A₁ * A₁').map star := by
          rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]; simp only [Matrix.mul_assoc]
      _ = M := by
          rw [h11, Matrix.transpose_one, Matrix.map_one _ (star_zero _) (star_one _), Matrix.one_mul, Matrix.mul_one]
  · have k1 : A₁' * θ₁ = Formalism.BasicNotions.TH.Jm r s * A₁' := by
      calc A₁' * θ₁ = A₁' * θ₁ * (A₁ * A₁') := by rw [h11, Matrix.mul_one]
        _ = A₁' * (θ₁ * A₁) * A₁' := by simp only [Matrix.mul_assoc]
        _ = (A₁' * A₁) * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [hA₁]; simp only [Matrix.mul_assoc]
        _ = Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [h12, Matrix.one_mul]
    calc A₂ * A₁' * θ₁ = A₂ * (A₁' * θ₁) := Matrix.mul_assoc _ _ _
      _ = A₂ * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [k1, Matrix.mul_assoc]
      _ = θ₂ * (A₂ * A₁') := by rw [← hA₂, Matrix.mul_assoc]

end GlobalTheory.CartanConjSkew

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

theorem conj_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have hcm := hB.cm
  have key : ∀ w, ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧
      uᵀ * X.J.map (B.emb w).1 * u.map star = X.J.map (B.emb w).1 ∧ u * X.θ w = Y.θ w * u := by
    intro w
    obtain ⟨u, v, huv, hu, hθ⟩ := cartan_conj (Complex.I • X.J.map (B.emb w).1) (X.θ w) (Y.θ w) (hX.sig w)
      (hX.cartan w) (hY.cartan w)
    refine ⟨u, v, huv, ?_, hθ⟩
    rw [Matrix.mul_smul, Matrix.smul_mul] at hu
    exact smul_right_injective _ Complex.I_ne_zero hu
  choose u v huv hu hθ using key
  obtain ⟨G, hGat, hG⟩ := exists_mat_at hcm B.emb (fun w => u w - 1)
  obtain ⟨H, hHat, hH⟩ := exists_mat_at hcm B.emb (fun w => v w - 1)
  have hmap1 : ∀ w, (1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (B.emb w)) = 1 :=
    fun w => Matrix.map_one _ (map_zero _) (map_one _)
  have hgmap : ∀ w, (1 + G).map (piInf (B.emb w)) = u w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hG]; abel
  have hhmap : ∀ w, (1 + H).map (piInf (B.emb w)) = v w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hH]; abel
  have hgh : (1 + G) * (1 + H) = 1 := by
    have h0 : (1 + G) * (1 + H) - 1 = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G) * (1 + H) - 1 = G + H + G * H := by noncomm_ring
        rw [e]; exact at_add (at_add hGat hHat) (at_mul_left hGat H)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, hgmap, hhmap, hmap1, huv, sub_self]
    exact sub_eq_zero.1 h0
  have hhg : (1 + H) * (1 + G) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hgh
  let g0 : GL (Fin n) (AE F E) := ⟨1 + G, 1 + H, hgh, hhg⟩
  have hmem : g0 ∈ UG (cA σ) (incM F X.J) := by
    show (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) = incM F X.J
    have h0 : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J =
            Gᵀ * incM F X.J + incM F X.J * G.map (cA σ) + Gᵀ * incM F X.J * G.map (cA σ) := by
          rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
        rw [e]
        exact at_add (at_add (at_mul_left (at_transpose hGat) _) (at_mul_right (at_map_cA σ hGat) _))
          (at_mul_right (at_map_cA σ hGat) _)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_cA_piInf hcm, hgmap,
          incM_map_piInf, hu, sub_self]
    exact sub_eq_zero.1 h0
  refine ⟨⟨g0, hmem⟩, ?_, fun w => ?_⟩
  · show At (evI F) ((1 + G) - 1)
    rw [add_sub_cancel_left]; exact hGat
  · show (1 + G).map (piInf (B.emb w)) * X.θ w = Y.θ w * (1 + G).map (piInf (B.emb w))
    rw [hgmap]; exact hθ w

end GlobalTheory.CartanConjSkew
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianCartanInvolutionSystemsConjugateArcStatement
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  first | exact @GlobalTheory.CartanConjSkew.conj_skew | exact GlobalTheory.CartanConjSkew.conj_skew | (intros; apply GlobalTheory.CartanConjSkew.conj_skew <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P P' : Point p v O Λ)

def mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.T →ₗ[ℤ_[p]] P'.T :=
  Tate.map p (IndepPoint.ptsHom α _)

theorem lev_mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (t : P.T) (n : ℕ) :
    (mapT P P' α t).lev n = t.lev n ≫ α := rfl

def mapV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P.V →ₗ[C] P'.V :=
  (mapT P P' α).baseChange C

variable [IsAlgClosed C] [CharZero C]

def adjT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.T →ₗ[ℤ_[p]] P.T :=
  (LinearEquiv.ofBijective _ P.pairT_bijective).symm.toLinearMap ∘ₗ (mapT P P' α).dualMap ∘ₗ pairT P'.A P'.eps

theorem pairT_adjT_left (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (t : P'.T) (s : P.T) :
    pairT P.A P.eps (adjT P P' α t) s = pairT P'.A P'.eps t (mapT P P' α s) :=
  LinearMap.congr_fun ((LinearEquiv.ofBijective _ P.pairT_bijective).apply_symm_apply
    ((mapT P P' α).dualMap (pairT P'.A P'.eps t))) s

theorem pairT_mapT (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (s : P.T) (t : P'.T) :
    pairT P'.A P'.eps (mapT P P' α s) t = pairT P.A P.eps s (adjT P P' α t) := by
  rw [← (isAlt_pairT P'.A P'.eps).neg_eq t, ← pairT_adjT_left, (isAlt_pairT P.A P.eps).neg_eq]

def adjV [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] : P'.V →ₗ[C] P.V :=
  (adjT P P' α).baseChange C

theorem adjV_tmul [Algebra ℤ_[p] C] (α : P.A.A ⟶ P'.A.A) [IsMonHom α] (c : C) (t : P'.T) :
    adjV P P' α (c ⊗ₜ t) = c ⊗ₜ adjT P P' α t := rfl

end General

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ]

def pullAct {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) :
    (StrictPull.polPull B f).OAct Λ := (exists_oAct_polPull f B o).choose

theorem eq_map_of_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y)
    (b : (Over.pullback f).obj X ⟶ (Over.pullback f).obj Y)
    (h : b.left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left) : b = (Over.pullback f).map a :=
  Over.OverMorphism.ext (pullback.hom_ext (h.trans (pullback.lift_fst _ _ _).symm)
    ((Over.w b).trans (Over.w ((Over.pullback f).map a)).symm))

theorem pullAct_act {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Out.PolAV S) (o : B.OAct Λ) (a : Λ) :
    (pullAct f B o).act a = (Over.pullback f).map (o.act a) :=
  eq_map_of_fst f _ _ ((exists_oAct_polPull f B o).choose_spec a)

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type} [CommRing R] (j : R →+* O)

def goodPoint (B : Out.PolAV (Sp R)) (o : B.OAct Λ) : Point p v O Λ :=
  ofGoodReduction hv ε (StrictPull.polPull B (spMap j)) (pullAct (spMap j) B o)

variable {B B' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ)

theorem goodPoint_oA (a : Λ) : (goodPoint hv ε j B o).oA.act a =
    (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map (o.act a)) :=
  (pullAct_act _ _ (pullAct (spMap j) B o) a).trans (congrArg _ (pullAct_act _ B o a))

def homO (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).Gt ⟶ (goodPoint hv ε j B' o').Gt :=
  (Over.pullback (spMap j)).map f

def homC (f : B.A ⟶ B'.A) : (goodPoint hv ε j B o).A.A ⟶ (goodPoint hv ε j B' o').A.A :=
  (Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homO hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap j)).map f))

instance (f : B.A ⟶ B'.A) [IsMonHom f] : IsMonHom (homC hv ε j o o' f) :=
  inferInstanceAs (IsMonHom ((Over.pullback (spMap (algebraMap O C))).map ((Over.pullback (spMap j)).map f)))

def homT (f : B.A ⟶ B'.A) [IsMonHom f] : (goodPoint hv ε j B o).T →ₗ[ℤ_[p]] (goodPoint hv ε j B' o').T :=
  mapT _ _ (homC hv ε j o o' f)

def homV [Algebra ℤ_[p] C] (f : B.A ⟶ B'.A) [IsMonHom f] :
    (goodPoint hv ε j B o).V →ₗ[C] (goodPoint hv ε j B' o').V :=
  mapV _ _ (homC hv ε j o o' f)

def homLie (f : B.A ⟶ B'.A) [IsMonHom f] (x : LieG (goodPoint hv ε j B o).Gt) : LieG (goodPoint hv ε j B' o').Gt :=
  TorusTateLie.lieMap (homO hv ε j o o' f) x

theorem lev_homT (f : B.A ⟶ B'.A) [IsMonHom f] (t : (goodPoint hv ε j B o).T) (n : ℕ) :
    (homT hv ε j o o' f t).lev n = t.lev n ≫ homC hv ε j o o' f := rfl

end Good

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def patAct {S : Scheme.{0}} (T : PAT H S) : letI := H.starRing; T.pol.OAct (𝓞 E) :=
  letI := H.starRing
  haveI : IsCommMonObj T.t.G := T.ab.comm
  ⟨T.t.act.toRingAct, fun a =>
    (GlobalTheory.RosLam.rosatiAdj_iff_lamEq GlobalTheory.firstFiveLaws.1.globalFns _ T.pol _ _ (T.t.act.hom a) (T.t.act.hom _)).2 (by
      change GlobalTheory.CM.LamEq _ _ _ _ _ (T.t.act.act (H.bar a))
      simpa [GlobalTheory.CM.LamEq] using T.t.adj a)⟩

variable {K : Type} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

abbrev patPoint (T : PAT H (Sp (𝓞 K))) : letI := H.starRing; Point ℓ v O (𝓞 E) :=
  letI := H.starRing
  goodPoint hv ε (embO hv i) T.pol (patAct T)

section Linear

variable {T T' : PAT H (Sp (𝓞 K))} {f : T.t.G ⟶ T'.t.G} (hf : Serre.IsLinearHom T.t.act T'.t.act f)

abbrev patT : letI := H.starRing; (patPoint hv ε i T).T →ₗ[ℤ_[ℓ]] (patPoint hv ε i T').T :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homT (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

abbrev patV [Algebra ℤ_[ℓ] C] : letI := H.starRing; (patPoint hv ε i T).V →ₗ[C] (patPoint hv ε i T').V :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homV (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

abbrev patLie : letI := H.starRing; LieG (patPoint hv ε i T).Gt → LieG (patPoint hv ε i T').Gt :=
  letI := H.starRing
  haveI : IsMonHom (C := Over (Sp (𝓞 K))) (M := T.pol.A) (N := T'.pol.A) f := hf.isMonHom
  homLie (B := T.pol) (B' := T'.pol) hv ε (embO hv i) (patAct T) (patAct T') f

end Linear

variable [NumberField K] {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

abbrev pointB : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i X.B

abbrev pointA (b : Bool) : letI := H.starRing; Point ℓ v O (𝓞 E) := patPoint hv ε i (X.A b)

abbrev phiV [Algebra ℤ_[ℓ] C] (k : Fin p ⊕ Fin q) :
    letI := H.starRing; (pointA hv ε i X k.isLeft).V →ₗ[C] (pointB hv ε i X).V := patV hv ε i (X.lin k)

abbrev phiLie (k : Fin p ⊕ Fin q) :
    letI := H.starRing; LieG (pointA hv ε i X k.isLeft).Gt → LieG (pointB hv ε i X).Gt := patLie hv ε i (X.lin k)

abbrev phiVP [Algebra ℤ_[ℓ] C] (a : Fin p) :
    letI := H.starRing; (pointA hv ε i X true).V →ₗ[C] (pointB hv ε i X).V :=
  patV (T := X.A true) hv ε i (X.lin (Sum.inl a))

abbrev phiVQ [Algebra ℤ_[ℓ] C] (b : Fin q) :
    letI := H.starRing; (pointA hv ε i X false).V →ₗ[C] (pointB hv ε i X).V :=
  patV (T := X.A false) hv ε i (X.lin (Sum.inr b))

end Triples

end GlobalTheory.PointMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothing
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.SmoothFinite

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def stabL (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | finRep E a k φ = φ}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

theorem height_mul_le (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖,
    by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_cptRep {φ : Sm E a} (hφ : φ.1 ∈ growth E a) (k : Kinf E a) : (cptRep E a k φ).1 ∈ growth E a := by
  intro g
  obtain ⟨C, N, hC⟩ := hφ g
  obtain ⟨B, hB, hB'⟩ := height_mul_le (Unitary.toUnits k : GL (Fin a) (Cinf E))
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N :=
      pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => ?_⟩
  change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits k))‖ ≤ _
  rw [mul_assoc, ← map_mul]
  refine (hC _).trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * Unitary.toUnits k)]) (hB' y) N) C0

theorem spanK_induction {φ : Sm E a} {p : Sm E a → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (c : ℂ) x, p x → p (c • x)) (hk : ∀ k, p (cptRep E a k φ)) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : p w := by
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hk k
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsmul c x hx

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

variable {φ : Sm E a}

theorem growth_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) : w.1 ∈ growth E a :=
  spanK_induction (p := fun w : Sm E a => w.1 ∈ growth E a) (zero_mem _)
    (fun x y hx hy => by rw [Submodule.coe_add]; exact add_mem hx hy)
    (fun c x hx => by rw [Submodule.coe_smul]; exact Submodule.smul_mem _ c hx)
    (fun k => growth_cptRep (φ := φ) hφ.growth k) hw

theorem left_mem (hφ : IsAutForm φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g :=
  spanK_induction (p := fun w : Sm E a => ∀ γ g, w.1 (ratGL E a γ * g) = w.1 g) (fun _ _ => rfl)
    (fun x y hx hy γ g => by simp [hx γ g, hy γ g])
    (fun c x hx γ g => by simp [hx γ g])
    (fun k γ g => by
      change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, hφ.left]) hw

theorem fixed_mem {k : GL (Fin a) (Af E)} (hk : k ∈ stabL φ) {w : Sm E a} (hw : w ∈ spanK E a φ) :
    finRep E a k w = w :=
  spanK_induction (p := fun w : Sm E a => finRep E a k w = w) (map_zero _)
    (fun x y hx hy => by rw [map_add (f := _), hx, hy])
    (fun c x hx => by rw [map_smul, hx])
    (fun c => by
      have hk' : finRep E a k φ = φ := hk
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk']) hw

theorem killed_mem {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (h0 : z φ = 0) {w : Sm E a}
    (hw : w ∈ spanK E a φ) : z w = 0 :=
  spanK_induction (p := fun w : Sm E a => z w = 0) (map_zero _)
    (fun x y hx hy => by rw [map_add (f := _), hx, hy, add_zero])
    (fun c x hx => by rw [map_smul, hx, smul_zero])
    (fun c => by
      rw [← Module.End.mul_apply, GlobalTheory.ZalgCpt.zalg_comm_cptRep E a c z hz, Module.End.mul_apply, h0, map_zero]) hw

variable (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] {α : Lie E a → ℂ}

theorem smoothing_add (hα : IsTest (invSet E a) α) (φ ψ : Sm E a) :
    smoothing ν α (φ + ψ).1 = smoothing ν α φ.1 + smoothing ν α ψ.1 := by
  funext x
  simp only [Pi.add_apply, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans
    (integral_add (hα.integrable_mul ν isOpen_invSet (φ.2 x).continuousOn)
      (hα.integrable_mul ν isOpen_invSet (ψ.2 x).continuousOn))
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_add]

theorem smoothing_smul (c : ℂ) (φ : Sm E a) :
    smoothing ν α (c • φ).1 = c • smoothing ν α φ.1 := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, smoothing]
  refine (integral_congr_ae (.of_forall fun y => ?_)).trans (integral_const_mul c _)
  by_cases h : IsUnit (Matrix.of y) <;> simp [chart, h, mul_left_comm]

def smoothMap (hα : IsTest (invSet E a) α) (W : Submodule ℂ (Sm E a)) : W →ₗ[ℂ] Sm E a where
  toFun w := ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩
  map_add' w w' := Subtype.ext (smoothing_add ν hα w.1 w'.1)
  map_smul' c w := Subtype.ext (smoothing_smul ν c w.1)

theorem smoothMap_mem (hα : IsTest (invSet E a) α) (hK : KInv α) (hφ : IsAutForm φ) :
    smoothMap ν hα (spanK E a φ) ∈ mapsJ φ (stabL φ) := by
  refine ⟨⟨fun k w => ?_, fun w => ⟨?_, fun γ g => ?_, fun k hk => ?_⟩⟩, fun z hz h0 w => ?_⟩
  · apply Subtype.ext; funext g
    exact GlobalTheory.T.smoothing_right_translate_maxCompact E a ν α hK w.1.1 k g
  · intro l
    obtain ⟨β, hβ, e⟩ : ∃ β, IsTest (invSet E a) β ∧
        ((l.map (lie E a)).prod (smoothMap ν hα (spanK E a φ) w)).1 = smoothing ν β w.1.1 := by
      induction l with
      | nil => exact ⟨α, hα, rfl⟩
      | cons X l ih =>
        obtain ⟨β, hβ, e⟩ := ih
        refine ⟨dens X β, isTest_dens X hβ, funext fun g => ?_⟩
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, lie_apply, e]
        exact GlobalTheory.T.lieDerivative_realLieSmoothing_eq_density E a ν β hβ w.1.1 w.1.2 X g
    rw [e]
    exact GlobalTheory.T.realLieSmoothing_mem_slowlyIncreasing E a ν β hβ w.1.1 (growth_mem hφ w.2)
  · show smoothing ν α w.1.1 (ratGL E a γ * g) = smoothing ν α w.1.1 g
    have hl := left_mem hφ w.2
    simp only [smoothing, chart, mul_assoc, hl]
  · apply Subtype.ext; funext g
    show smoothing ν α w.1.1 (g * finGL E a k) = smoothing ν α w.1.1 g
    have hw : (fun x => w.1.1 (x * finGL E a k)) = w.1.1 := congrArg Subtype.val (fixed_mem hk w.2)
    simp only [smoothing]
    rw [← chart_rt_fin, hw]
  · show (z ⟨smoothing ν α w.1.1, GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα w.1.1 w.1.2⟩) = 0
    apply Subtype.ext
    rw [GlobalTheory.T.centreEnvelopingAlgebra_commute_realLieSmoothing E a ν α hα w.1 _ z hz, killed_mem hz h0 w.2]
    funext g
    simp [smoothing, chart]

end

theorem exists_finite_space : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ →
    ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α →
      ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  intro hP E _ _ _ a ν _ φ hφ
  let w0 : spanK E a φ := ⟨φ, self_mem_spanK φ⟩
  haveI := GlobalTheory.T.finiteDimensional_centreAnnihilatorCompatibleMaps hP E a φ hφ (stabL φ) hφ.level
  refine ⟨(mapsJ φ (stabL φ)).map (LinearMap.applyₗ w0), inferInstance, ?_, fun α hα hK =>
    ⟨GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E a ν α hα φ.1 φ.2, smoothMap ν hα _, smoothMap_mem ν hα hK hφ, rfl⟩⟩
  rintro _ ⟨T, hT, rfl⟩
  exact (hT.1.2 w0).1

end GlobalTheory.AutGrowth.SmoothFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothingStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ → ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α → ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  first | exact @GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space | exact GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space | (intros; apply GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUAlphaH
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.FunObj.SqNum

theorem exists_heckeU_alphaH : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ →
    ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botSmall D i j),
      ∀ x, χ.f x = (alphaH L μ₀ i j).1 (finIdl D x) := by
  intro D T L sc μ₀ hL _ i j
  obtain ⟨χ₁, h1, -⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_of_isMu0 (N := 0) ⟨0, rfl⟩ (L.C.isMu0 j) fun g => (D.hc _).e_int j
  have hr := (ranks_exact D i j).2.1
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.Mem.Col2.SplitChar.trivial D (N := 0) ⟨0, rfl⟩)
      (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1]
    simp [alphaH, h, hL.xi_base, GlobalTheory.Mem.Col2.SplitChar.trivial]
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.AlphaSplit.etaU L.C.isEta) (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1, GlobalTheory.AlphaSplit.etaU_f]
    simp [alphaH, h, hL.xi_base]

end GlobalTheory.FunObj.SqNum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRightInvOfSpan
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem exists_rightInv_of_span {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  refine GlobalTheory.ZeroCycleHt.exists_rightInv fun v => ?_
  have hv : v ∈ Submodule.span F (Set.range w.col) := hw ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
  refine ⟨c, ?_⟩
  rw [← hc]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem htMul : HtMul := by
  intro F _ _ B N n w A Λ hL
  obtain ⟨P, hP⟩ := exists_rightInv_of_span hL.spans
  refine ⟨fun a a' G G' hG hG' ha ha' => ?_, fun c hc => ?_⟩
  · exact GlobalTheory.ZeroCycleHt.formHeight_mul 0 0 hP hL.det hG hG' ha ha'
  · have h1 : IsMultiHomogeneous (fun _ : Fin B => 0) (1 : MvPolynomial (Fin B × Fin N) F) := by
      intro t ht b
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at ht
      split_ifs at ht with h
      · subst h; simp
      · exact absurd rfl ht
    have := GlobalTheory.HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det one_ne_zero h1 hc
    rw [mul_one, GlobalTheory.ZeroCycleHt.formHeight_one] at this
    exact this

end GlobalTheory.HSShort
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorIntegralPointVacuumRootOfUnitySmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorIntegralPointVacuumRootOfUnitySmul
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

theorem vacuum_int_root_of_unity : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ),
    e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (r : GA D a), r ∈ intG D a →
    ∃ c : ℂ, (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧ W.Om r 1 e0 = c • e0 := by
  intro D δ crv a d e0 he W r hr
  obtain ⟨x, x', hx, hx', h⟩ := (GlobalTheory.NormSum.VacInt.vacuum_eigen D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ crv a d e0 he W).2.1
    r hr 1 (one_mem _)
  obtain ⟨m, hm, hxm⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D d W.chV' x).2.1 hx
  obtain ⟨m', hm', hxm'⟩ := (GlobalTheory.T.unitaryHeckeCharacter_values D a W.chV x').2.1 hx'
  refine ⟨_, ⟨m * m', Nat.mul_pos hm hm', ?_⟩, h⟩
  rw [← Units.val_pow_eq_pow_val, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm W.ep, mul_comm W.ep', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, mul_comm m m', pow_mul, hxm', one_pow, one_zpow,
    mul_comm m' m, pow_mul, hxm, one_pow, one_zpow, one_mul, Units.val_one]

end GlobalTheory.FunObj.StdDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorIntegralPointVacuumRootOfUnitySmulStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_integral_point_vacuum_rootOfUnity_smul : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (r : GA D a), r ∈ intG D a → ∃ c : ℂ, (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧ W.Om r 1 e0 = c • e0 := by
  first | exact @GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity | exact GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity | (intros; apply GlobalTheory.FunObj.StdDatum.vacuum_int_root_of_unity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDet
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatShift

theorem flat_step {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (τ : Psi H) (ρ : E →+* ℂ) (i j : ℕ) (hi : i < Dw.mult ρ) (hj : j < Dw.mult ρ) :
    (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = (wtOf Dw (flatWt Dw τ) 0).1 (ρ, j) ∧
      -1 ≤ (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) := by
  simp only [wtOf, flatWt, parWt, Datum.mult] at hi hj ⊢
  split_ifs at hi hj ⊢ <;> omega

theorem exists_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  intro E _ _ _ H Dw a n τ hD ha
  refine ⟨fun x => if x.2 < Dw.mult x.1 then ((a x : ℤ) + (wtOf Dw (flatWt Dw τ) 0).1 x).toNat else 0,
    ⟨fun ρ i j hij => ?_, hD.2⟩, fun ρ i hi => ?_, ?_⟩
  · by_cases hj : j < Dw.mult ρ
    · have hi : i < Dw.mult ρ := lt_of_le_of_lt hij hj
      have h1 : a (ρ, j) ≤ a (ρ, i) := hD.1 ρ hij
      obtain ⟨e, -⟩ := flat_step Dw τ ρ i j hi hj
      simp only [if_pos hi, if_pos hj]
      omega
    · simp only [if_neg hj]; exact Nat.zero_le _
  · have h1 := ha ρ i hi
    have h2 := (flat_step Dw τ ρ i i hi hi).2
    simp only [if_pos hi]
    omega
  · funext x
    rcases x with _ | ⟨ρ, i⟩
    · simp [exZ, wtZ, wtOf_snd]
    · have h1 := ha ρ i i.2
      have h2 := (flat_step Dw τ ρ i i i.2 i.2).2
      simp only [exZ, wtZ, Prod.fst_add, Pi.add_apply, if_pos i.2]
      omega

end GlobalTheory.FlatShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDetStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_weight_shift_flatLineDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  first | exact @GlobalTheory.FlatShift.exists_shift | exact GlobalTheory.FlatShift.exists_shift | (intros; apply GlobalTheory.FlatShift.exists_shift <;> assumption)
end
end
