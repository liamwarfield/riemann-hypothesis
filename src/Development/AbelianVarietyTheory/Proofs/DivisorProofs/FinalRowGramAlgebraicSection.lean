module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovolCong

theorem smul_mem_hat (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (S T : Set (Fin n → E)) (b : E) (hb : ∀ x ∈ S, b • x ∈ T) :
    ∀ z ∈ GlobalTheory.AdLat.hat F S, ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b) • z ∈ GlobalTheory.AdLat.hat F T := by
  intro z hz
  let φ : (Fin n → GlobalTheory.AdLat.RA F E) →+ (Fin n → GlobalTheory.AdLat.RA F E) :=
    DistribSMul.toAddMonoidHom _ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b)
  have hle : GlobalTheory.AdLat.hat F S ≤ (GlobalTheory.AdLat.hat F T).comap φ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, hb x hx, ?_⟩
    funext i
    simp only [φ, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  exact hle hz

theorem inv_smul_mem {D : D7} (V : HSp D) (I : Ideal (𝓞 D.host.E)) (b : D.host.E)
    (hb : b ∈ (D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (y : Fin V.rank → D.host.E)
    (hy : y ∈ (I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))) :
    b • y ∈ (I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    (b • LinearMap.id : (Fin V.rank → D.host.E) →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)
  have hf : (Formalism.L2.Pj.latG V 1).map f ≤ GlobalTheory.Member.latC V := by
    rw [hsub, Submodule.map_span_le]
    rintro _ ⟨a, ha, x, hx, rfl⟩
    have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [← inv_mul_cancel₀ hA]
      exact FractionalIdeal.mul_mem_mul hb ha
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hba
    have : f (a • x) = r • x := by
      simp only [f, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      rw [← hr, algebraMap_smul]
    rw [this]
    exact Submodule.smul_mem _ r hx
  have h1 : f y ∈ (I • Formalism.L2.Pj.latG V 1).map f := Submodule.mem_map_of_mem hy
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hf h1

theorem gen_mem {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E))
    (I : Ideal (𝓞 D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈
      GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)))
    (c : FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hc : ∀ v : HeightOneSpectrum (𝓞 D.host.F), c v ∈ HeightOneSpectrum.adicCompletionIntegers D.host.F v)
    (x : Fin V.rank → D.host.E) (hx : x ∈ GlobalTheory.Member.latC V) :
    K *ᵥ (fun i => c ⊗ₜ[D.host.F] x i) - (fun i => c ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E)) := by
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hsub := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.2
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hψs : ∀ (s : GlobalTheory.AdLat.RA D.host.F D.host.E) z, ψ (s • z) = s • ψ z := by
    intro s z
    simp only [ψ, AddMonoidHom.mk'_apply, Matrix.mulVec_smul, smul_sub]
  have h1 : (1 : D.host.E) ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      ((D.host.AA⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hA]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have key := Submodule.mul_induction_on (C := fun t : D.host.E => ψ (fun i => c ⊗ₜ[D.host.F] (t * x i)) ∈
      GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))) h1 ?_ ?_
  · simp only [one_mul] at key
    exact key
  · intro m hm b hb
    have hw : (fun i => c ⊗ₜ[D.host.F] (m * x i)) ∈
        GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)) := by
      refine AddSubgroup.subset_closure ⟨c, hc, m • x, ?_, rfl⟩
      rw [hsub]
      exact Submodule.subset_span ⟨m, hm, x, hx, rfl⟩
    have h2 := smul_mem_hat D.host.F _ _ b (fun y hy => inv_smul_mem V I b hb y hy) _ (h _ hw)
    have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (K *ᵥ (fun i => c ⊗ₜ[D.host.F] (m * x i)) -
        (fun i => c ⊗ₜ[D.host.F] (m * x i))) = ψ (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) := by
      have : (fun i => c ⊗ₜ[D.host.F] (m * b * x i)) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • (fun i => c ⊗ₜ[D.host.F] (m * x i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 1
        ring
      rw [this, hψs]
      rfl
    rw [← e]
    exact h2
  · intro t t' ht ht'
    have : (fun i => c ⊗ₜ[D.host.F] ((t + t') * x i)) =
        (fun i => c ⊗ₜ[D.host.F] (t * x i)) + (fun i => c ⊗ₜ[D.host.F] (t' * x i)) := by
      funext i
      simp only [Pi.add_apply, add_mul, TensorProduct.tmul_add]
    beta_reduce at ht ht' ⊢
    rw [this, AddMonoidHom.map_add ψ]
    exact (GlobalTheory.AdLat.hat _ _).add_mem ht ht'

end GlobalTheory.CovolCong


open GlobalTheory.CovolCong in
theorem GlobalTheory.CovolCong.cong_latC_of_cong_latG : ∀ {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)) (I : Ideal (𝓞 D.host.E)), (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V K I h
  let ψ : (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) →+ (Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E) :=
    AddMonoidHom.mk' (fun z => K *ᵥ z - z) (fun x y => by rw [Matrix.mulVec_add]; abel)
  have hle : GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ≤
      (GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
        Set (Fin V.rank → D.host.E))).comap ψ := by
    unfold GlobalTheory.AdLat.hat
    rw [AddSubgroup.closure_le]
    rintro _ ⟨c, hc, x, hx, rfl⟩
    exact gen_mem V K I h c hc x hx
  intro z hz
  exact hle hz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCongruenceSelfDualOfPrincipalLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCongruence_selfDual_of_principalLattice : ∀ {D : D7} (V : HSp D) (K : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E)) (I : Ideal (𝓞 D.host.E)), (∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E))) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)), K *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((I • GlobalTheory.Member.latC V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  first | exact @GlobalTheory.CovolCong.cong_latC_of_cong_latG | exact GlobalTheory.CovolCong.cong_latC_of_cong_latG | (intros; apply GlobalTheory.CovolCong.cong_latC_of_cong_latG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdeal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelMoveCong

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem intAdele_smul_mem_hat {n : ℕ} (S : Set (Fin n → E)) (c : FiniteAdeleRing (𝓞 F) F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F S) : (c ⊗ₜ[F] (1 : E)) • z ∈ GlobalTheory.AdLat.hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨c * a, fun v => mul_mem (hc v) (ha v), x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem ideal_smul_mem_hat {n : ℕ} (I : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) {t : 𝓞 E} (ht : t ∈ I)
    {z : Fin n → GlobalTheory.AdLat.RA F E} (hz : z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E)) • z ∈
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, t • x, Submodule.smul_mem_smul ht hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem nsmul_eq_smul {n : ℕ} (M : ℕ) (w : Fin n → GlobalTheory.AdLat.RA F E) :
    M • w = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((M : 𝓞 E) : E))) • w := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, map_natCast]
  rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem split_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (x y : Fin n → GlobalTheory.AdLat.RA F E)
    (r : GlobalTheory.AdLat.RA F E) (h : x = y + r • x) :
    K *ᵥ x - x = (K *ᵥ y - y) + r • (K *ᵥ x - x) := by
  conv_lhs => rw [h]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem gen_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (c : FiniteAdeleRing (𝓞 F) F)
    (x : Fin n → E) :
    K *ᵥ (fun i => c ⊗ₜ[F] x i) - (fun i => c ⊗ₜ[F] x i) =
      (c ⊗ₜ[F] (1 : E)) • (K *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x) := by
  have e : (fun i => c ⊗ₜ[F] x i) = (c ⊗ₜ[F] (1 : E)) • GlobalTheory.AdLat.fv F x := by
    funext i; simp [GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, Matrix.mulVec_smul, smul_sub]

end Gen

end GlobalTheory.LevelMoveCong

namespace GlobalTheory.LevelMoveCong

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix


set_option maxHeartbeats 2000000 in
theorem mulVec_sub_mem_hat_smul : ∀ {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), Formalism.L2.Pj.LatEmb V ι → ∀ (M : ℕ) (Mb Mh : Ideal (𝓞 D.host.E)), Mb ⊔ Mh = ⊤ → ((M : ℕ) : 𝓞 D.host.E) ∈ Mb → ∀ (κ : Formalism.L2.Theta.GA D V), GlobalTheory.Member.FinCong V 1 κ → ∀ (f : La →ₗ[𝓞 D.host.E] La), (∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ Formalism.L2.Pj.latGHat V 1, Formalism.L2.Pj.finVec V (ι (f a)) - (Formalism.L2.Theta.finHom V κ).1 *ᵥ Formalism.L2.Pj.finVec V (ι a) = M • w) → (∀ x, f x - x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), (Formalism.L2.Theta.finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((Mb • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V La _ _ ι hι M Mb Mh hsup hM κ hκ f hf hfb z hz
  set K := (Formalism.L2.Theta.finHom V κ).1 with hKdef
  set L' := Formalism.L2.Pj.latG V 1 with hL'
  set P := GlobalTheory.AdLat.hat D.host.F ((Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    Set (Fin V.rank → D.host.E)) with hP
  have hhat1 : Formalism.L2.Pj.latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  have hK : ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)),
      K *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) := by
    intro y hy
    have h4 := (GlobalTheory.Member.latG_lattice_and_completion D V κ).2.2.2.1
    have he := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hκ
    have h5 : K *ᵥ y ∈ (Formalism.L2.Pj.latGHat V κ : Set _) := by rw [h4]; exact ⟨y, hy, rfl⟩
    rw [he, hhat1] at h5
    exact h5
  have hone : ∀ v, (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) v ∈ v.adicCompletionIntegers D.host.F :=
    fun v => one_mem _
  have hfv : ∀ u ∈ L', Formalism.L2.Pj.finVec V u ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  have hfvP : ∀ u ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.Pj.finVec V u ∈ P :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  obtain ⟨b, hb, m, hm, hmb⟩ : ∃ b ∈ Mb, ∃ m ∈ Mh, b + m = 1 :=
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hfv_sub : ∀ u u', Formalism.L2.Pj.finVec V (u - u') = Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u' := by
    intro u u'; funext i; simp [Formalism.L2.Pj.finVec, TensorProduct.tmul_sub]
  have hrange : ∀ x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La),
      ι x ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
    intro x hx
    have h1 : ι x ∈ (Mb • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := Submodule.mem_map_of_mem hx
    rwa [Submodule.map_smul'', Submodule.map_top, hι.2] at h1

  have step1 : ∀ v : La, K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) ∈ P := by
    intro v
    obtain ⟨w, hw, hw'⟩ := hf (m • v) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have e : K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) =
        Formalism.L2.Pj.finVec V (ι (f (m • v) - m • v)) - M • w := by
      rw [map_sub, hfv_sub, ← hw']; abel
    rw [e]
    refine sub_mem (hfvP _ (hrange _ (hfb _))) ?_
    rw [hhat1] at hw
    rw [nsmul_eq_smul]
    exact ideal_smul_mem_hat Mb L' hM hw

  have step2 : ∀ u ∈ L', K *ᵥ Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u ∈ P := by
    intro u hu
    have hu' : u ∈ LinearMap.range ι := by rw [hι.2]; exact hu
    obtain ⟨v, rfl⟩ := hu'
    have hsplit : Formalism.L2.Pj.finVec V (ι v) = Formalism.L2.Pj.finVec V (ι (m • v)) +
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) •
          Formalism.L2.Pj.finVec V (ι v) := by
      funext i
      simp only [Formalism.L2.Pj.finVec, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_add]
      congr 1
      rw [Algebra.smul_def, ← add_mul]
      have : ((algebraMap (𝓞 D.host.E) D.host.E m) + (b : D.host.E)) = 1 := by
        show ((m : D.host.E)) + (b : D.host.E) = 1
        rw [add_comm]; exact_mod_cast congrArg ((↑) : 𝓞 D.host.E → D.host.E) hmb
      rw [this, one_mul]
    rw [split_sub K _ _ _ hsplit]
    refine add_mem (step1 v) (ideal_smul_mem_hat Mb L' hb ?_)
    have hu : ι v ∈ L' := by rw [hL', ← hι.2]; exact ⟨v, rfl⟩
    exact sub_mem (hK _ (hfv _ hu)) (hfv _ hu)

  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    rw [gen_sub K c x]
    exact intAdele_smul_mem_hat _ c hc (step2 x hx)
  | zero => rw [Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add y y' _ _ h h' =>
    have e : K *ᵥ (y + y') - (y + y') = (K *ᵥ y - y) + (K *ᵥ y' - y') := by
      rw [Matrix.mulVec_add]; abel
    rw [e]; exact add_mem h h'
  | neg y _ h =>
    have e : K *ᵥ (-y) - (-y) = -(K *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [e]; exact neg_mem h

end GlobalTheory.LevelMoveCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdealStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMove_lift_congruent_mod_ideal : ∀ {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), Formalism.L2.Pj.LatEmb V ι → ∀ (M : ℕ) (Mb Mh : Ideal (𝓞 D.host.E)), Mb ⊔ Mh = ⊤ → ((M : ℕ) : 𝓞 D.host.E) ∈ Mb → ∀ (κ : Formalism.L2.Theta.GA D V), GlobalTheory.Member.FinCong V 1 κ → ∀ (f : La →ₗ[𝓞 D.host.E] La), (∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ Formalism.L2.Pj.latGHat V 1, Formalism.L2.Pj.finVec V (ι (f a)) - (Formalism.L2.Theta.finHom V κ).1 *ᵥ Formalism.L2.Pj.finVec V (ι a) = M • w) → (∀ x, f x - x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), (Formalism.L2.Theta.finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((Mb • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  first | exact @GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul | exact GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul | (intros; apply GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR

theorem hatL_cong_of_hat {D : D7} (V : HSp D) (κ : GA D V) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)),
      (finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F (Λ' : Set (Fin V.rank → D.host.E))) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V κ).1 *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ' := by
  intro z hz
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ' _ (h _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ z hz))
  have e : (Lev.finE V κ).1 = (finHom V κ).1.map (Algebra.TensorProduct.comm D.host.F _ D.host.E) := rfl
  convert h1 using 1
  funext j
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.sub_apply, map_sub, Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply,
    Matrix.map_apply]

end GlobalTheory.BaseLevelInj
