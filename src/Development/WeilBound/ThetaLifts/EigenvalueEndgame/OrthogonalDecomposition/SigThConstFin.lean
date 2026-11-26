module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.HodgeTateFromSandwich
noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Notions

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}



def LocMap (om : Rep σ X W) (v : Pl F) (T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)) : Prop :=
  (∀ φ ∈ SB _, IsRapid (Y := W) (T φ)) ∧ ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → T φ₁ = fun x => T φ (x * h)

def Comes (om : Rep σ X W) (v : Pl F) (f : UA σ W.J → ℂ) : Prop :=
  ∃ (m : ℕ) (T : Fin m → ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)) (φ : Fin m → (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, LocMap om v (T i) ∧ φ i ∈ SB _) ∧ f = ∑ i, T i (φ i)

end Notions

def LocDecomp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsRapid (Y := G.W) f →
    ∀ v, X.Good v → v ≠ B.v₁ → Comes om v f ∧ Comes om' v f

def PairLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n' : ℕ) (X' : Spc F E n') (M' : Model σ X' W) (χX' χW' : Chr F E) (om' : Rep σ X' W) (r₁ s₁ : ℕ),
    IsPair B M' χX' χW' om' r₁ s₁ r' s' → n + n' = d → χW = χX / χX' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), chrW χW t (unifAt v) ≠ 1 →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, Comes om' v f → ∀ Ψ ∈ schA F _, ∀ u ∈ UAt σ X (evFin F v), ∀ g, th om μ D f Ψ (g * u) = th om μ D f Ψ g

def ThAut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, IsRapid (Y := W) f → ∀ Ψ ∈ schA F _, Continuous (th om μ D f Ψ) ∧ ∀ γ ∈ ratU σ X.J, ∀ g, th om μ D f Ψ (γ * g) = th om μ D f Ψ g

def ThZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → 1 ≤ r → 1 ≤ s → 3 ≤ n → 1 ≤ d →
    (∀ t : E →ₐ[F] Fv F B.v₁, chrW χW t ≠ 1) →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, IsRapid (Y := W) f → (∀ Ψ ∈ schA F _, ∀ g, th om μ D f Ψ g = th om μ D f Ψ 1) → ∀ Ψ ∈ schA F _, ∀ g, th om μ D f Ψ g = 0

def ThPerp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ f, IsRapid (Y := W) f → ∀ Ψ ∈ schA F _, M.Conv om Ψ → (∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g in M.dom, ‖theta om Ψ g h‖ ∂M.μ ≤ C * (ht h : ℝ) ^ k) →
    (∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ → ∀ g, th om μ D f Ψ g = 0) →
    Perp W (M.I om Ψ) f

end PositivityTheory.ThKEnd.Orth

end
end

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.LocDecompOf
section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.PairLocOf
section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.QhtUnbdd
section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.ActsOfReads
noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open GlobalTheory.SplitFlip PositivityTheory.KCo
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {n n' d : ℕ}

def SplitB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v),
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∃ ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
        Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) ∧
        (∀ g ∈ UAt σ X (evFin F v), ∃ g₀, Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)

theorem exists_inv' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) : ∃ j : (Y → ℂ) →ₗ[ℂ] (X → ℂ),
      (∀ Φ ∈ SB Y, j Φ ∈ SB X ∧ ι (j Φ) = Φ) ∧ ∀ φ ∈ SB X, j (ι φ) = φ := by
  obtain ⟨q, hq⟩ := (ι ∘ₗ (SB X).subtype).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun a b h =>
    Subtype.ext (hb.2.1 a.2 b.2 h))
  have k : ∀ φ ∈ SB X, (q (ι φ)).1 = φ := fun φ h => congrArg Subtype.val (LinearMap.congr_fun hq ⟨φ, h⟩)
  refine ⟨(SB X).subtype ∘ₗ q, fun Φ h => ⟨(q Φ).2, ?_⟩, k⟩
  obtain ⟨φ, h1, rfl⟩ := hb.2.2 h
  exact congrArg ι (k φ h1)

theorem intersection_update_fsHerm_neg_one {κ : Type} [Fintype κ] (v : Pl F) (f : SInf F κ) {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1) :
    ∃ T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), (∀ ψ, T ψ = pure f (Function.update φ v ψ)) ∧
      (∀ ψ ∈ SB _, T ψ ∈ schA F κ) ∧ ∀ S, ∀ ψ ∈ SB _, ∀ ψ₁, Acts (evFin F v) S ψ ψ₁ → S (T ψ) = T ψ₁ := by
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h2
  have m : ∀ ψ ∈ SB _, tens (evFin F v) ψ r ∈ schA F κ := fun ψ hψ => by
    rw [hr']
    refine PositivityTheory.KCo.pure_mem_schA f _ (fun u => ?_) (GlobalTheory.PureFactor.update_eventually φ v ψ h2)
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact h1 u
  exact ⟨{ toFun := fun ψ => tens (evFin F v) ψ r, map_add' := fun _ _ => funext fun _ => add_mul _ _ _
           map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }, hr', m, fun S ψ hψ ψ₁ h => h r ⟨hr, m ψ hψ⟩⟩

theorem acts_of_reads {v : Pl F} {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {S R}
    (h : Reads v ι S R) {j : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}
    (h2 : ∀ φ ∈ SB _, j (ι φ) = φ) {φ} (hφ : φ ∈ SB _) : j (R (ι φ)) ∈ SB _ ∧ Acts (evFin F v) S φ (j (R (ι φ))) := by
  obtain ⟨φ₁, a, b, c⟩ := h φ hφ
  rw [← c, h2 φ₁ a]
  exact ⟨a, b⟩

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_real (x : kˣ) (m : ℕ) : ∃ r : ℝ, 0 < r ∧ apow x ((m : ℂ) / 2) = r :=
  ⟨GlobalTheory.SplitWeil.nabs k x ^ ((m : ℝ) / 2), Real.rpow_pos_of_pos (GlobalTheory.SplitWeil.nabs_pos k x) _, by
    rw [Complex.ofReal_cpow (GlobalTheory.SplitWeil.nabs_pos k x).le]; simp [apow]⟩

theorem omB_right (ν α : kˣ →* ℂˣ) (h : GL (Fin d) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α 1 h Φ = ((α (gdet h) : ℂ) * apow (gdet h) ((n : ℂ) / 2)) • fun Y => Φ (Y * h.1) := funext fun Y => by
  simp [omB, gdet]

theorem omB_left (ν α : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α g 1 Φ = ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) • fun Y => Φ (g.1ᵀ * Y) := funext fun Y => by
  simp [omB, gdet]

theorem sb_star {A : Type} [TopologicalSpace A] {f : A → ℂ} (h : f ∈ SB A) : star f ∈ SB A :=
  ⟨h.1.comp star, h.2.comp_left (g := star) (star_zero _)⟩

end Loc

end PositivityTheory.ThKEnd.Orth

end
end

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.RapidBound
noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

section Gen

variable {G H : Type} [TopologicalSpace G] [TopologicalSpace H] [SecondCountableTopology G] [MeasurableSpace H] [BorelSpace H]
  {ν : Measure H} [IsFiniteMeasure ν] {k : G × H → ℂ}

theorem gen_cont [LocallyCompactSpace G] (hk : Continuous k)
    (hb : ∀ Ω, IsCompact Ω → ∃ K : ℝ, ∀ g ∈ Ω, ∀ h, ‖k (g, h)‖ ≤ K) : Continuous fun g => ∫ h, k (g, h) ∂ν :=
  continuous_iff_continuousAt.2 fun g₀ => by
    obtain ⟨Ω, hΩ, hg⟩ := exists_compact_mem_nhds g₀
    obtain ⟨K, hK⟩ := hb Ω hΩ
    exact continuousAt_of_dominated (bound := fun _ => K)
      (.of_forall fun g => (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (by filter_upwards [hg] with g hg using .of_forall (hK g hg)) (integrable_const _)
      (.of_forall fun h => (hk.comp (continuous_id.prodMk continuous_const)).continuousAt)

theorem gen_perp [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasure μ] (hk : Continuous k) {f : H → ℂ}
    (hf : Continuous f) (hi : ∀ h, Integrable (fun g => k (g, h)) μ) {K : ℝ} (hK : ∀ h, ‖f h‖ * ∫ g, ‖k (g, h)‖ ∂μ ≤ K)
    (z : ∀ g, ∫ h, f h * star (k (g, h)) ∂ν = 0) : ∫ h, (∫ g, k (g, h) ∂μ) * starRingEnd ℂ (f h) ∂ν = 0 := by
  have m : AEStronglyMeasurable (fun x : G × H => f x.2 * star (k x)) (μ.prod ν) :=
    ((hf.comp continuous_snd).mul hk.star).aestronglyMeasurable
  have i : Integrable (fun x : G × H => f x.2 * star (k x)) (μ.prod ν) := by
    refine (integrable_prod_iff' m).2 ⟨.of_forall fun h => (Integrable.mono (hi h) (hi h).1.star (.of_forall fun _ => (norm_star _).le)).const_mul (f h),
      .of_bound m.norm.prod_swap.integral_prod_right' K (.of_forall fun h => ?_)⟩
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simpa only [norm_mul, norm_star, integral_const_mul] using hK h
  have e := integral_integral_swap (f := fun g h => f h * star (k (g, h))) i
  simp only [z, integral_zero, integral_const_mul] at e
  have := congrArg (starRingEnd ℂ) e.symm
  rw [map_zero, ← integral_conj] at this
  rw [← this]
  refine integral_congr_ae (.of_forall fun h => ?_)
  simp only [map_mul, ← integral_conj]
  simp [mul_comm]

end Gen

theorem rapid_bound {φ : UA σ W.J → ℂ} (hφ : IsRapid (Y := W) φ) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : UA σ W.J → ℝ) (A : ℝ), (∀ γ ∈ ratU σ W.J, ∀ h, T (γ * h) = T h) →
      (∀ h, T h ≤ A * (ht h : ℝ) ^ N) → ∀ h, ‖φ h‖ * T h ≤ max A 0 * K := by
  obtain ⟨C, hC⟩ := hφ.2.2 N
  refine ⟨2 ^ N * max C 0, by positivity, fun T A hi hb h => ?_⟩
  have q1 : 1 ≤ qht h := le_ciInf fun γ => one_le_heightGL F _
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ W.J => ht (γ.1 * h))
    (lt_two_mul_self (zero_lt_one.trans_le q1))
  have h2 : (ht (γ.1 * h) : ℝ) ≤ 2 * qht h := by exact_mod_cast hγ.le
  calc _ ≤ ‖φ h‖ * (max A 0 * (2 * qht h : ℝ) ^ N) := by
        refine mul_le_mul_of_nonneg_left (hi γ γ.2 h ▸ (hb _).trans ?_) (norm_nonneg _)
        gcongr
        exact le_max_left _ _
    _ = max A 0 * (2 ^ N * (‖φ h‖ * (qht h : ℝ) ^ N)) := by ring
    _ ≤ _ := by gcongr; exact (hC h).trans (le_max_left _ _)

theorem finW (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)}
    (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) : IsFiniteMeasure (μ.restrict D) :=
  isFiniteMeasure_restrict.2 (hV F E σ hp.base.cm d _ (hE F E σ B hp.base d W _ _ (Or.inr hp.skew)).1 μ D hμ hD).ne

theorem finX (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') : IsFiniteMeasure (M.μ.restrict M.dom) :=
  isFiniteMeasure_restrict.2 (hV F E σ hp.base.cm n _ (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1 _ _ hp.good.haar hp.good.dom).ne

theorem theta_rat (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Ψ} (hΨ : Ψ ∈ schA F _) (g) :
    ∀ γ ∈ ratU σ W.J, ∀ h, theta om Ψ g (γ * h) = theta om Ψ g h := fun γ hγ h => by
  simpa using ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).2.1 1 (one_mem _) γ hγ g h

theorem th_bd (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {f} (hf : IsRapid (Y := W) f) {Ψ} (hΨ : Ψ ∈ schA F _) (b : ℝ≥0) :
    ∃ K : ℝ, ∀ g, ht g ≤ b → ∀ h, ‖f h * star (theta om Ψ g h)‖ ≤ K := by
  obtain ⟨C, k, hC⟩ := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).2.2
  obtain ⟨K, -, hK⟩ := rapid_bound hf k
  refine ⟨_, fun g hg h => (norm_mul _ _).trans_le ((norm_star (theta om Ψ g h)).symm ▸ hK (fun h => ‖theta om Ψ g h‖) (max C 0 * b ^ k)
    (fun γ hγ h => by simp only [theta_rat hB hp hΨ g γ hγ]) (fun h => (hC g h).trans ?_) h)⟩
  rw [mul_assoc, ← mul_pow]
  gcongr
  exact le_max_left _ _

theorem th_cont (hB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {f} (hf : IsRapid (Y := W) f) {Ψ} (hΨ : Ψ ∈ schA F _) :
    Continuous fun x : UA σ X.J × UA σ W.J => f x.2 * star (theta om Ψ x.1 x.2) :=
  (hf.1.comp continuous_snd).mul ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).1.star

theorem th_int (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)}
    {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {f} (hf : IsRapid (Y := W) f) {Ψ}
    (hΨ : Ψ ∈ schA F _) (g) : Integrable (fun h => f h * star (theta om Ψ g h)) (μ.restrict D) := by
  haveI := finW hE hV hp hμ hD
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  obtain ⟨K, hK⟩ := th_bd hB hp hf hΨ (ht g)
  exact .of_bound ((th_cont hB hp hf hΨ).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable K
    (.of_forall (hK g le_rfl))

theorem thAut_of (hB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) : ThAut := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp μ D hμ hD f hf Ψ hΨ
  haveI := finW hE hV hp hμ hD
  obtain ⟨lc, sc, -, -, -, -, -, hb⟩ := hG F E σ hp.base.cm n _ (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  refine ⟨gen_cont (th_cont hB hp hf hΨ) fun Ω hΩ => ?_, fun γ hγ g => integral_congr_ae (.of_forall fun h => ?_)⟩
  · obtain ⟨b, hb⟩ := hb Ω hΩ
    obtain ⟨K, hK⟩ := th_bd hB hp hf hΨ b
    exact ⟨K, fun g hg => hK g (hb g hg)⟩
  · have := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).2.1 γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    simp only [this]

theorem thPerp_of (hB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) : ThPerp := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp f hf Ψ hΨ hc ⟨C, k, hC⟩ h0 μ D hμ hD
  haveI := finW hE hV hp hμ hD
  haveI := finX hE hV hp
  haveI := (hG F E σ hp.base.cm n _ (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1).2.1
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨K, -, hK⟩ := rapid_bound hf k
  exact gen_perp ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Ψ hΨ).1 hf.1 hc
    (hK (fun h => ∫ g in M.dom, ‖theta om Ψ g h‖ ∂M.μ) C (fun γ hγ h => by simp only [theta_rat hB hp hΨ _ γ hγ]) hC) (h0 μ D hμ hD)

end PositivityTheory.ThKEnd.Orth

end
end

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst PositivityTheory.KCo
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem qht_unbdd (hE : EpsOf) (hS : SiegelAll) (hH : PositivityTheory.ThKG.Tow.PlaneHerm) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (h1 : 1 ≤ r) (h2 : 1 ≤ s) (h3 : 3 ≤ n) (b : ℝ) : ∃ g : UA σ X.J, b < qht g := by
  by_contra hn
  push Not at hn
  obtain ⟨fr, hg, -, -, -, C, k, hC⟩ := hS F E σ hB.cm n _ (hE F E σ B hB n X _ _ (Or.inl hX)).1
  have hr : 0 < fr.r := Nat.pos_of_ne_zero fun h0 => by
    obtain ⟨Y', Y₁, H, -, -, hA⟩ := hH F E σ B hB n (n - 2) (by omega) (by omega) X r s h1 h2 hX 0 1 one_pos (by omega)
    have := hA.xy
    rw [hg.aniso H.x (fun i => absurd i.2 (by omega)) hA.xx] at this
    simp [form] at this
  let A := max C 0 * (b + 1) ^ k
  have ht' : (fun _ => |A|) ∈ Cone fr.r := ⟨antitone_const, fun _ => abs_nonneg _⟩
  have b0 : 0 ≤ b := (NNReal.coe_nonneg _).trans (hn 1)
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (f := fun γ : ratU σ X.J => ht (γ.1 * fr.a fun _ => |A|))
    (b := qht (fr.a fun _ => |A|) + 1) (lt_add_one _)
  have e1 : (ht (γ.1 * fr.a fun _ => |A|) : ℝ) ≤ b + 1 := by
    have := hn (fr.a fun _ => |A|)
    have h' : (ht (γ.1 * fr.a fun _ => |A|) : ℝ) < qht (fr.a fun _ => |A|) + 1 := by exact_mod_cast hγ
    linarith
  have e2 : Real.exp (∑ _i : Fin fr.r, |A|) ≤ A := ((hC _ ht').2 γ γ.2).trans (by
    simp only [A]
    gcongr
    exact le_max_left _ _)
  have e3 : |A| ≤ ∑ _i : Fin fr.r, |A| := Finset.single_le_sum (fun _ _ => abs_nonneg A) (Finset.mem_univ ⟨0, hr⟩)
  linarith [Real.add_one_le_exp (∑ _i : Fin fr.r, |A|), le_abs_self A]

theorem th_left (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)) (f) (Ψ : Fn F n d) (g u : UA σ X.J) :
    th om μ D f (om (u, 1) Ψ) g = th om μ D f Ψ (g * u) := by
  simp only [th, pet, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem th_add (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)}
    {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {f} (hf : IsRapid (Y := W) f) {Φ Ψ}
    (hΦ : Φ ∈ schA F _) (hΨ : Ψ ∈ schA F _) (g) : th om μ D f (Φ + Ψ) g = th om μ D f Φ g + th om μ D f Ψ g := by
  simp only [th, pet, theta_add hp hΦ hΨ, star_add, mul_add]
  exact integral_add (th_int hB hE hV hp hμ hD hf hΦ g) (th_int hB hE hV hp hμ hD hf hΨ g)

theorem th_smul (hp : IsPair B M χX χW om r s r' s') (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)) (f) (c : ℂ) {Ψ}
    (hΨ : Ψ ∈ schA F _) (g) : th om μ D f (c • Ψ) g = star c * th om μ D f Ψ g := by
  simp only [th, pet, theta_smul hp c hΨ, star_mul', ← integral_const_mul, mul_left_comm]

theorem thZero_of (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hS : SiegelAll) (hSo : SoDecay) (hF : SoFin)
    (hH : PositivityTheory.ThKG.Tow.PlaneHerm) (hDi : DictSt) : ThZero := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp h1 h2 h3 h4 hν μ D hμ hD f hf hc
  haveI := finW hE hV hp hμ hD
  have so : ∀ Ψ ∈ M.So B.ψ B.τ₁, th om μ D f Ψ 1 = 0 := fun Ψ hΨ => by
    have s₁ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.2.1 Ψ hΨ
    obtain ⟨C, k, hC⟩ := hSo F E σ B n d X W M χX χW om r s r' s' hp Ψ hΨ 1
    obtain ⟨K, -, hK⟩ := rapid_bound hf k
    by_contra h0
    have p0 := norm_pos_iff.2 h0
    obtain ⟨g, hg⟩ := qht_unbdd hE hS hH hp.base hp.herm h1 h2 h3 (max C 0 * K * (μ.restrict D).real Set.univ / ‖th om μ D f Ψ 1‖)
    rw [div_lt_iff₀' p0, ← hc Ψ s₁ g] at hg
    refine hg.not_ge ?_
    have : ‖∫ h in D, f h * star (theta om Ψ g h) * ((qht g : ℝ) : ℂ) ∂μ‖ ≤ max C 0 * K * (μ.restrict D).real Set.univ :=
      norm_integral_le_of_norm_le_const (.of_forall fun h => by
        rw [norm_mul, norm_mul, norm_star, mul_assoc, Complex.norm_real, NNReal.norm_eq]
        exact hK (fun h => ‖theta om Ψ g h‖ * qht g) C (fun γ hγ h => by simp only [theta_rat hB hp s₁ g γ hγ])
          (fun h => by simpa using hC g h) h)
    rwa [integral_mul_const, norm_mul, Complex.norm_real, NNReal.norm_eq] at this
  let K : Submodule ℂ (Fn F n d) :=
    { carrier := {Ψ | Ψ ∈ schA F _ ∧ th om μ D f Ψ 1 = 0}
      add_mem' := fun a b => ⟨add_mem a.1 b.1, by rw [th_add hB hE hV hp hμ hD hf a.1 b.1, a.2, b.2, add_zero]⟩
      zero_mem' := ⟨zero_mem _, so 0 (zero_mem _)⟩
      smul_mem' := fun c _ a => ⟨Submodule.smul_mem _ c a.1, by rw [th_smul hp μ D f c a.1, a.2, mul_zero]⟩ }
  refine fun Ψ hΨ g => (hc Ψ hΨ g).trans (schA_le K (fun f₀ φ p1 p2 => ?_) hΨ).2
  obtain ⟨⟨ι, hι⟩, ν, α, u1, -, n1, hd⟩ := hDi F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.good hp.weil
    hp.hX hp.hW B.v₁ B.τ₁
  obtain ⟨φ₀, s₀, f0, a0⟩ := exists_full surjectivity_statement hι.bij (hd ι hι) u1
    (fun e => (n1 (by omega) h4 e).elim (hν _) (hν _)) (p1 B.v₁)
  obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one B.v₁ f₀ p1 p2
  have k1 : augAt om B.v₁ ≤ K.comap T := Submodule.span_le.2 (by
    rintro _ ⟨u, -, ψ, hψ, ψ₁, hψ₁, hA, rfl⟩
    refine ⟨t2 _ (sub_mem hψ₁ hψ), ?_⟩
    rw [map_sub, sub_eq_add_neg, ← neg_one_smul ℂ (T ψ), th_add hB hE hV hp hμ hD hf (t2 _ hψ₁) (Submodule.smul_mem _ _ (t2 _ hψ)),
      th_smul hp μ D f _ (t2 _ hψ), ← t3 _ _ hψ _ hA, th_left, hc _ (t2 _ hψ)]
    simp)
  have k2 : T φ₀ ∈ K := ⟨t2 _ s₀, so _ (Submodule.subset_span ⟨f₀, _, fun w => by
    by_cases hw : w = B.v₁
    · subst hw; rwa [Function.update_self]
    · rw [Function.update_of_ne hw]; exact p1 w, by
      filter_upwards [p2, hp.good.std, eventually_cofinite_ne B.v₁] with w h h' hw using
        (Function.update_of_ne hw _ _).trans (h.trans h'.symm), by
      rw [Function.update_self]; exact ⟨s₀, ι, hι, f0.2⟩, t1 φ₀⟩)⟩
  have := add_mem (k1 a0) k2
  rwa [Submodule.mem_comap, sub_add_cancel, t1, Function.update_eq_self] at this

end PositivityTheory.ThKEnd.Orth

end
end

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst GlobalTheory.SplitFlip PositivityTheory.KCo
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

variable {n' : ℕ} {X' : Spc F E n'}

theorem inv_loc₂ (hL : LocDist) (e : Fin n ⊕ Fin n' ≃ Fin d) {v : Pl F} {om : Rep σ X W} {om' : Rep σ X' W}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
    {ι' : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n') (Fin d) (Fv F v) → ℂ)}
    (b : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (b' : Set.BijOn ι' (SB (Fin n' × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n') (Fin d) (Fv F v)) : Set _))
    {ν ν' α α' : (Fv F v)ˣ →* ℂˣ} (n1 : ∀ x, ‖(ν x : ℂ)‖ = 1) (n2 : ∀ x, ‖(α x : ℂ)‖ = 1) (hν : ∀ x, ν x = α x / α' x)
    (hne : ν (unifAt v) ≠ 1) (L : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ)
    (hh : ∀ h₀, ∃ h, Reads v ι (om (1, h)) (omB ν α 1 h₀) ∧ Reads v ι' (om' (1, h)) (omB ν' α' 1 h₀) ∧
      ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → ∀ Ψ ∈ schA F _, L φ₁ (om (1, h) Ψ) = L φ Ψ)
    {u g₀} (hu : Reads v ι (om (u, 1)) (omB ν α g₀ 1)) : ∀ φ' ∈ SB _, ∀ Ψ ∈ schA F _, L φ' (om (u, 1) Ψ) = L φ' Ψ := by
  obtain ⟨j, j1, j2⟩ := exists_inv' b
  obtain ⟨j', j1', j2'⟩ := exists_inv' b'
  intro φ' p1' Ψ hΨ
  refine schA_le (LinearMap.eqLocus (L φ' ∘ₛₗ om (u, 1)) (L φ')) (fun f φ p1 p2 => ?_) hΨ
  obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 p2
  let N : (Fv F v)ˣ →* ℂˣ := MonoidHom.toHomUnits ⟨⟨fun x => apow x ((d : ℂ) / 2), apow_one _⟩, fun x y => apow_mul x y _⟩
  have hN : ∀ x, ((ν * N⁻¹) x : ℂ) = ν x * (apow x ((d : ℂ) / 2))⁻¹ := fun x => by simp [N]
  have cj : ∀ {z : ℂ}, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun h => (Complex.inv_eq_conj h).symm
  have cj' : ∀ (x : (Fv F v)ˣ) (m : ℕ), starRingEnd ℂ (apow x ((m : ℂ) / 2)) = apow x ((m : ℂ) / 2) := fun x m => by
    obtain ⟨r, -, h⟩ := apow_real x m
    rw [h, Complex.conj_ofReal]
  let β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun a b => L (j' b.1) (T (j (star a.1)))) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) fun _ _ _ => by simp
  let g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀.1ᵀ (by rw [Matrix.det_transpose]; exact g₀.det_ne_zero)
  have key := TC.locBil hL v e (ν * N⁻¹) (fun t ht h => hne (Units.ext ?_)) β (fun a b h₀ => ?_)
    ⟨_, sb_star (b.1 (p1 v))⟩ ⟨_, b'.1 p1'⟩ g₁
  · have k2 := t3 _ _ (p1 v) _ (acts_of_reads hu j2 (p1 v)).2
    rw [omB_left, map_smul, map_smul, t1, Function.update_eq_self] at k2
    change L _ (T (j (star fun y => star (ι (φ v) (g₀.1ᵀ * y))))) = _ * L _ (T (j (star (star _)))) at key
    rw [star_star, j2 _ (p1 v), j2' _ p1', t1 (φ v), Function.update_eq_self, hN,
      show Matrix.GeneralLinearGroup.det g₁ = gdet g₀ from Units.ext (Matrix.det_transpose _), ← Pi.star_def, star_star] at key
    change L _ (om (u, 1) _) = _
    rw [k2, map_smulₛₗ, key, map_mul, cj (n1 _), cj', smul_eq_mul]
    have := apow_ne_zero (gdet g₀) ((d : ℂ) / 2)
    field_simp
  · obtain ⟨r, hr, e1⟩ := apow_real (unifAt v) d
    rw [hN, e1, mul_inv_eq_iff_eq_mul₀ (by exact_mod_cast hr.ne'), ← Complex.ofReal_mul] at h
    have := n1 (unifAt v)
    rw [h, Complex.norm_real, Real.norm_of_nonneg (mul_pos ht hr).le] at this
    rw [h, this]; rfl
  · obtain ⟨h, r1, r2, r3⟩ := hh h₀
    have a1 := j1 _ (sb_star a.2)
    have b1 := j1' _ b.2
    have k1 := t3 _ _ a1.1 _ (acts_of_reads r1 j2 a1.1).2
    have k3 := r3 _ b1.1 _ (acts_of_reads r2 j2' b1.1).1 (acts_of_reads r2 j2' b1.1).2 _ (t2 _ a1.1)
    rw [k1, a1.2, b1.2, omB_right, omB_right] at k3
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, cj (n2 _), cj'] at k3
    have hd : (d : ℂ) / 2 = (n : ℂ) / 2 + (n' : ℂ) / 2 := by
      have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      rw [← this]; push_cast; ring
    change L (j' fun y => b.1 (y * h₀.1)) (T (j fun y => star a.1 (y * h₀.1))) = _ * L (j' b.1) (T (j (star a.1)))
    rw [← k3, hN, hν, hd, apow_add]
    have := apow_ne_zero (gdet h₀) ((n : ℂ) / 2)
    have := apow_ne_zero (gdet h₀) ((n' : ℂ) / 2)
    simp only [Units.val_div_eq_div_val]
    field_simp

theorem exists_ext {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A'] (S : Submodule ℂ A)
    (S' : Submodule ℂ A') (P : A → A' → ℂ) (h1 : ∀ a ∈ S, ∀ b ∈ S, ∀ x ∈ S', P (a + b) x = P a x + P b x)
    (h2 : ∀ (c : ℂ) a x, P (c • a) x = c * P a x) (h3 : ∀ a ∈ S, ∀ x ∈ S', ∀ y ∈ S', P a (x + y) = P a x + P a y)
    (h4 : ∀ (c : ℂ) a, ∀ x ∈ S', P a (c • x) = star c * P a x) :
    ∃ L : A →ₗ[ℂ] A' →ₛₗ[starRingEnd ℂ] ℂ, ∀ a ∈ S, ∀ x ∈ S', L a x = P a x := by
  obtain ⟨q, hq⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  obtain ⟨q', hq'⟩ := S'.subtype.exists_leftInverse_of_injective S'.ker_subtype
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a x => P (q a) (q' x))
    (fun a b x => by simpa using h1 _ (q a).2 _ (q b).2 _ (q' x).2) (fun c a x => by simpa using h2 c (q a) (q' x))
    (fun a x y => by simpa using h3 _ (q a).2 _ (q' x).2 _ (q' y).2) (fun c a x => by simpa using h4 c (q a) _ (q' x).2),
    fun a ha x hx => ?_⟩
  exact congrArg₂ P (congrArg Subtype.val (LinearMap.congr_fun hq ⟨a, ha⟩)) (congrArg Subtype.val (LinearMap.congr_fun hq' ⟨x, hx⟩))

theorem uniW (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s') :
    Countable (ratU σ W.J) ∧ ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure → μ.IsMulRightInvariant :=
  let h := hU F E σ hp.base.cm d W.J (-1) (fun i j => by simpa using hp.skew.skew i j)
    (hE F E σ B hp.base d W _ _ (Or.inr hp.skew)).1.2
  ⟨h.1, h.2.2⟩

theorem th_right (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s')
    {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {f}
    (hf : IsRapid (Y := W) f) {Ψ} (hΨ : Ψ ∈ schA F _) (g h) : th om μ D (fun x => f (x * h)) (om (1, h) Ψ) g = th om μ D f Ψ g := by
  obtain ⟨h1, h2⟩ := uniW hE hU hp
  have := h2 μ hμ
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have e : ∀ x, theta om (om (1, h) Ψ) g x = theta om Ψ g (x * h) := fun x => by
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [th, pet, e]
  exact PositivityTheory.ThKF.L2.integral_right hD (fun x => f x * star (theta om Ψ g x))
    (fun γ hγ x => by simp only [hf.2.1 γ hγ, theta_rat hB hp hΨ g γ hγ]) h

theorem th_addf (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hp : IsPair B M χX χW om r s r' s') {μ : Measure (UA σ W.J)}
    {D : Set (UA σ W.J)} (hμ : μ.IsHaarMeasure) (hD : IsFundamentalDomain (ratU σ W.J) D μ) {ι : Type} (S : Finset ι)
    {f : ι → UA σ W.J → ℂ} (hf : ∀ i, IsRapid (Y := W) (f i)) {Ψ} (hΨ : Ψ ∈ schA F _) (g) :
    th om μ D (∑ i ∈ S, f i) Ψ g = ∑ i ∈ S, th om μ D (f i) Ψ g := by
  simp only [th, pet, Finset.sum_apply, Finset.sum_mul]
  exact integral_finsetSum _ fun i _ => th_int hB hE hV hp hμ hD (hf i) hΨ g

theorem pairLoc_of (hB : ThetaBasic) (hE : EpsOf) (hV : FinVolU) (hU : PositivityTheory.ThKF.Unimod) (hL : LocDist) (hS : SplitB) :
    PairLoc := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp n' X' M' χX' χW' om' r₁ s₁ hp' hn hχ v t hne μ D hμ hD f
    ⟨m, T, φ, hT, e⟩ Ψ hΨ u hu g
  rw [e, th_addf hB hE hV hp hμ hD _ (fun i => (hT i).1.1 _ (hT i).2) hΨ, th_addf hB hE hV hp hμ hD _ (fun i => (hT i).1.1 _ (hT i).2) hΨ]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨t1, t2⟩, t3⟩ := hT i
  obtain ⟨L, hLP⟩ := exists_ext (SB _) (schA F (Fin n × Fin d)) (fun a x => th om μ D (T i a) x g)
    (fun a ha b hb x hx => by
      simp only [th, pet, map_add (f := _), Pi.add_apply, add_mul]
      exact integral_add (th_int hB hE hV hp hμ hD (t1 a ha) hx g) (th_int hB hE hV hp hμ hD (t1 b hb) hx g))
    (fun c a x => by simp only [th, pet, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul])
    (fun a ha x hx y hy => th_add hB hE hV hp hμ hD (t1 a ha) hx hy g) fun c a x hx => th_smul hp μ D _ c hx g
  obtain ⟨o1, ι, b, l1, r1⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp v t
  obtain ⟨-, ι', b', -, r2⟩ := hS F E σ B n' d X' W M' χX' χW' om' r₁ s₁ r' s' hp' v t
  obtain ⟨g₀, hg₀⟩ := l1 u hu
  have pr := (IsUWeilPair.isUSplitting hp.weil).pres
  rw [← th_left, ← hLP _ t3 _ (pr _ _ hΨ), ← hLP _ t3 _ hΨ]
  refine inv_loc₂ hL (finSumFinEquiv.trans (finCongr hn)) b b' (ν' := chrW χW' t) (α' := chrW χX' t) (om' := om')
    (fun x => Circle.norm_coe _) (fun x => Circle.norm_coe _) (fun x => ?_) hne L (fun h₀ => ?_) hg₀ _ t3 Ψ hΨ
  · simp only [hχ, chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div]
  · obtain ⟨h, hh, e₀⟩ := o1 h₀
    refine ⟨h, r1 h hh h₀ e₀, r2 h hh h₀ e₀, fun a ha a₁ ha₁ hA x hx => ?_⟩
    rw [hLP _ ha₁ _ (pr _ _ hx), hLP _ ha _ hx, t2 h hh a ha a₁ ha₁ hA, th_right hB hE hU hp hμ hD (t1 a ha) hx]

end PositivityTheory.ThKEnd.Orth

end
end

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.Imports
noncomputable section

namespace PositivityTheory.ThKEnd.Orth

variable {H P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]

def vals (ρ : H → Module.End ℂ P) (c : H → Module.End ℂ Q) : Set Q :=
  {y | ∃ U : P →ₗ[ℂ] Q, (∀ h x, U (ρ h x) = c h (U x)) ∧ ∃ x, y = U x}

theorem decomp (ρ : H → Module.End ℂ P) (c : H → Module.End ℂ Q) [Nontrivial P]
    (irr : ∀ N : Submodule ℂ P, (∀ h, ∀ x ∈ N, ρ h x ∈ N) → N = ⊥ ∨ N = ⊤) (R : Submodule ℂ Q) (hR : ∀ h, ∀ x ∈ R, c h x ∈ R)
    {f : Q} (hf : f ∈ R) (hs : f ∈ Submodule.span ℂ (vals ρ c)) :
    ∃ (m : ℕ) (U : Fin m → P →ₗ[ℂ] Q) (ξ : Fin m → P), (∀ i, (∀ h x, U i (ρ h x) = c h (U i x)) ∧ ∀ x, U i x ∈ R) ∧
      f = ∑ i, U i (ξ i) := by
  classical
  let A := FreeAlgebra ℂ H
  letI : Module A P := Module.compHom P (FreeAlgebra.lift ℂ ρ).toRingHom
  letI : Module A Q := Module.compHom Q (FreeAlgebra.lift ℂ c).toRingHom
  have eP : ∀ (a : A) (x : P), a • x = FreeAlgebra.lift ℂ ρ a x := fun _ _ => rfl
  have eQ : ∀ (a : A) (x : Q), a • x = FreeAlgebra.lift ℂ c a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ A P := ⟨fun z a x => by rw [eP, eP, map_smul]; rfl⟩
  haveI : IsScalarTower ℂ A Q := ⟨fun z a x => by rw [eQ, eQ, map_smul]; rfl⟩
  haveI : IsSimpleModule A P := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases irr (N.restrictScalars ℂ) (fun h x hx => by
      simpa [eP] using N.smul_mem (FreeAlgebra.ι ℂ h) hx) with h | h
    · exact Or.inl (Submodule.restrictScalars_injective ℂ A P h)
    · exact Or.inr (Submodule.restrictScalars_injective ℂ A P h)
  let R' : Submodule A Q :=
    { R.toAddSubmonoid with
      smul_mem' := fun a x hx => by
        induction a using FreeAlgebra.induction generalizing x with
        | grade0 z => simpa [eQ] using R.smul_mem z hx
        | grade1 h => simpa [eQ] using hR h x hx
        | mul a b ha hb => rw [mul_smul]; exact ha _ (hb _ hx)
        | add a b ha hb => rw [add_smul]; exact R.add_mem (ha _ hx) (hb _ hx) }
  obtain ⟨m, z, g, rfl⟩ := Submodule.mem_span_set'.1 hs
  choose U hU x hx using fun i => (g i).2
  let V : Fin m → P →ₗ[A] Q := fun i =>
    { (U i).toAddHom with
      map_smul' := fun a y => by
        change U i (a • y) = a • U i y
        induction a using FreeAlgebra.induction generalizing y with
        | grade0 z => simp [eP, eQ]
        | grade1 h => simpa [eP, eQ] using hU i h y
        | mul a b ha hb => rw [mul_smul, mul_smul, ha, hb]
        | add a b ha hb => rw [add_smul, add_smul, map_add (f := _), ha, hb] }
  let T : (Fin m → P) →ₗ[A] Q := ∑ i, V i ∘ₗ LinearMap.proj i
  have hT : T (fun i => z i • x i) = ∑ i, z i • (g i : Q) := by
    simp only [T, LinearMap.sum_apply, hx, ← map_smul]
    rfl
  obtain ⟨C, hC⟩ := exists_isCompl (R'.comap T)
  let π := (R'.comap T).subtype ∘ₗ Submodule.linearProjOfIsCompl _ C hC
  refine ⟨m, fun i => (T ∘ₗ π ∘ₗ LinearMap.single A (fun _ => P) i).restrictScalars ℂ, fun i => z i • x i,
    fun i => ⟨fun h y => ?_, fun y => Subtype.prop (p := (· ∈ R'.comap T)) _⟩, ?_⟩
  · simpa [eP, eQ] using (T ∘ₗ π ∘ₗ LinearMap.single A (fun _ => P) i).map_smul (FreeAlgebra.ι ℂ h) y
  · have e : π (fun i => z i • x i) = fun i => z i • x i :=
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC ⟨_, show T _ ∈ R from hT ▸ hf⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, ← map_sum, LinearMap.single_apply, Finset.univ_sum_single]
    exact hT.symm.trans (congrArg T e.symm)

end PositivityTheory.ThKEnd.Orth

end
end

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst GlobalTheory.SplitFlip PositivityTheory.KCo
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem qht_le (x h : UA σ W.J) : qht x ≤ qht (x * h) * ht h⁻¹ := by
  rw [qht, qht, NNReal.iInf_mul]
  refine ciInf_mono (OrderBot.bddBelow _) fun γ => ?_
  have := heightGL_mul_le F (γ.1 * (x * h)).1 (h⁻¹).1
  rwa [← Subgroup.coe_mul, mul_assoc, mul_inv_cancel_right] at this


variable (σ W) in
def rapid : Submodule ℂ (UA σ W.J → ℂ) where
  carrier := {f | IsRapid (Y := W) f}
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl, fun _ => ⟨0, fun _ => by simp⟩⟩
  add_mem' := fun {f g} a b => ⟨a.1.add b.1, fun γ hγ x => by simp only [Pi.add_apply, a.2.1 γ hγ, b.2.1 γ hγ], fun N => by
    obtain ⟨C, hC⟩ := a.2.2 N
    obtain ⟨C', hC'⟩ := b.2.2 N
    exact ⟨C + C', fun x => (mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)).trans
      ((add_mul _ _ _).trans_le (add_le_add (hC x) (hC' x)))⟩⟩
  smul_mem' := fun c f a => ⟨a.1.const_smul c, fun γ hγ x => by simp only [Pi.smul_apply, a.2.1 γ hγ], fun N => by
    obtain ⟨C, hC⟩ := a.2.2 N
    exact ⟨‖c‖ * C, fun x => by
      rw [Pi.smul_apply, norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)⟩⟩

def rt (h : UA σ W.J) : Module.End ℂ (UA σ W.J → ℂ) := LinearMap.funLeft ℂ ℂ (· * h)

theorem rapid_rt (h : UA σ W.J) {f} (a : f ∈ rapid σ W) : rt h f ∈ rapid σ W :=
  ⟨a.1.comp (continuous_mul_const h), fun γ hγ x => by simpa only [rt, LinearMap.funLeft_apply, mul_assoc] using a.2.1 γ hγ (x * h),
    fun N => by
      obtain ⟨C, hC⟩ := a.2.2 N
      refine ⟨C * (ht h⁻¹ : ℝ) ^ N, fun x => le_trans ?_ (mul_le_mul_of_nonneg_right (hC (x * h)) (by positivity))⟩
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast qht_le x h) N) (norm_nonneg _)⟩

theorem exists_op (hD : DictSt) (hp : IsPair B M χX χW om r s r' s') {v : Pl F} (t : E →ₐ[F] Fv F v) :
    ∃ a : UAt σ W (evFin F v) → Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ), ∀ h, ∀ φ ∈ SB _, a h φ ∈ SB _ ∧
      Acts (evFin F v) (om (1, h.1)) φ (a h φ) := by
  obtain ⟨⟨ι, hι⟩, ν, α, -, -, -, hd⟩ := hD F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.good hp.weil
    hp.hX hp.hW v t
  obtain ⟨j, -, j2⟩ := exists_inv' hι.bij
  choose g hg using fun h : UAt σ W (evFin F v) => (hd ι hι).right h.1 h.2
  exact ⟨fun h => j ∘ₗ (⟨⟨omB ν α 1 (g h), fun _ _ => funext fun _ => mul_add _ _ _⟩, fun _ _ => funext fun _ => mul_left_comm _ _ _⟩ :
    _ →ₗ[ℂ] _) ∘ₗ ι, fun h φ hφ => acts_of_reads (hg h) j2 hφ⟩

theorem I_left (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d}
    (hΦ : Φ ∈ schA F _) (g₀ : UA σ X.J) : M.I om (om (g₀, 1) Φ) = M.I om Φ := by
  funext h
  obtain ⟨h1, -, h2⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j)
    (hE F E σ B hp.base n X _ _ (Or.inl hp.herm)).1.2
  have := hp.good.haar
  have := h2 _ this
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact PositivityTheory.ThKF.L2.integral_right hp.good.dom (fun g => theta om Φ g h) (fun γ hγ g => by
    simpa using ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h) g₀

theorem I_add (hp : IsPair B M χX χW om r s r' s') {Φ Ψ : Fn F n d} (a : Φ ∈ schA F _ ∧ M.Conv om Φ) (b : Ψ ∈ schA F _ ∧ M.Conv om Ψ) :
    M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := funext fun h => by
  simp only [Model.I, theta_add hp a.1 b.1, Pi.add_apply]
  exact integral_add (a.2 h) (b.2 h)

theorem I_smul' (c : ℂ) (Φ : Fn F n d) : M.I om (c • Φ) = c • M.I om Φ := funext fun h => by
  simp only [Model.I, theta, map_smul, thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left, integral_const_mul]

theorem mem_vals (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hp : IsPair B M χX χW om r s r' s') {v : Pl F}
    {P : Type} [AddCommGroup P] [Module ℂ P] {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P} (onto : (SB _).map p = ⊤)
    (ker : ∀ φ ∈ SB _, p φ = 0 → φ ∈ augAt om v) {ρ : UAt σ W (evFin F v) → Module.End ℂ P}
    (hρ : ∀ h, ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h.1)) φ φ₁ ∧ ρ h (p φ) = p φ₁)
    (S : Set (Fn F n d)) (hc : ∀ Φ ∈ Submodule.span ℂ S, Φ ∈ schA F _ ∧ M.Conv om Φ)
    (hS : ∀ Φ ∈ S, ∃ f φ, (∀ u, φ u ∈ SB _) ∧ (∀ᶠ u in cofinite, φ u = M.vac u) ∧ Φ = pure f φ ∧
      ∀ ψ ∈ SB _, pure f (Function.update φ v ψ) ∈ S) :
    ∀ Φ ∈ Submodule.span ℂ S, M.I om Φ ∈ Submodule.span ℂ (vals ρ fun h => rt h.1) := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | zero => rw [← zero_smul ℂ (0 : Fn F n d), I_smul', zero_smul]; exact zero_mem _
  | add x y a b ha hb => rw [I_add hp (hc x a) (hc y b)]; exact add_mem ha hb
  | smul c x a ha => rw [I_smul']; exact Submodule.smul_mem _ c ha
  | mem Φ h =>
    obtain ⟨f, φ, p1, p2, rfl, p3⟩ := hS Φ h
    obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 ((p2.and hp.good.std).mono fun _ h => h.1.trans h.2)
    have c : ∀ ψ ∈ SB _, T ψ ∈ schA F _ ∧ M.Conv om (T ψ) := fun ψ hψ => hc _ (Submodule.subset_span (t1 ψ ▸ p3 ψ hψ))
    let J : SB (Fin n × Fin d → Fv F v) →ₗ[ℂ] (UA σ W.J → ℂ) :=
      { toFun := fun ψ => M.I om (T ψ)
        map_add' := fun a b => by rw [Submodule.coe_add, map_add (f := _), I_add hp (c _ a.2) (c _ b.2)]
        map_smul' := fun z a => by rw [Submodule.coe_smul, map_smul, I_smul']; rfl }
    have k : augAt om v ≤ (LinearMap.ker J).map (SB _).subtype := Submodule.span_le.2 (by
      rintro _ ⟨g, -, ψ, hψ, ψ₁, hψ₁, hA, rfl⟩
      refine ⟨⟨ψ₁, hψ₁⟩ - ⟨ψ, hψ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      change M.I om (T ψ₁) = M.I om (T ψ)
      rw [← t3 _ _ hψ _ hA, I_left hB hE hU hp (t2 _ hψ)])
    obtain ⟨q, hq⟩ := (p.domRestrict (SB _)).exists_rightInverse_of_surjective (by rw [LinearMap.range_domRestrict, onto])
    have e : ∀ ψ ∈ SB _, J (q (p ψ)) = M.I om (T ψ) := fun ψ hψ => by
      have e1 : p (q (p ψ) : _) = p ψ := LinearMap.congr_fun hq _
      obtain ⟨z, hz, e2⟩ := k (ker _ (sub_mem (q (p ψ)).2 hψ) (by rw [map_sub, e1, sub_self]))
      rw [show z = q (p ψ) - ⟨ψ, hψ⟩ from Subtype.ext e2, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero] at hz
      exact hz
    refine Submodule.subset_span ⟨J ∘ₗ q, fun h x => ?_, p (φ v), ?_⟩
    · obtain ⟨ψ, hψ, rfl⟩ : x ∈ (SB _).map p := onto ▸ Submodule.mem_top
      obtain ⟨ψ₁, h₁, hA, e₁⟩ := hρ h ψ hψ
      rw [e₁, LinearMap.comp_apply, LinearMap.comp_apply, e _ hψ, e _ h₁, ← t3 _ _ hψ _ hA]
      funext x
      simp only [rt, LinearMap.funLeft_apply, Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    · rw [LinearMap.comp_apply, e _ (p1 v), t1, Function.update_eq_self]

theorem comes_of {v : Pl F} {P : Type} [AddCommGroup P] [Module ℂ P] {p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P}
    (onto : (SB _).map p = ⊤) {ρ : UAt σ W (evFin F v) → Module.End ℂ P}
    (hρ : ∀ h, ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h.1)) φ φ₁ ∧ ρ h (p φ) = p φ₁) {f}
    (hf : ∃ (m : ℕ) (U : Fin m → P →ₗ[ℂ] (UA σ W.J → ℂ)) (ξ : Fin m → P),
      (∀ i, (∀ h x, U i (ρ h x) = rt h.1 (U i x)) ∧ ∀ x, U i x ∈ rapid σ W) ∧ f = ∑ i, U i (ξ i)) : Comes om v f := by
  obtain ⟨m, U, ξ, hU, rfl⟩ := hf
  choose φ h1 h2 using fun i => (onto ▸ Submodule.mem_top : ξ i ∈ (SB _).map p)
  refine ⟨m, fun i => U i ∘ₗ p, φ, fun i => ⟨⟨fun ψ _ => (hU i).2 _, fun h hh ψ hψ ψ₁ _ hA => ?_⟩, h1 i⟩, by simp [h2]⟩
  obtain ⟨ψ₂, -, hA', e⟩ := hρ ⟨h, hh⟩ ψ hψ
  rw [action_uniqueness F _ v _ ψ hψ _ _ hA hA', LinearMap.comp_apply, ← e, (hU i).1]
  rfl

theorem upd_sb {κ : Type} [Fintype κ] {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ u, φ u ∈ SB _) {v : Pl F} {x} (hx : x ∈ SB _) (u) :
    Function.update φ v x u ∈ SB _ := by
  by_cases hu : u = v
  · subst hu; rwa [Function.update_self]
  · rw [Function.update_of_ne hu]; exact h u

theorem upd_cof {κ : Type} {φ ψ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h : ∀ᶠ u in cofinite, φ u = ψ u) (v : Pl F) (x) :
    ∀ᶠ u in cofinite, Function.update φ v x u = ψ u := by
  filter_upwards [h, eventually_cofinite_ne v] with w h hw using (Function.update_of_ne hw _ _).trans h

theorem locDecomp_of (hB : ThetaBasic) (hE : EpsOf) (hU : PositivityTheory.ThKF.Unimod) (hP : TriplePair) (hK : KDecay) (hF : SoFin) (hS : PolSch)
    (hD : DictSt) (hN : GoodNe) (h1 : KReal) (h2 : KFin) (h3 : KCoinv) : LocDecomp := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT f ⟨Φ, hΦ, Φ', hΦ', e⟩ hr v hv hv₁
  obtain ⟨p, p', -⟩ := hP F E σ B a a' G X om om' hT
  obtain ⟨R, hR⟩ := h1 F E σ B a a' G X om om' hT
  obtain ⟨Rf, hf⟩ := h2 F E σ B a a' G X om om' hT
  obtain ⟨k, k', -⟩ := (h3 F E σ B a a' G X om om' R Rf ⟨hT, hR, hf⟩).1 v hv
  obtain ⟨d1, d2⟩ := hK F E σ B a a' G X om om' hT
  obtain ⟨⟨t⟩, -⟩ := hN F E σ B a a' G X om om' hT v hv
  obtain ⟨A, hA⟩ := exists_op hD p t
  obtain ⟨A', hA'⟩ := exists_op hD p' t
  obtain ⟨q, hq⟩ := ((Rf.p v).domRestrict (SB _)).exists_rightInverse_of_surjective (by rw [LinearMap.range_domRestrict, hf.onto v])
  let ρ : UAt σ G.W (evFin F v) → Module.End ℂ (Rf.Pi v) := fun h => Rf.p v ∘ₗ A h ∘ₗ (SB _).subtype ∘ₗ q
  have r' : ∀ h, ∀ φ ∈ SB _, ρ h (Rf.p' v φ) = Rf.p' v (A' h φ) := fun h φ hφ =>
    hf.equiv v h.1 h.2 _ (q _).2 φ hφ _ (hA h _ (q _).2).1 _ (hA' h φ hφ).1 (hA h _ (q _).2).2 (hA' h φ hφ).2 (LinearMap.congr_fun hq _)
  have r₀ : ∀ h, ∀ φ ∈ SB _, ρ h (Rf.p v φ) = Rf.p v (A h φ) := fun h φ hφ => by
    obtain ⟨ψ, hψ, e⟩ : Rf.p v φ ∈ (SB _).map (Rf.p' v) := hf.onto' v ▸ Submodule.mem_top
    rw [← e, r' h ψ hψ]
    exact (hf.equiv v h.1 h.2 φ hφ ψ hψ _ (hA h φ hφ).1 _ (hA' h ψ hψ).1 (hA h φ hφ).2 (hA' h ψ hψ).2 e.symm).symm
  have ρ1 := fun h φ hφ => (⟨_, (hA h φ hφ).1, (hA h φ hφ).2, r₀ h φ hφ⟩ :
    ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h.1)) φ φ₁ ∧ ρ h (Rf.p v φ) = Rf.p v φ₁)
  have ρ2 := fun h φ hφ => (⟨_, (hA' h φ hφ).1, (hA' h φ hφ).2, r' h φ hφ⟩ :
    ∃ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h.1)) φ φ₁ ∧ ρ h (Rf.p' v φ) = Rf.p' v φ₁)
  have := hf.nontriv v
  have key := decomp ρ (fun h => rt h.1) (fun N hN => hf.irred v N fun h hh φ hφ φ₁ _ hA₁ hm => by
      rw [action_uniqueness F _ v _ φ hφ _ _ hA₁ (hA ⟨h, hh⟩ φ hφ).2, ← r₀ _ φ hφ]
      exact hN _ _ hm) (rapid σ G.W) (fun h x hx => rapid_rt h.1 hx) hr (e ▸ sub_mem
    (mem_vals hB hE hU p (hf.onto v) (fun φ hφ => (k φ hφ).1) ρ1 _
      (fun Ψ hΨ => ⟨hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p Ψ hΨ, d1 Ψ (hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p Ψ hΨ)⟩)
      (fun _ ⟨f, a, φ, b, c, e⟩ => ⟨f, φ, b, c, e, fun ψ hψ => ⟨f, a, _, upd_sb b hψ, upd_cof c v ψ, rfl⟩⟩) Φ hΦ)
    (mem_vals hB hE hU p' (hf.onto' v) (fun φ hφ => (k' φ hφ).1) ρ2 _
      (fun Ψ hΨ => ⟨(hF F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p').2.2.1 Ψ hΨ, (d2 Ψ hΨ).2.1⟩)
      (fun _ ⟨f, φ, b, c, o, e⟩ => ⟨f, φ, b, c, e, fun ψ hψ => ⟨f, _, upd_sb b hψ, upd_cof c v ψ, by
        rwa [Function.update_of_ne hv₁.symm], rfl⟩⟩) Φ' hΦ'.2))
  exact ⟨comes_of (hf.onto v) ρ1 key, comes_of (hf.onto' v) ρ2 key⟩

end PositivityTheory.ThKEnd.Orth

end
end

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConstOf
noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst

theorem chrW_inv_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F} {χ χ' : Chr F E}
    {t : E →ₐ[F] Fv F v} {x} (h : chrW (χ / χ') t x ≠ 1) : chrW (χ' / χ) t x ≠ 1 := fun e => h (by
  simp only [chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply] at e ⊢
  rw [map_div, div_eq_one] at e ⊢
  exact e.symm)

theorem sigThConst_of (hP : TriplePair) (hN : GoodNe) (hC : ConstOfGood) (h1 : LocDecomp) (h2 : PairLoc) (h3 : ThAut) :
    SigThConst := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' hT f hf hr μ D hμ hD
  obtain ⟨p, p', -⟩ := hP F E σ B a a' G X om om' hT
  have ha' : 2 ≤ a' := by have := hT.geo.aBig; omega
  have ha : 2 ≤ a := by have := hT.geo.lt; omega
  have g : ∀ v ∉ insert B.v₁ X.T, SplitsFully E v → X.Good v ∧ v ≠ B.v₁ := fun v hv hs =>
    ⟨⟨fun h => hv (Finset.mem_insert_of_mem h), hs⟩, fun h => hv (h ▸ Finset.mem_insert_self _ _)⟩
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨c, i⟩ := h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p μ D hμ hD f hr Ψ hΨ
    refine hC F E σ B a G.V _ _ hT.base hT.geo.hV ha (insert B.v₁ X.T) _ c i fun v hv hs u hu x => ?_
    obtain ⟨⟨t⟩, ht⟩ := hN F E σ B a a' G X om om' hT v (g v hv hs).1
    exact h2 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ p' rfl rfl v t (chrW_inv_ne (ht t)) μ D hμ hD f
      (h1 F E σ B a a' G X om om' hT f hf hr v (g v hv hs).1 (g v hv hs).2).2 Ψ hΨ u hu x
  · obtain ⟨c, i⟩ := h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' μ D hμ hD f hr Ψ hΨ
    refine hC F E σ B a' G.V' _ _ hT.base hT.geo.hV' ha' (insert B.v₁ X.T) _ c i fun v hv hs u hu x => ?_
    obtain ⟨⟨t⟩, ht⟩ := hN F E σ B a a' G X om om' hT v (g v hv hs).1
    exact h2 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' _ _ _ _ _ _ _ _ p (add_comm _ _) rfl v t (ht t) μ D hμ hD f
      (h1 F E σ B a a' G X om om' hT f hf hr v (g v hv hs).1 (g v hv hs).2).1 Ψ hΨ u hu x

theorem orthIso_of (hB : ThetaBasic) (hP : TriplePair) (hW : WeilConv) (hD : DomSoU) (hF : SoFin) (hS : PolSch) (hN : GoodNe)
    (h1 : SigRapid) (h2 : SigThConst) (h3 : ThZero) (h4 : ThPerp) : OrthIso := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT f hf hc
  obtain ⟨p, p', w⟩ := hP F E σ B a a' G X om om' hT
  have hr := h1 F E σ B a a' G X om om' hT f hf hc
  have hk := h2 F E σ B a a' G X om om' hT f hf hr
  have hn := (hN F E σ B a a' G X om om' hT _ hT.chars.good).2
  have e1 := hT.geo.aBig
  have e2 := hT.geo.lt
  have e3 := hT.geo.eBig
  refine ⟨fun hp Φ hΦ => ?_, fun hq Φ hΦ => ?_⟩
  · have s := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p Φ hΦ
    obtain ⟨c1, c2⟩ := (hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p (Or.inl w)).1 Φ s
    exact h4 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p f hr Φ s c1 c2 fun μ D hμ hD =>
      h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p (by omega) hp (by omega) (by omega)
        (fun t e => chrW_inv_ne (hn t) (by rw [e]; rfl)) μ D hμ hD f hr (hk μ D hμ hD).1 Φ s
  · have s := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' Φ hΦ.1
    obtain ⟨m, f₀, φ, hφ, rfl⟩ := (hF F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p').1 Φ hΦ.2
    obtain ⟨c1, c2, -⟩ := dom_sum hB p' (dom_of_domSoU hD p') f₀ φ hφ fun i => (hφ i).1
    exact h4 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' f hr _ s c1 c2 fun μ D hμ hD =>
      h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' hq (by omega) (by omega) (by omega)
        (fun t e => hn t (by rw [Chars.ν, e]; rfl)) μ D hμ hD f hr (hk μ D hμ hD).2 _ s

end PositivityTheory.ThKEnd.Orth

end
end

noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst PositivityTheory.KCo

theorem splitB : SplitB := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t
  obtain ⟨⟨ι, hι⟩, -, h2, h3⟩ := dictionary_extended F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v t
  exact ⟨h2, ι, hι.bij, fun g hg => ⟨Matrix.GeneralLinearGroup.map (piW t) g.1, (h3 ι hι).1 g hg _ rfl⟩, (h3 ι hι).2⟩

theorem sigThConst_fin (hB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) (hP : TriplePair) (hK : KDecay) (hF : SoFin)
    (hU : PositivityTheory.ThKF.Unimod) (hS : PolSch) (hN : GoodNe) (hC : ConstOfGood) (hL : LocDist)
    (h1 : KReal) (h2 : KFin) (h3 : KCoinv) : SigThConst :=
  sigThConst_of hP hN hC (locDecomp_of hB hE hU hP hK hF hS dictionary_statement hN h1 h2 h3) (pairLoc_of hB hE hV hU hL splitB) (thAut_of hB hG hE hV)

theorem orthIso_fin (hB : ThetaBasic) (hH : PositivityTheory.ThKG.Tow.PlaneHerm) (hG : GrpTop) (hE : EpsOf) (hV : FinVolU) (hA : SiegelAll)
    (hP : TriplePair) (hW : WeilConv) (hO : SoDecay) (hU : DomSoU) (hF : SoFin) (hS : PolSch) (hN : GoodNe)
    (h1 : SigRapid) (h2 : SigThConst) : OrthIso :=
  orthIso_of hB hP hW hU hF hS hN h1 h2 (thZero_of hB hE hV hA hO hF hH dictionary_statement) (thPerp_of hB hG hE hV)

end PositivityTheory.ThKEnd.Orth

end
