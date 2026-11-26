module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharEqOfSplitOfTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletion
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresBasic

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem coef_inv (f : S.Forms) (c : S.Cl) (g : stab ι J (P.y c)) :
    (χ (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef ((f : S.Cl → S.V) c)) = P.coef ((f : S.Cl → S.V) c) := by
  obtain ⟨g, rfl⟩ := (P.stabI c).surjective g
  rw [← P.coef_act, f.2 c g]

theorem ext_dec (f : S.Forms) (γ : Γ) (c : S.Cl) (k : J) :
    P.ext (f : S.Cl → S.V) (ι γ * P.y c * k) = (χ k : ℂ) • ρ γ (P.coef ((f : S.Cl → S.V) c)) := by
  have hs := P.dec_spec (ι γ * P.y c * k)
  have hc : P.decC (ι γ * P.y c * k) = c :=
    (P.reps (ι γ * P.y c * k)).unique ⟨_, _, hs⟩ ⟨γ, k, rfl⟩
  unfold ClassPres.ext
  rw [hc] at hs ⊢
  generalize P.decG (ι γ * P.y c * k) = γ' at hs ⊢
  generalize P.decK (ι γ * P.y c * k) = k' at hs ⊢
  have e : (P.y c)⁻¹ * ι (γ⁻¹ * γ') * P.y c = (k : G) * (k' : G)⁻¹ := by
    have h2 : ι γ' = ι γ * P.y c * k * (k' : G)⁻¹ * (P.y c)⁻¹ := by rw [hs]; group
    rw [map_mul, map_inv, h2]; group
  have hm : γ⁻¹ * γ' ∈ stab ι J (P.y c) := by
    rw [mem_stab, e]; exact J.mul_mem k.2 (J.inv_mem k'.2)
  have hk : stabK ι (⟨_, hm⟩ : stab ι J (P.y c)) = k' * k⁻¹ := by
    apply Subtype.ext
    simp only [stabK]
    rw [e]; simp
  have hi := coef_inv P f c ⟨_, hm⟩
  rw [hk] at hi
  conv_rhs => rw [← hi]
  rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul]
  congr 1
  · rw [map_mul, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, inv_mul_cancel_right]
  · simp

theorem ext_y (f : S.Forms) (c : S.Cl) :
    P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c) := by
  have := ext_dec P f 1 c 1
  simpa using this

theorem extMem : P.ExtMem := by
  intro f γ h k
  obtain ⟨c, ⟨γ', k', rfl⟩, -⟩ := P.reps h
  have e : ι γ * (ι γ' * P.y c * k') * k = ι (γ * γ') * P.y c * (k' * k : J) := by
    simp [mul_assoc]
  rw [e, ext_dec, ext_dec, map_mul, map_mul, map_smul, smul_smul, Units.val_mul, mul_comm]
  rfl

theorem isom : P.Isom := by
  intro f f'
  unfold adInner CSD.csum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ext_y, ext_y, P.coef_pair, map_mul, map_inv₀, map_natCast, CSD.wt,
    ← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card]

def bW : Module.Basis S.ιV ℂ W := Module.Basis.mk P.coef_li (by rw [P.coef_span])

theorem bW_apply (j : S.ιV) : bW P j = P.coef (S.bV j) := by simp [bW]

theorem repr_coef (x : S.V) (j : S.ιV) : (bW P).repr (P.coef x) j = σ (S.bV.repr x j) := by
  have : P.coef x = ∑ i, σ (S.bV.repr x i) • bW P i := by
    conv_lhs => rw [← S.bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ, bW_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem coef_injective : Function.Injective P.coef := by
  intro x x' h
  apply S.bV.repr.injective
  ext j
  apply σ.injective
  rw [← repr_coef P, ← repr_coef P, h]

theorem extL_injective : Function.Injective P.extL := by
  intro f f' h
  apply Subtype.ext
  funext c
  apply coef_injective P
  rw [← ext_y, ← ext_y]
  exact congrFun h _

theorem eq_of_reps {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ)
    (h : ∀ c, F (P.y c) = F' (P.y c)) : F = F' := by
  funext g
  obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
  rw [hF γ _ k, hF' γ _ k, h]

theorem ext_li : LinearIndependent ℂ (fun i => P.extL (S.basis i)) := by
  letI : Algebra K ℂ := σ.toAlgebra
  let Φ : S.Forms →ₗ[K] (S.Cl × S.ιV → K) :=
    { toFun := fun f p => S.bV.repr ((f : S.Cl → S.V) p.1) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro f f' h
    apply Subtype.ext
    funext c
    apply S.bV.repr.injective
    ext j
    exact congrFun h (c, j)
  have h1 := S.basis.linearIndependent.map' Φ hΦ
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  let Ψ : (G → W) →ₗ[ℂ] (S.Cl × S.ιV → ℂ) :=
    { toFun := fun F p => (bW P).repr (F (P.y p.1)) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  refine LinearIndependent.of_comp Ψ ?_
  have e : (⇑Ψ ∘ fun i => P.extL (S.basis i)) = fun i => ⇑(algebraMap K ℂ) ∘ (⇑Φ ∘ ⇑S.basis) i := by
    funext i p
    show (bW P).repr (P.ext _ (P.y p.1)) p.2 = σ (S.bV.repr ((S.basis i : S.Cl → S.V) p.1) p.2)
    rw [ext_y, repr_coef]
  rw [e]
  exact h2

open Classical in
def avgForm (S : CSD K) (c : S.Cl) (x : S.V) : S.Forms :=
  ⟨Pi.single c (∑ g : S.Gam c, S.ρ c g x), by
    intro c' γ
    by_cases h : c' = c
    · subst h
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Pi.single_eq_same, map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft γ) _ _ fun _ => rfl
    · simp [Pi.single_eq_of_ne h]⟩

theorem ext_span : Submodule.span ℂ (Set.range P.extL) = AdForms ι ρ J χ := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact extMem P f
  · intro F hF
    have hmem : ∀ M : Submodule ℂ (G → W), (∀ f, P.extL f ∈ M) →
        (∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j))) ∈ M := fun M hM =>
      M.sum_mem fun c _ => M.sum_mem fun j _ => M.smul_mem _ (hM _)
    have key : F = ∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j)) := by
      refine eq_of_reps P hF (hmem _ (extMem P)) fun c => ?_
      simp only [Finset.sum_apply, Pi.smul_apply, ClassPres.extL_apply, ext_y]
      rw [Finset.sum_eq_single c]
      · have hg : ∀ g : S.Gam c, ∑ j, (bW P).repr (F (P.y c)) j • P.coef (S.ρ c g (S.bV j)) = F (P.y c) := by
          intro g
          have h1 := hF (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
          rw [stabK_spec] at h1
          conv_rhs => rw [h1, ← (bW P).sum_repr (F (P.y c))]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [P.coef_act, map_sum, map_smul, Finset.smul_sum, bW_apply]
          exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [avgForm, Pi.single_eq_same, map_sum, mul_smul, ← Finset.smul_sum]
        simp only [Finset.smul_sum (s := (Finset.univ : Finset (S.Gam c)))]
        rw [Finset.sum_comm]
        simp only [hg, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
        exact_mod_cast Fintype.card_ne_zero
      · intro c' _ hc
        simp [avgForm, Pi.single_eq_of_ne (Ne.symm hc)]
      · simp
    rw [key]
    exact hmem _ fun f => Submodule.subset_span ⟨f, rfl⟩

end GlobalTheory.PresBasic

namespace GlobalTheory

theorem classPres_basic : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.Isom ∧ P.ExtBij ∧ (∀ (f : S.Forms) c, P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c)) ∧ Function.Injective P.extL :=
  fun _ _ _ _ _ _ P => ⟨PresBasic.extMem P, PresBasic.isom P, ⟨PresBasic.ext_li P, PresBasic.ext_span P⟩,
    PresBasic.ext_y P, PresBasic.extL_injective P⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalFamilyOrthogonalDecomposition
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory

namespace NormalFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem adjoint_apply_eq_zero {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) {v : E}
    (hv : S v = 0) : LinearMap.adjoint S v = 0 := by
  have e : S (LinearMap.adjoint S v) = LinearMap.adjoint S (S v) := LinearMap.congr_fun h.eq v
  rw [← inner_self_eq_zero (𝕜 := ℂ), LinearMap.adjoint_inner_right, e, hv, map_zero, inner_zero_left]

theorem apply_eq_zero_of_pow {S : Module.End ℂ E} (h : Commute S (LinearMap.adjoint S)) (k : ℕ) {v : E}
    (hv : (S ^ k) v = 0) : S v = 0 := by
  induction k generalizing v with
  | zero =>
    have : v = 0 := by simpa using hv
    rw [this, map_zero]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply] at hv
    have h1 := adjoint_apply_eq_zero h (ih hv)
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← LinearMap.adjoint_inner_left, h1, inner_zero_left]

theorem adjoint_sub_smul (T : Module.End ℂ E) (a : ℂ) :
    LinearMap.adjoint (T - a • (1 : Module.End ℂ E)) =
      LinearMap.adjoint T - (starRingEnd ℂ a) • (1 : Module.End ℂ E) := by
  rw [map_sub, LinearEquiv.map_smulₛₗ]
  congr 2
  exact star_one (Module.End ℂ E)

theorem commute_sub_smul {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    Commute (T - a • (1 : Module.End ℂ E)) (LinearMap.adjoint (T - a • (1 : Module.End ℂ E))) := by
  rw [adjoint_sub_smul]
  exact (h.sub_right ((Commute.one_right T).smul_right _)).sub_left ((Commute.one_left _).smul_left a)

theorem maxGenEigenspace_eq {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) (a : ℂ) :
    T.maxGenEigenspace a = T.eigenspace a := by
  ext v
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_eigenspace_iff]
  constructor
  · rintro ⟨k, hk⟩
    have := apply_eq_zero_of_pow (commute_sub_smul h a) k hk
    simpa [sub_eq_zero] using this
  · intro hv
    exact ⟨1, by simp [hv]⟩

theorem eigenspace_isOrtho {T : Module.End ℂ E} (h : Commute T (LinearMap.adjoint T)) {a b : ℂ}
    (hab : a ≠ b) : T.eigenspace a ⟂ T.eigenspace b := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro v hv w hw
  rw [Module.End.mem_eigenspace_iff] at hv hw
  have h0 : (T - a • (1 : Module.End ℂ E)) v = 0 := by simp [hv]
  have h1 := adjoint_apply_eq_zero (commute_sub_smul h a) h0
  have h2 : inner ℂ v ((T - a • (1 : Module.End ℂ E)) w) = 0 := by
    rw [← LinearMap.adjoint_inner_left, h1, inner_zero_left]
  have h3 : (T - a • (1 : Module.End ℂ E)) w = (b - a) • w := by simp [hw, sub_smul]
  rw [h3, inner_smul_right, mul_eq_zero] at h2
  exact h2.resolve_left (sub_ne_zero.2 hab.symm)

end NormalFamily

theorem normalFamily_orthogonal_decomposition :
    ∀ {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (op : I → Module.End ℂ E), PairComm op → (∀ i, ∃ i', op i' = LinearMap.adjoint (op i)) → (∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i)) ∧ (⨆ x, eigAt op x) = ⊤ ∧ ∀ x x', x ≠ x' → eigAt op x ⟂ eigAt op x' := by
  intro E I _ _ _ op hc hadj
  have hn : ∀ i, Commute (op i) (LinearMap.adjoint (op i)) := fun i => by
    obtain ⟨i', hi'⟩ := hadj i
    rw [← hi']
    exact hc i i'
  have h1 : ∀ x, eigAt op x = ⨅ i, (op i).eigenspace (x i) := fun x =>
    iInf_congr fun i => NormalFamily.maxGenEigenspace_eq (hn i) (x i)
  refine ⟨h1, iSup_eigAt_eq_top hc fun i => Module.End.iSup_maxGenEigenspace_eq_top (op i), ?_⟩
  intro x x' hx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  rw [h1, h1]
  exact (NormalFamily.eigenspace_isOrtho (hn i) hi).mono (iInf_le _ i) (iInf_le _ i)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeSplitOneOfCharTied
namespace GlobalTheory.RowClose

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.RowClose.heckeSplitOne_of_charTied : ∀ (D : _root_.Formalism.BasicNotions.D7) (C : _root_.Formalism.L2.Host.CharFrame D)
    (nch : _root_.Formalism.BasicNotions.NChoice D) (Tp : _root_.Formalism.L2.Host.TupTied D C nch), _root_.Formalism.L2.Host.NCharTied D C nch Tp →
    _root_.GlobalTheory.RowCopy.HeckeSplitOne D := by
  intro D C nch Tp T
  have h := _root_.GlobalTheory.HeckeSplitRow.heckeSplitOne_of_tie D.nd D.naut
    (_root_.GlobalTheory.HeckeSplitRow.heckeCharTie_of_tied T)
  unfold _root_.GlobalTheory.ThetaExh.HeckeSplitOne at h
  exact h

end GlobalTheory.RowClose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegrableOnFundamentalDomainMulRight
open MeasureTheory

namespace GlobalTheory

section
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H}

omit [μ.IsMulLeftInvariant] [Countable Γ] in
theorem isFundamentalDomain_image_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) '' 𝓕) μ := by
  refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
  · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
  · intro γ h
    simp [Subgroup.smul_def, mul_assoc]

theorem setIntegral_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) :
    ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
  rw [h𝓕.setIntegral_eq (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)]
  exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
    (measurableEmbedding_mulRight y) u 𝓕).symm

theorem integrableOn_fundamentalDomain_mul_right (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H)
    (u : H → ℂ) (hu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) (hi : IntegrableOn u 𝓕 μ) :
    IntegrableOn (fun h => u (h * y)) 𝓕 μ := by
  rw [h𝓕.integrableOn_iff (isFundamentalDomain_image_mul_right h𝓕 y) (f := u)
    (fun γ h => hu γ γ.2 h)] at hi
  exact ((measurePreserving_mul_right μ y).integrableOn_image
    (measurableEmbedding_mulRight y)).1 hi

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.DoubleCosetComm

variable {G : Type} [Group G]

def InDC (J : Subgroup G) (x g : G) : Prop := ∃ k₁ k₂ : J, g = (k₁ : G) * x * k₂

theorem InDC.mul {J : Subgroup G} {x g a b : G} (h : InDC J x g) (ha : a ∈ J) (hb : b ∈ J) :
    InDC J x (a * g * b) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨⟨a, ha⟩ * u, v * ⟨b, hb⟩, by simp [mul_assoc]⟩

theorem InDC.inv {J : Subgroup G} {x g : G} (h : InDC J x g) : InDC J x⁻¹ g⁻¹ := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨v⁻¹, u⁻¹, by simp [mul_assoc]⟩

open Classical in
theorem card_filter_le {J : Subgroup G} {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B)
    (P Q : G → Prop) (ψ : G → G) (h1 : ∀ a ∈ A, P a → InDC J y (ψ a))
    (h2 : ∀ a ∈ A, P a → ∀ k ∈ J, Q (ψ a * k))
    (h3 : ∀ a ∈ A, ∀ a' ∈ A, (ψ a)⁻¹ * ψ a' ∈ J → a⁻¹ * a' ∈ J) :
    (A.filter P).card ≤ (B.filter Q).card := by
  have hex : ∀ a : G, ∃ b : G, a ∈ A → P a → b ∈ B ∧ b⁻¹ * ψ a ∈ J := by
    intro a
    by_cases h : a ∈ A ∧ P a
    · obtain ⟨b, hb, -⟩ := hB.2 _ (h1 a h.1 h.2)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨1, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose r hr using hex
  refine Finset.card_le_card_of_injOn r ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨hb, hj⟩ := hr a ha.1 ha.2
    refine ⟨hb, ?_⟩
    have := h2 a ha.1 ha.2 _ (J.inv_mem hj)
    simpa [mul_assoc] using this
  · intro a ha a' ha' e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ha'
    have hj := (hr a ha.1 ha.2).2
    have hj' := (hr a' ha'.1 ha'.2).2
    rw [← e] at hj'
    have h4 : (ψ a)⁻¹ * ψ a' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hj) hj'
    exact (hA.2 a' (hA.1 a' ha'.1)).unique ⟨ha.1, h3 a ha.1 a' ha'.1 h4⟩ ⟨ha'.1, by simp⟩

section Theta

variable {J L : Subgroup G} {θ : G → G}
  (hm : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (hi : ∀ x ∈ L, θ (θ x) = x)
  (hK : ∀ k ∈ J ⊓ L, θ k ∈ J) (hL : ∀ g ∈ L, θ g ∈ L)
  (hdc : ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)

include hm in
theorem theta_inv {g : G} (hg : g ∈ L) : θ g⁻¹ = (θ g)⁻¹ := by
  have h1 : θ 1 = 1 := by
    have h := hm 1 L.one_mem 1 L.one_mem
    rw [mul_one] at h
    have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h'
  apply eq_inv_of_mul_eq_one_left
  rw [← hm _ hg _ (L.inv_mem hg), mul_inv_cancel, h1]

include hm hi hK hL in
theorem theta_coset {a a' : G} (ha : a ∈ L) (ha' : a' ∈ L) (h : θ a * (θ a')⁻¹ ∈ J) : a⁻¹ * a' ∈ J := by
  have hl : a'⁻¹ * a ∈ L := L.mul_mem (L.inv_mem ha') ha
  have e : θ (a'⁻¹ * a) = θ a * (θ a')⁻¹ := by
    rw [hm _ (L.inv_mem ha') _ ha, theta_inv hm ha']
  have := hK (θ (a'⁻¹ * a)) ⟨e ▸ h, hL _ hl⟩
  rw [hi _ hl] at this
  simpa using J.inv_mem this

include hdc in
theorem InDC.theta {x g : G} (h : InDC J x g) (hg : g ∈ L) : InDC J x (θ g) := by
  obtain ⟨a, ha, b, hb, e⟩ := hdc g hg
  rw [e]
  exact h.mul ha.1 hb.1

include hm hi hK hL hdc in
theorem card_le_inv {x : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x⁻¹ A') (hAL : ∀ a ∈ A, a ∈ L) :
    A.card ≤ A'.card := by
  classical
  have := card_filter_le hA hA' (fun _ => True) (fun _ => True) (fun a => (θ a)⁻¹)
    (fun a ha _ => (InDC.theta hdc (hA.1 a ha) (hAL a ha)).inv) (fun _ _ _ _ _ => trivial)
    (fun a ha a' ha' h => theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa using h))
  simpa using this

open Classical in
include hm hi hK hL hdc in
theorem card_conv_le {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    {z : G} (hz : z ∈ L) :
    (A.filter fun a => InDC J y (a⁻¹ * z)).card ≤ (B.filter fun b => InDC J x (b⁻¹ * z)).card := by
  obtain ⟨k, hk, k', hk', e⟩ := hdc z hz
  refine card_filter_le hA hB _ _ (fun a => z * k' * (θ a)⁻¹) ?_ ?_ ?_
  · intro a ha hP
    have hl := L.inv_mem (hAL a ha)
    have h1 := InDC.theta hdc hP (L.mul_mem hl hz)
    rw [hm _ hl _ hz, theta_inv hm (hAL a ha), e] at h1
    simpa [mul_assoc] using h1.mul (J.inv_mem hk.1) J.one_mem
  · intro a ha _ c hc
    have h1 := InDC.theta hdc (hA.1 a ha) (hAL a ha)
    simpa [mul_assoc] using h1.mul (J.inv_mem hc) (J.inv_mem hk'.1)
  · intro a ha a' ha' h
    exact theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa [mul_assoc] using h)

end Theta

open Classical in
theorem card_pairs {J L : Subgroup G} {y : G} {A B : Finset G} (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    (hBL : ∀ b ∈ B, b ∈ L) {z : G} (hz : z ∈ L) :
    ((A ×ˢ B).filter fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))).card =
      (A.filter fun a => InDC J y (a⁻¹ * z)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have h1 : InDC J y b := hB.1 b hp.1.2
    simpa [mul_assoc] using h1.mul J.one_mem (J.inv_mem hp.2.1)
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' e
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp hp' e
    subst e
    have h4 : b⁻¹ * b' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hp.2.1) hp'.2.1
    have := (hB.2 b' (hB.1 b' hp'.1.2)).unique ⟨hp.1.2, h4⟩ ⟨hp'.1.2, by simp⟩
    rw [this]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨b, ⟨hb, hj⟩, -⟩ := hB.2 _ ha.2
    refine ⟨(a, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨ha.1, hb⟩, ?_, L.mul_mem (L.inv_mem hz) (L.mul_mem (hAL a ha.1) (hBL b hb))⟩
    simpa [mul_assoc] using J.inv_mem hj

theorem dcOp_comm_and_card : ∀ {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J L : Subgroup G) (χ : J →* ℂˣ) (x y : G) (A B A' : Finset G) (F : G → W), (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ B, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J y B → IsDC J x⁻¹ A' → (∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) → dcOp A (dcOp B F) = dcOp B (dcOp A F) ∧ A.card = A'.card := by
  classical
  intro G W _ _ _ J L χ x y A B A' F _ hχ ⟨θ, hL, hm, hi, hK, hdc⟩ hAL hBL hAL' hA hB hA' hF
  refine ⟨?_, le_antisymm (card_le_inv hm hi hK hL hdc hA hA' hAL)
    (card_le_inv hm hi hK hL hdc hA' (by rwa [inv_inv]) hAL')⟩
  have hFK : ∀ g g' : G, (g : G ⧸ (J ⊓ L)) = g' → ∀ h, F (h * g) = F (h * g') := by
    intro g g' e h
    rw [QuotientGroup.eq] at e
    have := hF ⟨_, e.1⟩ (h * g)
    rw [hχ ⟨_, e.1⟩ e.2] at this
    simpa [mul_assoc] using this.symm
  have hms : (A ×ˢ B).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) =
      (B ×ˢ A).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [Multiset.count_map, Multiset.count_map]
      by_cases hz : z ∈ L
      · have e1 := card_pairs (A := A) hB hAL hBL hz
        have e2 := card_pairs (A := B) hA hBL hAL hz
        have e3 := le_antisymm (card_conv_le hm hi hK hL hdc hA hB hAL hz)
          (card_conv_le hm hi hK hL hdc hB hA hBL hz)
        have := e1.trans (e3.trans e2.symm)
        rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val] at this
        convert this
      · have hz' : ∀ C D : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ D, a ∈ L) →
            Multiset.filter (fun p : G × G => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) (C ×ˢ D).val = 0 := by
          intro C D hC hD
          rw [Multiset.filter_eq_nil]
          intro p hp e
          rw [Finset.mem_val, Finset.mem_product] at hp
          rw [QuotientGroup.eq] at e
          apply hz
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (hC _ hp.1) (hD _ hp.2)) (L.inv_mem e.2)
        rw [hz' A B hAL hBL, hz' B A hBL hAL]
  funext h
  have key : ∀ C D : Finset G, dcOp C (dcOp D F) h =
      (((C ×ˢ D).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L)))).map fun q => F (h * q.out)).sum := by
    intro C D
    rw [Multiset.map_map]
    change _ = ∑ p ∈ C ×ˢ D, _
    rw [Finset.sum_product]
    simp only [dcOp, Function.comp]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
    exact hFK _ _ (QuotientGroup.out_eq' _).symm h
  rw [key, key, hms]

end GlobalTheory.DoubleCosetComm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem use₂ {Kf K ι : Type} [Field Kf] [Field K] [Fintype ι] {n : ℕ} (eK : K →+* Kf) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map eK (actP lam B F) = actP lam (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) := by
  have h1 : (MvPolynomial.map eK).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc eK (B τ))).toRingHom.comp (MvPolynomial.map eK) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map eK (trAct B F) = trAct (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) :=
    congrArg (fun φ : Pol K ι n →+* Pol Kf ι n => φ F) h1
  have h3 : eK (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc eK (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

end GlobalTheory.ValCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.FormsDescent

section General

variable {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

def coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) : V :=
  ∑ i, φ (b.repr v i) • b i

theorem repr_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (v : V) (i : ι) :
    b.repr (coordMap F b φ v) i = φ (b.repr v i) := by
  unfold coordMap
  rw [b.repr_sum_self]

theorem coordMap_sum (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) {α : Type} [Fintype α]
    (x : α → K) (w : α → V) (hw : ∀ a i, b.repr (w a) i ∈ F) :
    coordMap F b φ (∑ a, x a • w a) = ∑ a, φ (x a) • w a := by
  apply b.repr.injective
  ext i
  rw [repr_coordMap]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply', Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := φ.map_smul (⟨b.repr (w a) i, hw a i⟩ : F) (x a)
  simp only [Subfield.smul_def, smul_eq_mul] at h
  rw [mul_comm (x a), h, mul_comm]

theorem map_coordMap (F : Subfield K) (b : Module.Basis ι K V) (φ : K →ₗ[F] K) (g : V →ₗ[K] V)
    (hg : ∀ i j, b.repr (g (b j)) i ∈ F) (v : V) :
    g (coordMap F b φ v) = coordMap F b φ (g v) := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [h1, coordMap_sum F b φ _ _ (fun a i => hg i a)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordMap, map_sum, map_smul]

theorem exists_retraction (F : Subfield K) :
    ∃ φ : K →ₗ[F] K, (∀ x, φ x ∈ F) ∧ ∀ x ∈ F, φ x = x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F K)
    (LinearMap.ker_eq_bot.2 (algebraMap F K).injective)
  refine ⟨(Algebra.linearMap F K).comp g, fun x => (g x).2, fun x hx => ?_⟩
  have h := LinearMap.congr_fun hg ⟨x, hx⟩
  have h' : g x = ⟨x, hx⟩ := h
  show ((g x : F) : K) = x
  rw [h']

end General

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem hasRatBasis_of_act
    (h : ∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) : S.HasRatBasis := by
  classical
  haveI : Module.Finite (cmMax K) K := Module.Finite.of_restrictScalars_finite ℚ (cmMax K) K
  let e := Module.finBasis (cmMax K) K
  let s : Set S.Forms := {f | S.IsRat (f : S.Cl → S.V)}
  have hs : ⊤ ≤ Submodule.span K s := by
    intro f _
    let φ : Fin (Module.finrank (cmMax K) K) → (K →ₗ[cmMax K] K) :=
      fun k => (Algebra.linearMap (cmMax K) K).comp (e.coord k)
    let g : Fin (Module.finrank (cmMax K) K) → S.Forms := fun k =>
      ⟨fun c => coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c), fun c γ => by
        rw [map_coordMap (cmMax K) S.bV (φ k) (S.ρ c γ) (h c γ), f.2 c γ]⟩
    have hf : f = ∑ k, e k • g k := by
      apply Subtype.ext
      funext c
      apply S.bV.repr.injective
      ext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
        Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, g, repr_coordMap]
      conv_lhs => rw [← e.sum_repr (S.bV.repr ((f : S.Cl → S.V) c) i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
      rfl
    rw [hf]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro c i
    show S.bV.repr (coordMap (cmMax K) S.bV (φ k) ((f : S.Cl → S.V) c)) i ∈ cmMax K
    rw [repr_coordMap]
    exact (e.coord k _).2
  let b := Module.Basis.ofSpan hs
  refine ⟨b.reindex (b.indexEquiv (Module.finBasis K S.Forms)), fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.Basis.ofSpan_subset hs ⟨_, rfl⟩

theorem repr_mem_of_isRat (h : S.HasRatBasis) (f : S.Forms) (hf : S.IsRat (f : S.Cl → S.V)) (a : Fin S.dim) :
    S.basis.repr f a ∈ cmMax K := by
  have hb : ∀ i, S.IsRat (S.basis i : S.Cl → S.V) := by
    have : S.basis = h.choose := by
      unfold CSD.basis
      exact dif_pos h
    rw [this]
    exact h.choose_spec
  obtain ⟨φ, h1, h2⟩ := exists_retraction (cmMax K)
  have key : f = ∑ a, φ (S.basis.repr f a) • S.basis a := by
    apply Subtype.ext
    funext c
    have e1 : (f : S.Cl → S.V) c = ∑ a, S.basis.repr f a • (S.basis a : S.Cl → S.V) c := by
      conv_lhs => rw [← S.basis.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    have e2 : coordMap (cmMax K) S.bV φ ((f : S.Cl → S.V) c) = (f : S.Cl → S.V) c := by
      apply S.bV.repr.injective
      ext i
      rw [repr_coordMap, h2 _ (hf c i)]
    rw [← e2, e1, coordMap_sum (cmMax K) S.bV φ _ _ (fun a i => hb a c i)]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
  have : S.basis.repr f a = φ (S.basis.repr f a) := by
    conv_lhs => rw [key]
    rw [S.basis.repr_sum_self]
  rw [this]
  exact h1 _

end GlobalTheory.FormsDescent

namespace GlobalTheory

theorem forms_rat : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K), ((∀ c (γ : S.Gam c) i j, S.bV.repr (S.ρ c γ (S.bV j)) i ∈ cmMax K) → S.HasRatBasis) ∧ ∀ T : Module.End K S.Forms, S.HasRatBasis → (∀ f : S.Forms, S.IsRat (f : S.Cl → S.V) → S.IsRat ((T f : S.Forms) : S.Cl → S.V)) → ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro K _ _ _ S
  refine ⟨FormsDescent.hasRatBasis_of_act S, fun T h hT a b => ?_⟩
  rw [LinearMap.toMatrix_apply]
  refine FormsDescent.repr_mem_of_isRat S h _ (hT _ ?_) a
  have : S.basis = h.choose := by
    unfold CSD.basis
    exact dif_pos h
  rw [this]
  exact h.choose_spec b

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPowDivFactorialLe
noncomputable section

namespace GlobalTheory.BiextInhab

open MvPowerSeries Formalism.FG.SolveVAux

def laK (K : Type) [Field K] (l d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) K :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : K) ^ e)⁻¹ else 0

section Field

variable {K : Type} [Field K] {l d : ℕ}

theorem _root_.GlobalTheory.BiextInhab.laK_idMod2 (hl : l.Prime) :
    _root_.Formalism.FG.IsIdMod2 (_root_.GlobalTheory.BiextInhab.laK K l d) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · show _root_.GlobalTheory.BiextInhab.laK K l d j 0 = 0
    unfold _root_.GlobalTheory.BiextInhab.laK
    refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
    exact pow_ne_zero _ hl.ne_zero (Finsupp.single_eq_zero.mp h.symm)
  · show _root_.GlobalTheory.BiextInhab.laK K l d j (Finsupp.single i 1) = _
    unfold _root_.GlobalTheory.BiextInhab.laK
    rw [Finset.sum_eq_single 0]
    · simp [Finsupp.single_left_inj one_ne_zero]
    · intro e _ he
      refine if_neg fun h => he ?_
      have h1 := congrArg (fun f : ZMod d →₀ ℕ => f.sum fun _ k => k) h
      simp only [Finsupp.sum_single_index] at h1
      rcases Nat.pow_eq_one.mp h1.symm with h2 | h2
      · exact absurd h2 hl.ne_one
      · omega
    · intro h
      simp at h

variable [NeZero d]

end Field

section Padic

open Formalism.G

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} {τ : Type}

variable [NeZero d]

end Padic

section Main

open GlobalTheory.ThStr Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

def serW (l : ℕ) [Fact l.Prime] (κ : Type) : Subring (MvPowerSeries κ ℂ_[l]) :=
  (MvPowerSeries.map (σ := κ) (Wp l).subtype).range

theorem _root_.GlobalTheory.BiextInhab.mem_serW {κ : Type} {F : MvPowerSeries κ ℂ_[l]} :
    F ∈ _root_.GlobalTheory.BiextInhab.serW l κ ↔ _root_.Formalism.MainNotions.GL3Theta.IntegralW F := by
  constructor
  · rintro ⟨G, rfl⟩ n
    exact (coeff n G).2
  · intro h
    exact ⟨fun n => ⟨coeff n F, h n⟩, by ext n; rfl⟩

variable [NeZero d]

private theorem coeff_mapDomain_rename_of_injective {σ τ R : Type} [CommSemiring R] (f : σ → τ)
    [Filter.TendstoCofinite f] (hf : Function.Injective f) (p : MvPowerSeries σ R)
    (n : σ →₀ ℕ) : coeff (Finsupp.mapDomain f n) (rename f p) = coeff n p := by
  rw [coeff_rename, Finset.sum_eq_single n]
  · intro y hy hne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
    exact absurd (Finsupp.mapDomain_injective hf hy) hne
  · intro hn
    exact absurd (by simp) hn

theorem _root_.GlobalTheory.BiextInhab.bridge (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]
    {β : Type} (b : β) (s : ZMod d) :
    _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) := by
  have hinj : Function.Injective (fun r : ZMod d => (r, b)) := fun x y h => (Prod.mk.inj h).1
  have hren : _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      rename (fun r : ZMod d => (r, b)) (_root_.GlobalTheory.ThStr.laS l d s) := by
    rw [rename_eq_subst]
    rfl
  have hsingle : ∀ e : ℕ, (Finsupp.single (s - 2 * (e : ZMod d), b) ((l ^ 2) ^ e) :
      ZMod d × β →₀ ℕ) = Finsupp.mapDomain (fun r : ZMod d => (r, b))
        (Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) := by
    intro e
    rw [Finsupp.mapDomain_single, pow_mul]
    push_cast
    rfl
  rw [hren]
  ext m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (fun r : ZMod d => (r, b)))
  · obtain ⟨n, rfl⟩ := hm
    have hdeg : _root_.Formalism.BasicNotions.JetTdeg (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n) =
        n.sum fun _ k => k := by
      unfold _root_.Formalism.BasicNotions.JetTdeg
      exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    rw [coeff_mapDomain_rename_of_injective _ hinj]
    show _root_.GlobalTheory.ThStr.laS l d s n =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n)
    unfold _root_.GlobalTheory.ThStr.laS _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    rw [hdeg]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hsingle e, (Finsupp.mapDomain_injective hinj).eq_iff]
  · rw [coeff_rename_eq_zero _ _ hm]
    show (0 : ℂ_[l]) = _root_.Formalism.BasicNotions.jetLogG l d (s, b) m
    unfold _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    symm
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    rintro rfl
    exact hm ⟨_, (hsingle e).symm⟩

end Main

end GlobalTheory.BiextInhab
end
end
