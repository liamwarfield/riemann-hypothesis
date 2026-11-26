module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.VanPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CuspIdeal
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix

namespace UpperTheory.Gal.Spc

section Abstract

variable {Γ A H : Type} [Group Γ] [Group A] [Group H] [TopologicalSpace A] [TopologicalSpace H]
  [IsTopologicalGroup A] [IsTopologicalGroup H]
  (e : Γ ≃* A × H) {K : Subgroup Γ} {K₀ : Subgroup A} {K' : Subgroup H}

private theorem mem_K (hK : K.map e.toMonoidHom = K₀.prod K') (x : Γ) : x ∈ K ↔ e x ∈ K₀.prod K' := by
  rw [← hK, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem compact_hull (hK : K.map e.toMonoidHom = K₀.prod K') (c₀ : IsCompact (K₀ : Set A))
    (c' : IsCompact (K' : Set H)) {f : Γ → ℂ} (hf : f ∈ Formalism.UG.Hecke ℂ K) :
    ∃ D : Set (A × H), IsCompact D ∧ ∀ x, f x ≠ 0 → e x ∈ D := by
  obtain ⟨-, S, hS⟩ := hf
  have hC : IsCompact ((K₀ : Set A) ×ˢ (K' : Set H)) := c₀.prod c'
  refine ⟨⋃ s ∈ S, (fun p : (A × H) × (A × H) => p.1 * e s * p.2) ''
    (((K₀ : Set A) ×ˢ (K' : Set H)) ×ˢ ((K₀ : Set A) ×ˢ (K' : Set H))), ?_, ?_⟩
  · exact S.isCompact_biUnion fun s _ => (hC.prod hC).image (by fun_prop)
  · intro x hx
    obtain ⟨s, hs, u, v, rfl⟩ := hS x hx
    refine Set.mem_iUnion₂.2 ⟨s, hs, ⟨(e u, e v), ⟨?_, ?_⟩, by simp [map_mul]⟩⟩
    · exact Subgroup.mem_prod.1 ((mem_K e hK u).1 u.2)
    · exact Subgroup.mem_prod.1 ((mem_K e hK v).1 v.2)

private theorem finite_cosets (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set A))
    (o' : IsOpen (K' : Set H)) (c₀ : IsCompact (K₀ : Set A)) (c' : IsCompact (K' : Set H)) {a : Γ → ℂ}
    (ha : a ∈ Formalism.UG.Hecke ℂ K) : {q : Γ ⧸ K | a q.out ≠ 0}.Finite := by
  have oU : IsOpen ((K₀.prod K' : Subgroup (A × H)) : Set (A × H)) := by
    rw [Subgroup.coe_prod]
    exact o₀.prod o'
  haveI := QuotientGroup.discreteTopology oU
  obtain ⟨D, hD, hsupp⟩ := compact_hull e hK c₀ c' ha
  have hT : (((↑) : A × H → (A × H) ⧸ K₀.prod K') '' D).Finite :=
    (hD.image QuotientGroup.continuous_mk).finite_of_discrete
  let φ : Γ ⧸ K → (A × H) ⧸ K₀.prod K' := fun q => ((e q.out : A × H) : (A × H) ⧸ K₀.prod K')
  have hφ : Function.Injective φ := by
    intro q₁ q₂ h
    have h' : (e q₁.out)⁻¹ * e q₂.out ∈ K₀.prod K' := QuotientGroup.eq.1 h
    rw [← map_inv, ← map_mul, ← mem_K e hK] at h'
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.2 h'
  refine (hT.preimage hφ.injOn).subset ?_
  intro q hq
  exact ⟨e q.out, hsupp _ hq, rfl⟩

private theorem slice_right (hK : K.map e.toMonoidHom = K₀.prod K') {f : Γ → ℂ} (hf : Formalism.UG.IsBiInv K f)
    (h' : H) (g : A) {c : A} (hc : c ∈ K₀) : f (e.symm (g * c, h')) = f (e.symm (g, h')) := by
  have hm : e.symm (c, 1) ∈ K := (mem_K e hK _).2 (by simpa using Subgroup.mem_prod.2 ⟨hc, K'.one_mem⟩)
  have hsplit : e.symm (g * c, h') = e.symm (g, h') * e.symm (c, 1) := by
    rw [← map_mul]
    simp
  rw [hsplit]
  simpa using hf 1 ⟨_, hm⟩ (e.symm (g, h'))

private theorem slice_cont (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set A)) {f : Γ → ℂ}
    (hf : Formalism.UG.IsBiInv K f) (h' : H) : Continuous fun g : A => f (e.symm (g, h')) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hev : ∀ᶠ x in nhds g, g⁻¹ * x ∈ K₀ := by
    have hc : Continuous fun x : A => g⁻¹ * x := continuous_const.mul continuous_id
    exact (o₀.preimage hc).mem_nhds (by simp [K₀.one_mem])
  refine (continuousAt_const (y := f (e.symm (g, h')))).congr ?_
  filter_upwards [hev] with x hx
  have hx' := slice_right e hK hf h' g hx
  rw [mul_inv_cancel_left] at hx'
  exact hx'.symm

end Abstract

section Unipotent

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [MeasurableSpace k]
  [BorelSpace k] [SecondCountableTopology k] {n a b : ℕ} (ε : Fin n ≃ Fin a ⊕ Fin b)

private def blk (X : Fin a → Fin b → k) : Matrix (Fin n) (Fin n) k :=
  Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)

private theorem blk_neg (X : Fin a → Fin b → k) : blk ε X * blk ε (-X) = 1 := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem blk_cont : Continuous (blk ε : (Fin a → Fin b → k) → Matrix (Fin n) (Fin n) k) := by
  unfold blk
  fun_prop

private theorem integrable_slice {F : GL (Fin n) k → ℂ} (hc : Continuous F) {C : Set (GL (Fin n) k)}
    (hC : IsCompact C) (hs : ∀ y, F y ≠ 0 → y ∈ C) (μ : Measure (Fin a → Fin b → k)) [μ.IsAddHaarMeasure]
    (u : (Fin a → Fin b → k) → GL (Fin n) k) (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) = blk ε X)
    (g h : GL (Fin n) k) : Integrable (fun X => F (g * (h⁻¹ * u X * h))) μ := by
  have hinv : ∀ X, (((u X)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = blk ε (-X) := by
    intro X
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hu X]
    exact blk_neg ε X
  have hcu : Continuous u := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have hv : (Units.val ∘ u) = blk ε := funext hu
      rw [hv]
      exact blk_cont ε
    · have hv : (fun X => (((u X)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = fun X => blk ε (-X) :=
        funext hinv
      rw [hv]
      exact (blk_cont ε).comp continuous_neg
  have hcont : Continuous fun X => g * (h⁻¹ * u X * h) :=
    continuous_const.mul ((continuous_const.mul hcu).mul continuous_const)
  let π : GL (Fin n) k → (Fin a → Fin b → k) := fun y i j =>
    (y : Matrix (Fin n) (Fin n) k) (ε.symm (Sum.inl i)) (ε.symm (Sum.inr j))
  have hπ : Continuous π :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem _ _
  have hπu : ∀ X, π (u X) = X := by
    intro X
    funext i j
    simp [π, hu, blk, Matrix.reindex_apply]
  have hπ' : Continuous fun y : GL (Fin n) k => π (h * (g⁻¹ * y) * h⁻¹) := by
    exact hπ.comp ((continuous_const.mul (continuous_const.mul continuous_id)).mul continuous_const)
  refine (hc.comp hcont).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (hC.image hπ') ?_
  intro X hX
  by_contra hne
  apply hX
  refine ⟨g * (h⁻¹ * u X * h), hs _ hne, ?_⟩
  dsimp only
  rw [show h * (g⁻¹ * (g * (h⁻¹ * u X * h))) * h⁻¹ = u X by group]
  exact hπu X

end Unipotent

section Main

variable {Γ H : Type} [Group Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [MeasurableSpace k]
  [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (e : Γ ≃* GL (Fin n) k × H) {K : Subgroup Γ} {K₀ : Subgroup (GL (Fin n) k)} {K' : Subgroup H}

private theorem hecke_integrable (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set (GL (Fin n) k)))
    (c₀ : IsCompact (K₀ : Set (GL (Fin n) k))) (c' : IsCompact (K' : Set H)) {f : Γ → ℂ}
    (hf : f ∈ Formalism.UG.Hecke ℂ K) (h' : H) {a b : ℕ} (ε : Fin n ≃ Fin a ⊕ Fin b)
    (μ : Measure (Fin a → Fin b → k)) [μ.IsAddHaarMeasure] (u : (Fin a → Fin b → k) → GL (Fin n) k)
    (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) =
      Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (g h : GL (Fin n) k) : Integrable (fun X => f (e.symm (g * (h⁻¹ * u X * h), h'))) μ := by
  obtain ⟨D, hD, hsupp⟩ := compact_hull e hK c₀ c' hf
  have hbi : Formalism.UG.IsBiInv K f := hf.1
  refine integrable_slice ε (slice_cont e hK o₀ hbi h') (hD.image continuous_fst) ?_ μ u
    (fun X => (hu X).trans rfl) g h
  intro y hy
  exact ⟨(y, h'), by simpa using hsupp _ hy, rfl⟩

private theorem left_mul (w : Γ) (y : GL (Fin n) k) (h' : H) :
    w * e.symm (y, h') = e.symm ((e w).1 * y, (e w).2 * h') := by
  apply e.injective
  rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

private theorem noConst_lin (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set (GL (Fin n) k)))
    (c₀ : IsCompact (K₀ : Set (GL (Fin n) k))) (c' : IsCompact (K' : Set H)) {f f' : Γ → ℂ}
    (hf : f ∈ Formalism.UG.Hecke ℂ K) (hf' : f' ∈ Formalism.UG.Hecke ℂ K) (c : ℂ)
    (Cf : ∀ h : H, NoConst fun g => f (e.symm (g, h))) (Cf' : ∀ h : H, NoConst fun g => f' (e.symm (g, h)))
    (h' : H) : NoConst fun g => (c • f + f') (e.symm (g, h')) := by
  intro a b ε ha hb μ hμ u hu g h
  haveI := hμ
  have i1 := hecke_integrable e hK o₀ c₀ c' hf h' ε μ u hu g h
  have i2 := hecke_integrable e hK o₀ c₀ c' hf' h' ε μ u hu g h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (i1.const_mul c) i2, integral_const_mul, Cf h' a b ε ha hb μ hμ u hu g h,
    Cf' h' a b ε ha hb μ hμ u hu g h]
  simp

private theorem noConst_conv (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set (GL (Fin n) k)))
    (o' : IsOpen (K' : Set H)) (c₀ : IsCompact (K₀ : Set (GL (Fin n) k))) (c' : IsCompact (K' : Set H))
    {α f : Γ → ℂ} (hα : α ∈ Formalism.UG.Hecke ℂ K) (hf : f ∈ Formalism.UG.Hecke ℂ K)
    (Cf : ∀ h : H, NoConst fun g => f (e.symm (g, h))) (h' : H) :
    NoConst fun g => Formalism.UG.conv K α f (e.symm (g, h')) := by
  intro a b ε ha hb μ hμ u hu g h
  haveI := hμ
  have hS := finite_cosets e hK o₀ o' c₀ c' hα
  have key : ∀ y : GL (Fin n) k, Formalism.UG.conv K α f (e.symm (y, h')) =
      ∑ q ∈ hS.toFinset, α q.out * f (e.symm ((e q.out⁻¹).1 * y, (e q.out⁻¹).2 * h')) := by
    intro y
    unfold Formalism.UG.conv
    rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset)]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [left_mul e]
    · intro q hq
      simp only [Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hq ⊢
      exact left_ne_zero_of_mul hq
  simp only [key]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [integral_const_mul]
    have hz := Cf ((e q.out⁻¹).2 * h') a b ε ha hb μ hμ u hu ((e q.out⁻¹).1 * g) h
    simp only [mul_assoc] at hz ⊢
    rw [hz, mul_zero]
  · intro q _
    refine Integrable.const_mul ?_ _
    have hi := hecke_integrable e hK o₀ c₀ c' hf ((e q.out⁻¹).2 * h') ε μ u hu ((e q.out⁻¹).1 * g) h
    simpa only [mul_assoc] using hi

end Main

theorem cuspIdeal : CuspIdeal := by
  intro p _ G _ Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  refine ⟨fun a ha f hf Cf h' => ?_, fun h' => ?_, fun f hf f' hf' c Cf Cf' h' => ?_⟩
  · exact noConst_conv S.e S.map_eq S.open₀ S.open' S.cpt₀ S.cpt' ha hf Cf h'
  · intro a b ε ha hb μ hμ u hu g h
    simp
  · exact noConst_lin S.e S.map_eq S.open₀ S.cpt₀ S.cpt' hf hf' c Cf Cf' h'

end UpperTheory.Gal.Spc
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CommOfOpen
set_option autoImplicit false

noncomputable section

open Formalism.UG GlobalTheory.LKDef

namespace UpperTheory.Gal.Spc

section Abstract

variable {H₁ H₂ Γ V : Type} [Group H₁] [Group H₂] [Group Γ] [AddCommGroup V] [Module ℂ V]
  (ι : Γ →* H₁ × H₂) (K₁ : Subgroup H₁) (K₂ : Subgroup H₂) (ξ : Representation ℂ Γ V)

variable {K₁} in
private theorem hecke_right {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (h : H₁) (c : K₁) : f (h * c) = f h := by
  have := hf.1 1 c h
  simpa using this

variable {K₁} in
private theorem hecke_left {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (h : H₁) (c : K₁) : f (c * h) = f h := by
  have := hf.1 c 1 h
  simpa using this

variable {K₁} in
private theorem fin_act (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (Φ : H₁ × H₂ → V) (g : H₁ × H₂) :
    (Function.support fun x : H₁ ⧸ K₁ => f x.out • Φ (g * (x.out, 1))).Finite :=
  (P.finite_supp K₁ hK f hf).subset fun x hx h0 => hx (by simp [h0])

variable {ι K₁ K₂ ξ} in
private theorem form_right {Φ : H₁ × H₂ → V} (hΦ : Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ) (g : H₁ × H₂) {k₁ : H₁} {k₂ : H₂}
    (h₁ : k₁ ∈ K₁) (h₂ : k₂ ∈ K₂) : Φ (g * (k₁, k₂)) = Φ g :=
  hΦ.2 _ (Subgroup.mem_prod.2 ⟨h₁, h₂⟩) g

variable {ι K₁ K₂ ξ} in
private theorem act_mem (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) {Φ : H₁ × H₂ → V}
    (hΦ : Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ) : hActK K₁ f Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ := by
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
  · unfold hActK
    rw [map_finsum (ξ γ) (fin_act hK hf Φ g)]
    refine finsum_congr fun x => ?_
    rw [map_smul, mul_assoc, hΦ.1]
  · obtain ⟨h₁, h₂⟩ := Subgroup.mem_prod.1 hk
    unfold hActK
    have key := P.finsum_out_mul K₁ k.1 (fun h => f h • Φ (g * (h, 1))) (fun h c => by
      have e : g * (h * (c : H₁), (1 : H₂)) = g * (h, 1) * ((c : H₁), (1 : H₂)) := by
        simp [mul_assoc]
      show f (h * c) • Φ (g * (h * (c : H₁), (1 : H₂))) = f h • Φ (g * (h, 1))
      rw [hecke_right hf, e, form_right hΦ _ c.2 (one_mem _)])
    refine Eq.trans ?_ key
    refine finsum_congr fun x => ?_
    have e : g * k * (x.out, (1 : H₂)) = g * (k.1 * x.out, 1) * ((1 : H₁), k.2) := by
      ext <;> simp [mul_assoc]
    show _ = f (k.1 * x.out) • Φ (g * (k.1 * x.out, 1))
    rw [e, form_right hΦ _ (one_mem _) h₂, hecke_left hf x.out ⟨k.1, h₁⟩]

private def act (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) :
    Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ) where
  toFun Φ := ⟨hActK K₁ f Φ, act_mem hK hf Φ.2⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, f x.out • ((a : H₁ × H₂ → V) (g * (x.out, 1)) + (b : H₁ × H₂ → V) (g * (x.out, 1)))) =
      (∑ᶠ x : H₁ ⧸ K₁, f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))) +
        ∑ᶠ x : H₁ ⧸ K₁, f x.out • (b : H₁ × H₂ → V) (g * (x.out, 1))
    simp only [smul_add]
    exact finsum_add_distrib (fin_act hK hf _ g) (fin_act hK hf _ g)
  map_smul' c a := by
    apply Subtype.ext
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, f x.out • (c • (a : H₁ × H₂ → V) (g * (x.out, 1)))) =
      c • ∑ᶠ x : H₁ ⧸ K₁, f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))
    rw [smul_finsum' c (show Function.HasFiniteSupport
      (fun x : H₁ ⧸ K₁ => f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))) from fin_act hK hf _ g)]
    exact finsum_congr fun x => smul_comm _ _ _

variable {K₁} in
private theorem act_mul (hK : IsCommensurated K₁) {f₁ f₂ : H₁ → ℂ} (h₁ : f₁ ∈ Hecke ℂ K₁) (h₂ : f₂ ∈ Hecke ℂ K₁)
    {Φ : H₁ × H₂ → V} (hΦ : ∀ (k : H₁), k ∈ K₁ → ∀ g, Φ (g * (k, 1)) = Φ g) :
    hActK K₁ (conv K₁ f₁ f₂) Φ = hActK K₁ f₁ (hActK K₁ f₂ Φ) := by
  funext g
  let φ : H₁ → V := fun x => Φ (g * (x, 1))
  have hφ : φ ∈ AMF ℂ (⊥ : Subgroup H₁) K₁ (1 : Representation ℂ (⊥ : Subgroup H₁) V) := by
    rintro ⟨γ, hγ⟩ x ⟨κ, hκ⟩
    obtain rfl : γ = 1 := Subgroup.mem_bot.1 hγ
    have e : g * ((1 : H₁) * x * κ, (1 : H₂)) = g * (x, 1) * (κ, 1) := by simp [mul_assoc]
    show Φ (g * ((1 : H₁) * x * κ, (1 : H₂))) = Φ (g * (x, 1))
    rw [e, hΦ κ hκ]
  have key := congrFun (P.hecke_act_mul H₁ ⊥ K₁ ℂ V 1 hK f₁ h₁ f₂ h₂ φ hφ) 1
  have e1 : ∀ (f : H₁ → ℂ) (a : H₁), hAct K₁ f φ a = hActK K₁ f Φ (g * (a, 1)) := by
    intro f a
    unfold hAct hActK
    refine finsum_congr fun x => ?_
    have e : g * (a * x.out, (1 : H₂)) = g * (a, 1) * (x.out, 1) := by simp [mul_assoc]
    show f x.out • Φ (g * (a * x.out, (1 : H₂))) = _
    rw [e]
  have l : hActK K₁ (conv K₁ f₁ f₂) Φ g = hAct K₁ (conv K₁ f₁ f₂) φ 1 := by
    rw [e1]
    exact congrArg _ (mul_one g).symm
  have r : hActK K₁ f₁ (hActK K₁ f₂ Φ) g = hAct K₁ f₁ (hAct K₁ f₂ φ) 1 := by
    show (∑ᶠ x : H₁ ⧸ K₁, f₁ x.out • hActK K₁ f₂ Φ (g * (x.out, 1))) =
      ∑ᶠ x : H₁ ⧸ K₁, f₁ x.out • hAct K₁ f₂ φ (1 * x.out)
    refine finsum_congr fun x => ?_
    rw [e1, one_mul]
  rw [l, r, key]

variable {ι K₁ K₂ ξ} in
private theorem act_isHecke (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) :
    HeckeTraceForms.IsHecke ι (K₁.prod K₂) ξ (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2)
      (act ι K₁ K₂ ξ hK hf) := by
  intro φ g
  let e : H₁ ⧸ K₁ → (H₁ × H₂) ⧸ (K₁.prod K₂) := fun q => QuotientGroup.mk (q.out, 1)
  have he : Function.Injective e := by
    intro a b hab
    have h := QuotientGroup.eq.1 hab
    have h1 := (Subgroup.mem_prod.1 h).1
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    exact QuotientGroup.eq.2 (by simpa using h1)
  set A : (H₁ × H₂) ⧸ (K₁.prod K₂) → V := fun h =>
    (f h.out.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.out.2) • (φ : H₁ × H₂ → V) (g * h.out) with hA
  have hsupp : ∀ h, A h ≠ 0 → h ∈ Set.range e := by
    intro h hh
    have h2 : h.out.2 ∈ K₂ := by
      by_contra hn
      exact hh (by simp [hA, Set.indicator_of_notMem (show h.out.2 ∉ (K₂ : Set H₂) from hn)])
    refine ⟨QuotientGroup.mk h.out.1, ?_⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K₁ h.out.1
    show QuotientGroup.mk ((QuotientGroup.mk h.out.1 : H₁ ⧸ K₁).out, (1 : H₂)) = h
    rw [hc, ← QuotientGroup.out_eq' h]
    refine QuotientGroup.eq.2 (Subgroup.mem_prod.2 ?_)
    simp only [QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · simpa using K₁.inv_mem c.2
    · simpa using h2
  have hval : ∀ q, A (e q) = f q.out • (φ : H₁ × H₂ → V) (g * (q.out, 1)) := by
    intro q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (K₁.prod K₂) ((q.out, 1) : H₁ × H₂)
    obtain ⟨c₁, c₂⟩ := Subgroup.mem_prod.1 c.2
    have ho : (e q).out = (q.out, 1) * (c : H₁ × H₂) := hc
    simp only [hA]
    rw [ho]
    have e2 : g * (((q.out, 1) : H₁ × H₂) * (c : H₁ × H₂)) = g * (q.out, 1) * ((c : H₁ × H₂).1, (c : H₁ × H₂).2) := by
      rw [mul_assoc]
    rw [e2, form_right φ.2 _ c₁ c₂]
    congr 1
    have i2 : ((((q.out, 1) : H₁ × H₂) * (c : H₁ × H₂)).2) ∈ (K₂ : Set H₂) := by simpa using c₂
    rw [Set.indicator_of_mem i2]
    have := hecke_right hf q.out ⟨_, c₁⟩
    simpa using this
  have hsum : (∑ᶠ h, A h) = ∑ᶠ q, A (e q) := by
    rw [← finsum_mem_range he, finsum_mem_def]
    refine finsum_congr fun h => ?_
    by_cases hr : h ∈ Set.range e
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      by_contra hne
      exact hr (hsupp h hne)
  show hActK K₁ f φ g = ∑ᶠ h, A h
  rw [hsum]
  exact finsum_congr fun q => (hval q).symm

private theorem abs_main (hK : IsCommensurated K₁) :
    ∃ T : (H₁ → ℂ) → Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ), T 0 = 0 ∧
      ∀ f ∈ Hecke ℂ K₁, (∀ Φ, (T f Φ : H₁ × H₂ → V) = hActK K₁ f Φ) ∧
        HeckeTraceForms.heckeTrace ι (K₁.prod K₂) ξ (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2) =
          LinearMap.trace ℂ _ (T f) ∧
        ∀ f' ∈ Hecke ℂ K₁, T (conv K₁ f f') = T f * T f' ∧ ∀ c : ℂ, T (c • f + f') = c • T f + T f' := by
  classical
  let T : (H₁ → ℂ) → Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ) := fun f =>
    if h : f ∈ Hecke ℂ K₁ then act ι K₁ K₂ ξ hK h else 0
  have hT : ∀ f (h : f ∈ Hecke ℂ K₁), T f = act ι K₁ K₂ ξ hK h := fun f h => dif_pos h
  have hTa : ∀ f (h : f ∈ Hecke ℂ K₁) Φ, (T f Φ : H₁ × H₂ → V) = hActK K₁ f Φ := fun f h Φ => by rw [hT f h]; rfl
  refine ⟨T, ?_, fun f hf => ⟨hTa f hf, ?_, fun f' hf' => ⟨?_, fun c => ?_⟩⟩⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    rw [hTa 0 (Submodule.zero_mem _)]
    funext g
    simp [hActK]
  · have hI := act_isHecke (ι := ι) (K₂ := K₂) (ξ := ξ) hK hf
    have hex : ∃ T', HeckeTraceForms.IsHecke ι (K₁.prod K₂) ξ
        (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2) T' := ⟨_, hI⟩
    rw [HeckeTraceForms.heckeTrace, dif_pos hex, hT f hf]
    congr 1
    apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext g
    rw [hex.choose_spec Φ g, hI Φ g]
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    have hc := P.hecke_convolution_mem_holds H₁ K₁ ℂ hK f hf f' hf'
    rw [hTa _ hc, Module.End.mul_apply, hTa f hf, hTa f' hf']
    exact act_mul hK hf hf' fun k hk g => form_right Φ.2 g hk (one_mem _)
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    have hc : c • f + f' ∈ Hecke ℂ K₁ := Submodule.add_mem _ (Submodule.smul_mem _ c hf) hf'
    rw [hTa _ hc]
    show _ = c • (T f Φ : H₁ × H₂ → V) + (T f' Φ : H₁ × H₂ → V)
    rw [hTa f hf, hTa f' hf']
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, (c • f + f') x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) =
      c • (∑ᶠ x : H₁ ⧸ K₁, f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) +
        ∑ᶠ x : H₁ ⧸ K₁, f' x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))
    have hA : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) := fin_act hK hf _ g
    have hB : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => f' x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) := fin_act hK hf' _ g
    have hC : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => c • f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) :=
      Set.Finite.subset hA fun x hx h0 => hx (by
        show c • f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1)) = 0
        rw [show f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1)) = 0 from h0, smul_zero])
    rw [smul_finsum' c hA, ← finsum_add_distrib hC hB]
    refine finsum_congr fun x => ?_
    simp [add_smul, mul_smul]

end Abstract

private theorem comm_of_open {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H)
    (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) : IsCommensurated K := by
  intro g
  have : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have h1 : IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
    rw [Subgroup.coe_map]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ ho
  have h2 : IsOpen (((K.map (MulAut.conj g).toMonoidHom).subgroupOf K : Subgroup K) : Set K) :=
    h1.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ h2
  exact Subgroup.index_ne_zero_iff_finite.2 this

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.opAlg :
    UpperTheory.Gal.Spc.OpAlg := by
  intro p _ G Lv V _ _ ξ B
  exact UpperTheory.Gal.Spc.abs_main B.emb Lv.K.toSubgroup (UpperTheory.Gal.LocalSmoothExtension.Kp G) (ξ.comp (GlobalTheory.LKCx.grp G B.β).subtype)
    (UpperTheory.Gal.Spc.comm_of_open _ Lv.K.isOpen Lv.compact)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ClsMove
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open UpperTheory.Gal.LocalSmoothExtension
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Ring

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

private theorem sim_triv (σ : S →+* Sᵐᵒᵖ) (b b' : S) (x x' Y : Sˣ) (t t' T : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b' * (σ x').unop = algebraMap A S t')
    (hb : b' = algebraMap A S T * ((Y : S) * b * (σ Y).unop)) :
    ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop =
      algebraMap A S ((t' * T⁻¹ * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h0 : b = (t : A) • (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ x).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hx, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = ((t⁻¹ : Aˣ) : A) • b := by
    conv_rhs => rw [h0]
    rw [smul_smul, Units.inv_mul, one_smul]
  have h3 : (Y : S) * b * (σ Y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  calc ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop
      = x' * (Y * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ Y).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • (x' * ((Y : S) * b * (σ Y).unop) * (σ x').unop) := by
        rw [h2]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • ((T⁻¹ : Aˣ) : A) • ((x' : S) * b' * (σ x').unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = _ := by
        rw [hx', Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul]
        ring

private theorem sim_conj (σ : S →+* Sᵐᵒᵖ) (b b' : S) (z y : Sˣ) (T : Aˣ) (r : A)
    (hb : b' = algebraMap A S T * ((y : S) * b * (σ y).unop))
    (hz : (z : S) * b' * (σ z).unop = algebraMap A S r * b') :
    ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop = algebraMap A S r * b := by
  have h1 : (σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h3 : (y : S) * b * (σ y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  rw [← Algebra.smul_def] at hz ⊢
  calc ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop
      = ((y⁻¹ : Sˣ) : S) * ((z : S) * ((y : S) * b * (σ y).unop) * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((T⁻¹ : Aˣ) : A) • (((y⁻¹ : Sˣ) : S) * ((z : S) * b' * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = r • (((y⁻¹ : Sˣ) : S) * (((T⁻¹ : Aˣ) : A) • b') * (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [hz]; simp only [mul_smul_comm, smul_mul_assoc]; rw [smul_comm]
    _ = r • ((((y⁻¹ : Sˣ) : S) * y) * b * ((σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop)) := by
        rw [← h3]; simp only [mul_assoc]
    _ = r • b := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Ring

private theorem mem_forms_move {A H V : Type} [Group A] [Group H] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (Γ Γ' : Subgroup A) (ι : Γ →* H) (ι' : Γ' →* H) (K : Subgroup H) (y : A) (d : H)
    (hc : ∀ γ' : Γ', ∃ γ : Γ, (γ' : A) = y * (γ : A) * y⁻¹ ∧ ι' γ' = d * ι γ * d⁻¹)
    {Φ : H → V} (hΦ : Φ ∈ HeckeTraceForms.forms ι K (ξ.comp Γ.subtype)) :
    (fun g => ξ y (Φ (d⁻¹ * g))) ∈ HeckeTraceForms.forms ι' K (ξ.comp Γ'.subtype) := by
  refine ⟨fun γ' g => ?_, fun k hk g => ?_⟩
  · obtain ⟨γ, e1, e2⟩ := hc γ'
    have e3 : d⁻¹ * (ι' γ' * g) = ι γ * (d⁻¹ * g) := by rw [e2]; group
    have e4 : Φ (ι γ * (d⁻¹ * g)) = ξ (γ : A) (Φ (d⁻¹ * g)) := hΦ.1 γ (d⁻¹ * g)
    show ξ y (Φ (d⁻¹ * (ι' γ' * g))) = ξ (γ' : A) (ξ y (Φ (d⁻¹ * g)))
    rw [e3, e4, e1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · show ξ y (Φ (d⁻¹ * (g * k))) = ξ y (Φ (d⁻¹ * g))
    rw [← mul_assoc]
    exact congrArg _ (hΦ.2 k hk _)

variable {p : ℕ} [Fact p.Prime]

private theorem op_move {G : HTGroup p} {A V : Type} [Group A] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (K : Subgroup G.GAf) (f : G.GAf → ℂ) (Φ : G.GAf × Gr G 1 → V) (y : A)
    (d : G.GAf × Gr G 1) :
    op K f (fun g => ξ y (Φ (d⁻¹ * g))) = fun g => ξ y (op K f Φ (d⁻¹ * g)) := by
  funext g
  let L : V ≃+ V :=
    { toFun := ξ y
      invFun := ξ y⁻¹
      left_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      right_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      map_add' := map_add _ }
  show ∑ᶠ h : G.GAf ⧸ K, f h.out • ξ y (Φ (d⁻¹ * (g * (h.out, 1)))) =
    L (∑ᶠ h : G.GAf ⧸ K, f h.out • Φ (d⁻¹ * g * (h.out, 1)))
  rw [AddEquiv.map_finsum]
  refine finsum_congr fun h => ?_
  show _ = ξ y (_ • _)
  rw [map_smul, mul_assoc]

private theorem conj_emb (G : HTGroup p) (B B' : DForm G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : (B'.β : G.C) = algebraMap ℚ G.C s * (y * B.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t)
    (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ) (hx' : Triv G (AfP p) B'.β x' t') :
    ∃ d : G.GAf × Gr G 1, ∀ γ' : grp G B'.β, ∃ γ : grp G B.β,
      (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (γ : G.Cˣ × ℚˣ) * ((y, 1) : G.Cˣ × ℚˣ)⁻¹ ∧
      B'.embAt x' t' hx' γ' = d * B.embAt x t hx γ * d⁻¹ := by
  let Y : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom y
  let T : (AfP p)ˣ := Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs.ne')
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) := by
    show _ = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s)
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  have hb : inC G (AfP p) B'.β = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) *
      ((Y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) B.β * (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop) := by
    rw [hβ, map_mul, map_mul, map_mul, e1, e2]
    rfl
  have hc := sim_triv (starT G.star (AfP p)) _ _ x x' Y t t' T hx hx' hb
  let c : G.GAf := ⟨(x' * Y * x⁻¹, t' * T⁻¹ * t⁻¹), hc⟩
  refine ⟨(c, inclG G 1 (locC G (y, 1))), fun γ' => ?_⟩
  have hz : ((γ'.1.1 : G.Cˣ) : G.C) * B'.β * (G.star ((γ'.1.1 : G.Cˣ) : G.C)).unop =
      algebraMap ℚ G.C (γ'.1.2 : ℚ) * B'.β := γ'.2.1
  have hmem : ((y⁻¹ * γ'.1.1 * y, γ'.1.2) : G.Cˣ × ℚˣ) ∈ grp G B.β :=
    ⟨sim_conj G.star (B.β : G.C) (B'.β : G.C) γ'.1.1 y (Units.mk0 s hs.ne') (γ'.1.2 : ℚ) hβ hz, γ'.2.2⟩
  have hconj : (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (y⁻¹ * γ'.1.1 * y, γ'.1.2) *
      ((y, 1) : G.Cˣ × ℚˣ)⁻¹ := by
    refine Prod.ext ?_ ?_
    · simp [mul_assoc]
    · simp
  refine ⟨⟨_, hmem⟩, hconj, ?_⟩
  refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) ?_
  · show x' * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * x'⁻¹ =
      (x' * Y * x⁻¹) * (x * Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) * x⁻¹) *
        (x' * Y * x⁻¹)⁻¹
    have e3 : Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) =
        Y⁻¹ * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * Y := by
      rw [map_mul, map_mul, map_inv]
    rw [e3]
    group
  · have e3 : ∀ a b : (AfP p)ˣ, b = a * b * a⁻¹ := fun a b => by
      rw [mul_comm a b, mul_inv_cancel_right]
    exact e3 (t' * T⁻¹ * t⁻¹) (Units.map (algebraMap ℚ (AfP p)).toMonoidHom γ'.1.2)
  · have e3 := congrArg ((inclG G 1).comp (locC G)) hconj
    rw [map_mul, map_mul, map_inv] at e3
    exact e3

theorem clsMove : ClsMove := by
  intro p _ G V _ _ ξ K J ψ θ e ⟨B, x, t, hx, Φ, hΦ, h0, he, hψ⟩
  have hrel : DForm.Rel B (Quot.out (Quot.mk _ B : DFCls G)) :=
    (GlobalTheory.LKDef.Regroup.dform_rel_equivalence.eqvGen_iff).1
      (Quot.eqvGen_exact (Quot.out_eq (Quot.mk DForm.Rel B)).symm)
  obtain ⟨y, s, hs, hβ⟩ := hrel
  obtain ⟨d, hd⟩ := conj_emb G B _ y s hs hβ x t hx _ _
    (Quot.out (Quot.mk _ B : DFCls G)).trivAf.choose_spec.choose_spec
  refine ⟨Quot.mk _ B, fun g => ξ (y, 1) (Φ (d⁻¹ * g)),
    mem_forms_move ξ _ _ _ _ _ _ d hd hΦ, fun h => h0 ?_, ?_, fun j => ?_⟩
  · funext g
    have := congrFun h (d * g)
    simp only [inv_mul_cancel_left, Pi.zero_apply] at this
    have h2 := congrArg (ξ ((y, 1) : G.Cˣ × ℚˣ)⁻¹) this
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h2
    exact h2
  · rw [op_move, he]
  · rw [op_move, hψ j]
    funext g
    simp

end UpperTheory.Gal.Spc
end
end

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.CertificateRingHomMap (wop wmul)
open UpperTheory.Gal.LocalSmoothExtension
open Formalism.UG (Hecke)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Abstract

variable {H : Type} [Group H] {K : Subgroup H} {M : Type} [AddCommGroup M] [Module ℂ M]
  {T : (H → ℂ) → Module.End ℂ M} {J : Type}

private theorem polyFn_single (ψ : J → H → ℂ) (w : List J) (c : ℂ) (f : H → ℂ) :
    polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f :=
  Finsupp.sum_single_index (zero_smul _ _)

private theorem polyFn_zero (ψ : J → H → ℂ) (f : H → ℂ) : polyFn K ψ 0 f = 0 :=
  Finsupp.sum_zero_index

private theorem polyFn_add (ψ : J → H → ℂ) (s t : List J →₀ ℂ) (f : H → ℂ) :
    polyFn K ψ (s + t) f = polyFn K ψ s f + polyFn K ψ t f :=
  Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

private theorem word_mem (ψ : J → H → ℂ) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (w : List J) :
    wordFn K ψ w f ∈ Hecke ℂ K := by
  have h := hmem (Finsupp.single w 1)
  rwa [polyFn_single, one_smul] at h

private theorem T_word (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) :
    T (wordFn K ψ w f) = (w.map fun j => T (ψ j)).prod * T f := by
  induction w with
  | nil => simp [wordFn]
  | cons j w ih =>
    have h : wordFn K ψ (j :: w) f = Formalism.UG.conv K (ψ j) (wordFn K ψ w f) := rfl
    rw [h, hmul _ (hψ j) _ (hmem w), ih, List.map_cons, List.prod_cons, mul_assoc]

private theorem T_poly (hT0 : T 0 = 0) (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, T (c • f + f') = c • T f + T f')
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K)
    (s : List J →₀ ℂ) : T (polyFn K ψ s f) = wop (fun j => T (ψ j)) s * T f := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero, hT0, UpperTheory.Gal.CertificateRingHomMap.wop_zero, zero_mul]
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h, hlin _ (hmem s) _ (hmem t), one_smul, hs, ht, UpperTheory.Gal.CertificateRingHomMap.wop_add, add_mul]
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h, hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _), hT0, add_zero,
      T_word hmul ψ hψ f (word_mem ψ f hmem) w, UpperTheory.Gal.CertificateRingHomMap.wop_single, smul_mul_assoc]

private theorem T_pow (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    T (powFn K u e n) = T u ^ n * T e := by
  induction n with
  | zero => simp [powFn]
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h, hmul _ hu _ (hmem n), ih, pow_succ', mul_assoc]

private theorem C_pow {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (u e : H → ℂ) (hu : u ∈ Hecke ℂ K) (he : C e) (hmem : ∀ n, powFn K u e n ∈ Hecke ℂ K) (n : ℕ) :
    C (powFn K u e n) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    have h : powFn K u e (n + 1) = Formalism.UG.conv K u (powFn K u e n) := Function.iterate_succ_apply' _ _ _
    rw [h]
    exact hid _ hu _ (hmem n) ih

private theorem C_word {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ w, wordFn K ψ w f ∈ Hecke ℂ K) (w : List J) : C (wordFn K ψ w f) := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact hid _ (hψ j) _ (hmem w) ih

private theorem C_poly {C : (H → ℂ) → Prop}
    (hid : ∀ a ∈ Hecke ℂ K, ∀ f ∈ Hecke ℂ K, C f → C (Formalism.UG.conv K a f)) (h0 : C 0)
    (hlin : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, ∀ c : ℂ, C f → C f' → C (c • f + f'))
    (ψ : J → H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (f : H → ℂ) (hf : C f)
    (hmem : ∀ s, polyFn K ψ s f ∈ Hecke ℂ K) (s : List J →₀ ℂ) : C (polyFn K ψ s f) := by
  induction s using Finsupp.induction_linear with
  | zero => rw [polyFn_zero]; exact h0
  | add s t hs ht =>
    have h : polyFn K ψ (s + t) f = (1 : ℂ) • polyFn K ψ s f + polyFn K ψ t f := by
      rw [one_smul, polyFn_add]
    rw [h]
    exact hlin _ (hmem s) _ (hmem t) _ hs ht
  | single w c =>
    have h : polyFn K ψ (Finsupp.single w c) f = c • wordFn K ψ w f + 0 := by
      rw [polyFn_single, add_zero]
    rw [h]
    exact hlin _ (word_mem ψ f hmem w) _ (Submodule.zero_mem _) _
      (C_word hid ψ hψ f hf (word_mem ψ f hmem) w) h0

private theorem hecke_relation_image (hmul : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, T (Formalism.UG.conv K f f') = T f * T f')
    (ψ : J → H → ℂ) (e u u' : H → ℂ) (hψ : ∀ j, ψ j ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K) (hu : u ∈ Hecke ℂ K)
    (hu' : u' ∈ Hecke ℂ K) (hrel : Rel (Formalism.UG.conv K) ψ e u u') (hB : Formalism.UG.conv K u e ∈ Hecke ℂ K)
    (hA : ∀ j, Formalism.UG.conv K (ψ j) e ∈ Hecke ℂ K) :
    Rel (· * ·) (fun j => T (ψ j)) (T e) (T u) (T u') := by
  refine ⟨?_, fun j => ?_, ?_, fun j j' => ?_, fun j => ?_, ?_⟩
  · have h := congrArg T hrel.idem
    rwa [hmul _ he _ he] at h
  · have h := congrArg T (hrel.eT j)
    rwa [hmul _ he _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T hrel.eu
    rwa [hmul _ he _ hB, hmul _ hu _ he] at h
  · have h := congrArg T (hrel.TT j j')
    rwa [hmul _ (hψ j) _ (hA j'), hmul _ (hψ j') _ he, hmul _ (hψ j') _ (hA j), hmul _ (hψ j) _ he] at h
  · have h := congrArg T (hrel.uT j)
    rwa [hmul _ hu _ (hA j), hmul _ (hψ j) _ he, hmul _ (hψ j) _ hB, hmul _ hu _ he] at h
  · have h := congrArg T hrel.inv
    rwa [hmul _ hu' _ hB, hmul _ hu _ he] at h

end Abstract

private theorem forms_fin {Γ H V : Type} [Group Γ] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V)
    (hf : Finite (DoubleCoset.Quotient (ι.range : Set H) (K : Set H))) :
    FiniteDimensional ℂ (HeckeTraceForms.forms ι K ξ) := by
  haveI := hf
  obtain ⟨r, hr⟩ : ∃ r : DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → H, ∀ g : H,
      ∃ γ : Γ, ∃ k ∈ K, g = ι γ * r (DoubleCoset.mk ι.range K g) * k := by
    refine ⟨fun q => Quotient.out q, fun g => ?_⟩
    obtain ⟨h, ⟨γ, rfl⟩, k, hk, e⟩ := (@DoubleCoset.eq _ _ ι.range K _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk ι.range K g))
    exact ⟨γ, k, hk, e⟩
  let L : HeckeTraceForms.forms ι K ξ →ₗ[ℂ] (DoubleCoset.Quotient (ι.range : Set H) (K : Set H) → V) :=
    { toFun := fun φ q => (φ : H → V) (r q)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective L ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  apply Subtype.ext
  funext g
  have h0 : (φ : H → V) (r (DoubleCoset.mk ι.range K g)) = 0 :=
    congrFun hφ (DoubleCoset.mk ι.range K g)
  obtain ⟨γ, k, hk, e⟩ := hr g
  have h1 : (φ : H → V) g = ξ γ ((φ : H → V) (r (DoubleCoset.mk ι.range K g))) := by
    conv_lhs => rw [e]
    rw [φ.2.2 k hk, φ.2.1]
  rw [h1, h0, map_zero]
  rfl

def SpecOfF : Prop := ForPlaces fun p _ G Lv C R => Finite (DFCls G) →
  ∀ (D : Datum p) (L : GlobalTheory.LKGeo.Link D G) (lam : (D.F →+* ℂ) → Fin G.n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ξ : Representation ℂ (G.Cˣ × ℚˣ) V), IsWt L lam ξ →
    ∀ (J : Type) (ψ : J → G.GAf → ℂ) (θ : J → ℂ) (e u u' : G.GAf → ℂ),
    (∀ j, ψ j ∈ Hecke ℂ Lv.K.toSubgroup) → e ∈ Hecke ℂ Lv.K.toSubgroup → u ∈ Hecke ℂ Lv.K.toSubgroup →
    u' ∈ Hecke ℂ Lv.K.toSubgroup → Rel (Formalism.UG.conv Lv.K.toSubgroup) ψ e u u' → C e →
    (∀ n : ℕ, 1 ≤ n → ∃ A : Set G.GAf, (∀ g ∈ A, R g ∧ RegAf G g) ∧ (∀ j a, ψ j a ≠ 0 → ∀ g ∈ A, a * g ∈ A) ∧
      ∀ g, powFn Lv.K.toSubgroup u e n g ≠ 0 → g ∈ A) →
    HasEig G ξ Lv.K.toSubgroup ψ θ e → ∃ n : ℕ, 1 ≤ n ∧ Spec L lam Lv.K.toSubgroup ψ θ (powFn Lv.K.toSubgroup u e n)

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.specOfF :
    UpperTheory.Gal.Spc.SpecOfF := by
  intro p _ G hGa Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁ hfin D L lam V _ _ _ ξ hwt J ψ θ e u u' hψ he hu hu' hrel hCe hA hEig
  have hW := words p G Lv J ψ e u u' hψ he hu hrel
  have hp : ∀ n, powFn Lv.K.toSubgroup u e n ∈ Hecke ℂ Lv.K.toSubgroup := fun n => (hW n).1
  have hpoly : ∀ n s, polyFn Lv.K.toSubgroup ψ s (powFn Lv.K.toSubgroup u e n) ∈ Hecke ℂ Lv.K.toSubgroup :=
    fun n => (hW n).2.1
  obtain ⟨hCi, hC0, hCl⟩ := cuspIdeal p G hGa Lv k P H S k₁ P₁
  obtain ⟨q₀, Φ₀, hΦ₀, hne, hΦe, hΦψ⟩ := clsMove p G V ξ Lv.K.toSubgroup J ψ θ e hEig
  letI : Fintype (DFCls G) := Fintype.ofFinite _
  have hop := fun q : DFCls G => opAlg p G Lv V ξ (Quot.out q)
  choose T hT0 hT using hop
  haveI hfd' : ∀ q : DFCls G, FiniteDimensional ℂ (HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G))
      (ξ.comp (grp G (Quot.out q).β).subtype)) := fun q =>
    forms_fin (Quot.out q).emb _ _ (GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level p G hGa Lv (Kp G) (Subgroup.Commensurable.refl _) (Quot.out q))
  have hmul : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup,
      T q (Formalism.UG.conv Lv.K.toSubgroup f f') = T q f * T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').1
  have hlin : ∀ q, ∀ f ∈ Hecke ℂ Lv.K.toSubgroup, ∀ f' ∈ Hecke ℂ Lv.K.toSubgroup, ∀ c : ℂ,
      T q (c • f + f') = c • T q f + T q f' := fun q f hf f' hf' => ((hT q f hf).2.2 f' hf').2
  have hB : Formalism.UG.conv Lv.K.toSubgroup u e ∈ Hecke ℂ Lv.K.toSubgroup := hp 1
  have hAj : ∀ j, Formalism.UG.conv Lv.K.toSubgroup (ψ j) e ∈ Hecke ℂ Lv.K.toSubgroup := fun j =>
    word_mem ψ _ (hpoly 0) [j]
  have key := specAlg (DFCls G) J
    (fun q => HeckeTraceForms.forms (Quot.out q).emb (Lv.K.toSubgroup.prod (Kp G)) (ξ.comp (grp G (Quot.out q).β).subtype))
    (fun q j => T q (ψ j)) (fun q => T q e) (fun q => T q u) (fun q => T q u') θ
    (fun q => hecke_relation_image (hmul q) ψ e u u' hψ he hu hu' hrel hB hAj)
    ⟨q₀, ⟨Φ₀, hΦ₀⟩, fun h => hne (congrArg Subtype.val h),
      Subtype.ext (((hT q₀ e he).1 ⟨Φ₀, hΦ₀⟩).trans hΦe),
      fun j => Subtype.ext (((hT q₀ (ψ j) (hψ j)).1 ⟨Φ₀, hΦ₀⟩).trans (hΦψ j))⟩
  obtain ⟨n, hn, a, ha⟩ := key
  refine ⟨n, hn, (hW n).2.2.1, V, inferInstance, inferInstance, inferInstance, ξ, hwt, fun s hs => ⟨a, ?_, ?_⟩⟩
  · obtain ⟨A, hAR, hAψ, hAp⟩ := hA n hn
    have hsup := (hW n).2.2.2 A hAψ hAp
    have hCF : S.Cusp (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) :=
      C_poly hCi hC0 hCl ψ hψ _ (C_pow hCi u e hu hCe hp n) (hpoly n) _
    have hR : ∀ g, polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n) g ≠ 0 →
        (P₁.at g).charpoly.Separable := fun g hg => (hAR g (hsup _ g hg)).1
    exact ⟨fun g hg => (hAR g (hsup _ g hg)).2,
      vanPairs p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR,
      vanForms p G hGa Lv k P H S k₁ P₁ _ (hpoly n _) hCF hR⟩
  · have hq : ∀ q : DFCls G, (Quot.out q).trace ξ Lv.K.toSubgroup
        (polyFn Lv.K.toSubgroup ψ (wmul a s) (powFn Lv.K.toSubgroup u e n)) (Kp G) (oneP G) =
        LinearMap.trace ℂ _ (wop (fun j => T q (ψ j)) (wmul a s) * (T q u ^ n * T q e)) := fun q => by
      rw [(hT q _ (hpoly n _)).2.1, T_poly (hT0 q) (hmul q) (hlin q) ψ hψ _ (hpoly n),
        T_pow (hmul q) u e hu hp n]
    unfold dTrace
    rw [finsum_eq_sum_of_fintype]
    simp only [hq]
    exact ha s hs
