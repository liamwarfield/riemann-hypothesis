module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagClassMeasureBoundLatticeStabiliserStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProjector
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.WittInt

theorem exists_projector {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ z ∈ Λ, P z ∈ Λ) ∧ (∀ z, P z ∈ W) ∧ ∀ z ∈ W, P z = z := by
  have hmul : ∀ y : V, ∃ s : nonZeroDivisors O, s • y ∈ Λ := fun y => by
    have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
    rw [Submodule.span_eq] at hs
    exact ⟨s, hs⟩
  have hunit : ∀ s : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O V) s) := fun s => by
    have := isLocalizedModule_id (nonZeroDivisors O) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := hunit
      surj := fun y => by
        obtain ⟨s, hs⟩ := hmul y
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hne : ∀ s : nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hsat : ∀ (s : nonZeroDivisors O) (v : V), (s : O) • v ∈ W → v ∈ W := fun s v h => by
    rw [← algebraMap_smul K] at h
    exact (W.smul_mem_iff (hne s)).1 h
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := (W.restrictScalars O).comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c v h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  let g : V →ₗ[K] V := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype (Λ.subtype ∘ₗ π) hunit)
  have hg : ∀ y : Λ, g y = π y := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hunit y
  refine ⟨g, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact (π _).2
  · obtain ⟨c, hc⟩ := hmul z
    refine hsat c _ ?_
    rw [← LinearMap.map_smul_of_tower]
    have := hg ⟨_, hc⟩
    rw [show g ((c : O) • z) = _ from this]
    exact hπ _
  · obtain ⟨c, hc⟩ := hmul z
    have h1 := hg ⟨_, hc⟩
    rw [hπ' ⟨_, hc⟩ ((W.restrictScalars O).smul_mem (c : O) hz)] at h1
    have h2 : g (algebraMap O K c • z) = algebraMap O K c • z := by
      rw [algebraMap_smul]; exact h1
    rw [map_smul] at h2
    exact smul_right_injective V (hne c) h2

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem form_star {J : Matrix (Fin n) (Fin n) E} (hJ : Jᴴ = J) (x y : Fin n → E) :
    star (star x ⬝ᵥ (J *ᵥ y)) = star y ⬝ᵥ (J *ᵥ x) := by
  rw [← star_dotProduct_star, star_star, star_mulVec, hJ, dotProduct_mulVec, dotProduct_comm]

theorem form_adj {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (M : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) :
    star (M *ᵥ x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ ((J⁻¹ * Mᴴ * J) *ᵥ y)) := by
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hd),
    Matrix.one_mul, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem form_nondeg {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (y : Fin n → E)
    (h : ∀ x : Fin n → E, star x ⬝ᵥ (J *ᵥ y) = 0) : y = 0 := by
  apply eq_zero_of_mulVec_eq_zero hd
  funext i
  have := h (Pi.single i 1)
  simpa [← Pi.single_star] using this

theorem exists_adjoint {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0)
    (P : (Fin n → E) →ₗ[E] (Fin n → E)) :
    ∃ Q : (Fin n → E) →ₗ[E] (Fin n → E),
      (∀ x y, star (P x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ Q y)) ∧
      LinearMap.trace E _ Q = star (LinearMap.trace E _ P) := by
  obtain ⟨M, rfl⟩ := Matrix.toLin'.surjective P
  refine ⟨Matrix.toLin' (J⁻¹ * Mᴴ * J), fun x y => form_adj hd M x y, ?_⟩
  rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_mul_cycle,
    mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul, trace_conjTranspose]

end Form

theorem split_of_trace (E : Type) [Field E] [NumberField E] [StarRing E] (w : 𝓞 E)
    (hw : (w : E) + star (w : E) = 1) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (hd : J.det ≠ 0)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hself : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (W : Submodule E (Fin n → E)) (hW : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) :
    ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧
      Module.finrank E W' = Module.finrank E W ∧
      (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧
      ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧
        ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  have hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
    let U := Submodule.span E (Λ : Set (Fin n → E))
    change U = ⊤
    by_contra hU
    let g : (Fin n → E) →ₗ[E] Module.Dual E U :=
      ((dotProductBilin E E).compl₂ (Matrix.mulVecLin J)).domRestrict₂ U
    have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E (Fin n → E) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hU
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    let y : Fin n → E := star z
    have hy₀ : y ≠ 0 := by
      intro hy
      apply hz₀
      have := congrArg star hy
      simpa [y] using this
    have hline (a : E) : a • y ∈ Λ := (hself _).2 fun x hx => by
      have hz' : z ⬝ᵥ (J *ᵥ x) = 0 :=
        congrArg (fun f : Module.Dual E U => f ⟨x, Submodule.subset_span hx⟩)
          (LinearMap.mem_ker.mp hz)
      have horth : star x ⬝ᵥ (J *ᵥ y) = 0 := by
        rw [← form_star hJ y x]
        simp [y, hz']
      simp only [Matrix.mulVec_smul, dotProduct_smul, horth, smul_zero]
      exact ⟨0, map_zero _⟩
    let i : E →ₗ[𝓞 E] Λ :=
      ((LinearMap.toSpanSingleton E _ y).restrictScalars (𝓞 E)).codRestrict Λ hline
    let : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hy₀ (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨P, hPΛ, hPW, hPid⟩ := exists_projector Λ hΛ.fg hspan W
  obtain ⟨Q, hPQ, htr⟩ := exists_adjoint hd P
  have hQP : ∀ x y, star (Q x) ⬝ᵥ (J *ᵥ y) = star x ⬝ᵥ (J *ᵥ P y) := fun x y => by
    rw [← form_star hJ, ← hPQ, form_star hJ]
  have hQΛ : ∀ z ∈ Λ, Q z ∈ Λ := fun z hz => (hself _).2 fun y hy => by
    rw [← hPQ]; exact (hself z).1 hz _ (hPΛ y hy)
  have hQ0 : ∀ y, (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → Q y = 0 := fun y hy =>
    form_nondeg hd _ fun x => by rw [← hPQ]; exact hy _ (hPW x)
  have hQW : ∀ y ∈ W, Q y = 0 := fun y hy => hQ0 y fun x hx => hW x hx y hy
  have hPP : ∀ y, P (P y) = P y := fun y => hPid _ (hPW y)
  have hQQ : ∀ y, Q (Q y) = Q y := fun y => by
    rw [← sub_eq_zero]
    refine form_nondeg hd _ fun x => ?_
    rw [mulVec_sub, dotProduct_sub, ← hPQ, ← hPQ, hPP, hPQ, sub_self]
  have hQPz : ∀ y, Q (P y) = 0 := fun y => hQW _ (hPW y)
  let T : (Fin n → E) →ₗ[E] (Fin n → E) := Q - (w : E) • (P ∘ₗ Q)
  have hT : ∀ y, T y = Q y - (w : E) • P (Q y) := fun y => rfl
  have hQT : ∀ y, Q (T y) = Q y := fun y => by
    rw [hT, map_sub, map_smul, hQPz, hQQ, smul_zero, sub_zero]
  have hTT : ∀ y, T (T y) = T y := fun y => by rw [hT (T y), hQT, hT]
  have hWT : ∀ x ∈ W, ∀ y, star x ⬝ᵥ (J *ᵥ T y) = star x ⬝ᵥ (J *ᵥ y) := fun x hx y => by
    rw [hT, mulVec_sub, dotProduct_sub, hW x hx _ (W.smul_mem _ (hPW _)), sub_zero, ← hPQ, hPid x hx]
  have hTl : ∀ x y, star (T x) ⬝ᵥ (J *ᵥ y) =
      star x ⬝ᵥ (J *ᵥ (P y - star (w : E) • P (Q y))) := fun x y => by
    rw [hT, star_sub, star_smul, sub_dotProduct, smul_dotProduct, hPQ, hQP, hQP, mulVec_sub,
      dotProduct_sub, mulVec_smul, dotProduct_smul]
  refine ⟨LinearMap.range T, ?_, ?_, ?_, fun z hz => ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hTl, hQT, hT, map_sub, map_smul, hPP, sub_sub, ← add_smul, hw, one_smul, sub_self, mulVec_zero,
      dotProduct_zero]
  · have h1 : LinearMap.IsProj W P := ⟨hPW, hPid⟩
    have h2 : LinearMap.IsProj (LinearMap.range T) T :=
      ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hTT x⟩
    have h3 : Q ∘ₗ P = 0 := LinearMap.ext hQPz
    have h4 : LinearMap.trace E _ T = LinearMap.trace E _ Q := by
      simp only [T]
      rw [map_sub, map_smul, LinearMap.trace_comp_comm', h3, map_zero, smul_zero, sub_zero]
    rw [h2.trace, htr, h1.trace, star_natCast] at h4
    exact_mod_cast h4
  · rintro _ ⟨y, rfl⟩ hy
    have h0 : Q y = 0 := hQ0 y fun x hx => by rw [← hWT x hx]; exact hy x hx
    rw [hT, h0, map_zero, smul_zero, sub_zero]
  · have hTz : T z ∈ Λ := Λ.sub_mem (hQΛ z hz) (Λ.smul_mem w (hPΛ _ (hQΛ z hz)))
    have hu : z - T z ∈ Λ := Λ.sub_mem hz hTz
    have hxW : P (z - T z) ∈ W := hPW _
    have hQu : Q (z - T z) = 0 := by rw [map_sub, hQT, sub_self]
    refine ⟨P (z - T z), hPΛ _ hu, T z, hTz, hxW, ⟨z, rfl⟩, fun t ht => ?_⟩
    obtain ⟨a, ha, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ht
    rw [star_add, add_dotProduct, hTl, sub_right_comm, map_sub P (z - T z), map_sub Q (z - T z), hQu, hQPz, hPP, sub_self,
      sub_self, map_zero, smul_zero, sub_self, mulVec_zero, dotProduct_zero, add_zero, mulVec_sub,
      mulVec_sub, dotProduct_sub, dotProduct_sub, hWT a ha, hW a ha _ hxW, sub_self, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∀ W : Submodule E (Fin n → E), (∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → ∃ W' : Submodule E (Fin n → E), (∀ x ∈ W', ∀ y ∈ W', star x ⬝ᵥ (J *ᵥ y) = 0) ∧ Module.finrank E W' = Module.finrank E W ∧ (∀ y ∈ W', (∀ x ∈ W, star x ⬝ᵥ (J *ᵥ y) = 0) → y = 0) ∧ ∀ z ∈ Λ, ∃ x ∈ Λ, ∃ y ∈ Λ, x ∈ W ∧ y ∈ W' ∧ ∀ t ∈ W ⊔ W', star t ⬝ᵥ (J *ᵥ (z - x - y)) = 0 := by
  intro E _ _ _ hE n J hJ hd Λ hΛ hs W hW
  obtain ⟨w, hw⟩ := GlobalTheory.TraceOnto.exists_trace_one E hE
  exact split_of_trace E w hw n J hJ hd Λ hΛ hs W hW

end GlobalTheory.WittInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.AdaptedExists

theorem exists_complement (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q : ℕ) (he : ∀ y, e (star y) = star (e y))
    {κ : Type} [Fintype κ] [DecidableEq κ] (hI : HasSig I p q)
    (hI₀ : HasSig I₀ (p - Fintype.card κ) (q - Fintype.card κ)) (hn : I.n = I₀.n + 2 * Fintype.card κ)
    (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hΛ : Submodule.IsLattice I.E Λ)
    (hdual : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (I.J *ᵥ x) ∈ (algebraMap (𝓞 I.E) I.E).range)
    (T T' : Matrix (Fin I.n) κ I.E) (B : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (h1 : Tᴴ * I.J * T = 0) (h2 : T'ᴴ * I.J * T' = 0) (h3 : Tᴴ * I.J * T' = 1) (h4 : Tᴴ * I.J * B = 0)
    (h5 : T'ᴴ * I.J * B = 0) (h6 : (Bᴴ * I.J * B).det ≠ 0)
    (h7 : ∀ z ∈ Λ, ∃ y, B *ᵥ y ∈ Λ ∧ (Bᴴ * I.J) *ᵥ (z - B *ᵥ y) = 0) :
    ∃ (γ : GL (Fin I₀.n) I.E) (x₀ : I₀.Gf), (B * γ.1)ᴴ * I.J * (B * γ.1) = I₀.J.map e ∧
      ∀ y, y ∈ lamX I₀ (1, x₀) ↔ ((B * γ.1) *ᵥ fun l => e (y l)) ∈ Λ := by
  obtain ⟨xΛ, hxΛ⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I Λ hΛ (by simpa only [hform_eq] using hdual)
  have hΛfull : Submodule.IsFullLattice I.E Λ :=
    { toIsLattice := hΛ
      span_eq_top := by rw [← hxΛ]; exact (GlobalTheory.PointLattice.lamX_selfDual I (1, xΛ)).2.2.1 }
  have he' : ∀ y, e.symm (star y) = star (e.symm y) := fun y => e.injective (by simp [he])
  set G : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E := (Bᴴ * I.J * B).map e.symm with hG
  have hGe : Bᴴ * I.J * B = G.map e := by ext r s; exact (e.apply_symm_apply _).symm
  have hGd : G.det ≠ 0 := fun h => h6 (by
    rw [hGe]; exact ((e : I₀.E →+* I.E).map_det G).symm.trans (by rw [h, map_zero]))
  have hGh : Gᴴ = G := by
    rw [hG, ← Matrix.conjTranspose_map _ he', ← gram_swap (J_herm I)]
  obtain ⟨L, hL, -, hLd⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J B G Λ (J_herm I) hGe hGd hΛfull hdual h7
  obtain ⟨γ, hγ⟩ := GlobalTheory.FlagMeas.sameKindIsometric I₀.E I₀.cm.cmUnram I₀.n G I₀.J hGh (J_herm I₀) hGd I₀.J_det ⟨L, hL.toIsLattice, hLd⟩
    ⟨I₀.L, Submodule.IsLattice.of_fg I₀.E I₀.L_fg, by simpa only [hform_eq] using I₀.L_dual⟩ (fun φ => by
      refine ⟨_, _, ?_, hasSignature_map I₀ _ _ hI₀ φ⟩
      set ψ : I.E →+* ℂ := φ.comp e.symm.toRingHom
      have hψ : ∀ x, ψ (star x) = star (ψ x) := I.cm.cmUnram.2.1 ψ
      have hm : G.map φ = (B.map ψ)ᴴ * I.J.map ψ * B.map ψ := by rw [map_gram ψ hψ]; rfl
      rw [hm]
      refine hasSignature_complement _ _ p q κ _ (T.map ψ) (T'.map ψ) _ ?_ (hasSignature_map I p q hI ψ) hn ?_ ?_ ?_ ?_ ?_ ?_
      · rw [← Matrix.conjTranspose_map _ hψ, J_herm]
      · rw [map_gram ψ hψ, h1, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h2, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h3, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
      · rw [map_gram ψ hψ, h4, Matrix.map_zero _ (map_zero ψ)]
      · rw [map_gram ψ hψ, h5, Matrix.map_zero _ (map_zero ψ)]
      · rw [← hm]
        exact fun h => hGd (φ.injective ((φ.map_det G).trans (h.trans (map_zero φ).symm))))
  set γ' : GL (Fin I₀.n) I.E := Matrix.GeneralLinearGroup.map (e : I₀.E →+* I.E) γ
  have hγ' : γ'.1 = γ.1.map (e : I₀.E →+* I.E) := rfl
  have hT : (B * γ'.1)ᴴ * I.J * (B * γ'.1) = I₀.J.map e := by
    have := map_gram (e : I₀.E →+* I.E) he G γ.1 γ.1
    rw [hγ, ← hγ'] at this
    refine Eq.trans ?_ this
    rw [show G.map (e : I₀.E →+* I.E) = _ from hGe.symm]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨L', hL', hm, hLd'⟩ := exists_factor_lattice I.E I₀.E e he _ _ I.J (B * γ'.1) I₀.J Λ (J_herm I) hT I₀.J_det hΛfull hdual
    fun z hz => by
      obtain ⟨y, hy, hy'⟩ := h7 z hz
      have : (B * γ'.1) *ᵥ (γ'⁻¹.1 *ᵥ y) = B *ᵥ y := by
        rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      refine ⟨γ'⁻¹.1 *ᵥ y, by rwa [this], ?_⟩
      rw [this, conjTranspose_mul, Matrix.mul_assoc, ← mulVec_mulVec, hy', mulVec_zero]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.SelfDualPoint.exists_lamX_eq I₀ L' hL'.toIsLattice (by simpa only [hform_eq] using hLd')
  exact ⟨γ', x₀, hT, by rwa [hx₀]⟩

theorem exists_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  intro I I₀ e p q a j he hI hp hq hI₀ xf S ⟨h0, hmono, hrk, hsat, hiso⟩
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  simp only [hform_eq] at hdual hiso
  have hn : I.n = I₀.n + 2 * ∑ i, j i := by
    have h1 := (GlobalTheory.FlagMeas.instance_numbers I).2.2.2.2.2 _ _ hI
    have h2 := (GlobalTheory.FlagMeas.instance_numbers I₀).2.2.2.2.2 _ _ hI₀
    omega
  have hle : ∀ k, S k ≤ lamX I (1, xf) := fun k y hy => ((hsat k y).1 hy).1
  have hSfg : (S (Fin.last a)).FG := hfg.of_le (hle _)
  obtain ⟨A, hA⟩ := GlobalTheory.saturatedFlag_splits I.E I.n a S h0 hmono hSfg fun i y hy h => (hsat i y).2 ⟨hle _ hy, h⟩
  obtain ⟨Λ, Ti, hΛ, hS⟩ := exists_blocks I.E I.n a j S A h0 hmono hSfg hrk hA
  set κ := Σ i, Fin (j i)
  have hκ : Fintype.card κ = ∑ i, j i := by simp [κ]
  have hsum : ∀ (M : Matrix (Fin I.n) κ I.E) (u : κ → I.E),
      M *ᵥ u = ∑ i, M.submatrix id (Sigma.mk i) *ᵥ fun s => u ⟨i, s⟩ := fun M u => by
    ext r
    simp [mulVec, dotProduct, Finset.sum_apply, κ, Fintype.sum_sigma]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin I.n) κ I.E, ∀ i, Ti i = T.submatrix id (Sigma.mk i) :=
    ⟨fun r s => Ti s.1 r s.2, fun _ => rfl⟩
  have hlast : ∀ z, z ∈ S (Fin.last a) ↔ ∃ u : κ → I.E, (∀ i, (fun s => u ⟨i, s⟩) ∈ Λ i) ∧ z = T *ᵥ u := fun z => by
    rw [hS]
    refine ⟨fun ⟨u, hu, _, hz⟩ => ⟨fun s => u s.1 s.2, hu, by rw [hsum, hz]; simp only [hT]⟩,
      fun ⟨u, hu, hz⟩ => ⟨_, hu, fun i hi => absurd (Fin.castSucc_lt_last i) hi, by rw [hz, hsum]; simp only [hT]⟩⟩
  have hone : ∀ i, ∀ t ∈ Λ i, Ti i *ᵥ t ∈ S (Fin.last a) := fun i t ht => by
    refine (hS _ _).2 ⟨Pi.single i t, fun k => ?_, fun i hi => absurd (Fin.castSucc_lt_last i) hi, ?_⟩
    · by_cases h : k = i
      · subst h; simpa using ht
      · simp [h]
    · rw [Finset.sum_eq_single i] <;> simp +contextual
  set W := Submodule.span I.E (S (Fin.last a) : Set (Fin I.n → I.E)) with hW
  have hrange : LinearMap.range T.mulVecLin = W := by
    refine le_antisymm ?_ (Submodule.span_le.2 fun z hz => ?_)
    · rintro _ ⟨u, rfl⟩
      rw [mulVecLin_apply, hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) ≤ W.comap (Ti i).mulVecLin :=
        Submodule.span_le.2 fun t ht => Submodule.subset_span (hone i t ht)
      rw [← hT]
      have hsp := Submodule.IsFullLattice.span_eq_top (self := hΛ i)
      exact this (hsp ▸ Submodule.mem_top)
    · obtain ⟨u, -, rfl⟩ := (hlast z).1 hz
      exact ⟨u, rfl⟩
  have hdim : Module.finrank I.E W = Fintype.card κ := by
    have := telescope a j (fun k => Formalism.HN.rkK (S k)) hrk
    simp only [h0] at this
    rw [hκ]
    rw [show Formalism.HN.rkK (⊥ : Submodule (𝓞 I.E) (Fin I.n → I.E)) = 0 by
      rw [Formalism.HN.rkK, Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot], zero_add] at this
    exact this
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ (I.J *ᵥ y) = 0 := fun x hx y hy => by
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact hiso x hx y hy
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp [h, h']
    | add_right x y z _ _ _ h h' => simp [mulVec_add, h, h']
    | smul_left c x y _ _ h => simp [h]
    | smul_right c x y _ _ h => simp [mulVec_smul, h]
  obtain ⟨W', hW'iso, hW'dim, hW'nd, hsplit⟩ := GlobalTheory.WittInt.main I.E I.cm.cmUnram I.n I.J (J_herm I) I.J_det _
    (Submodule.IsLattice.of_fg I.E hfg) hdual W hWiso
  obtain ⟨T', B, hrange', h3, h6, hB⟩ := exists_witt I.E I.n I₀.n κ I.J T W W' (J_herm I) I.J_det (hκ ▸ hn) hrange hdim
    (hW'dim.trans hdim) hWiso hW'iso hW'nd
  have mT : ∀ u, T *ᵥ u ∈ W := fun u => hrange ▸ ⟨u, rfl⟩
  have mT' : ∀ u, T' *ᵥ u ∈ W' := fun u => hrange' ▸ ⟨u, rfl⟩
  have h1 : Tᴴ * I.J * T = 0 := gram_eq_zero _ _ _ fun x y => hWiso _ (mT x) _ (mT y)
  have h2 : T'ᴴ * I.J * T' = 0 := gram_eq_zero _ _ _ fun x y => hW'iso _ (mT' x) _ (mT' y)
  have h4 : Tᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_left (mT x))
  have h5 : T'ᴴ * I.J * B = 0 := gram_eq_zero _ _ _ fun x y =>
    (hB _).1 ⟨y, rfl⟩ _ (Submodule.mem_sup_right (mT' x))
  have hdec : ∀ z ∈ lamX I (1, xf), ∃ u u' y, T *ᵥ u ∈ S (Fin.last a) ∧ T' *ᵥ u' ∈ lamX I (1, xf) ∧
      B *ᵥ y ∈ lamX I (1, xf) ∧ z = T *ᵥ u + T' *ᵥ u' + B *ᵥ y := fun z hz => by
    obtain ⟨x, hx, y, hy, hxW, hyW, h⟩ := hsplit z hz
    obtain ⟨w, hw⟩ := (hB _).2 h
    have hxS := (hsat _ x).2 ⟨hx, hxW⟩
    rw [← hrange] at hxW
    rw [← hrange'] at hyW
    obtain ⟨u, rfl⟩ := hxW
    obtain ⟨u', rfl⟩ := hyW
    simp only [mulVecLin_apply] at hw hx hy hxS
    exact ⟨u, u', w, hxS, hy, hw ▸ sub_mem (sub_mem hz hx) hy, by rw [hw]; abel⟩
  obtain ⟨γ, x₀, hG, hx₀⟩ := exists_complement I I₀ e p q he hI (hκ ▸ hI₀) (hκ ▸ hn) _ (Submodule.IsLattice.of_fg I.E hfg) hdual T T' B
    h1 h2 h3 h4 h5 h6 fun z hz => by
      obtain ⟨u, u', y, -, -, hy, rfl⟩ := hdec z hz
      refine ⟨y, hy, ?_⟩
      rw [add_sub_cancel_right, mulVec_add, mulVec_mulVec, mulVec_mulVec, gram_swap (J_herm I) T,
        gram_swap (J_herm I) T', h4, h5]
      simp
  have hsub : ∀ {l : Type} (M : Matrix (Fin I.n) κ I.E) (N : Matrix (Fin I.n) l I.E) {k₁ k₂ : Type}
      (f : k₁ → κ) (g : k₂ → l),
      (M.submatrix id f)ᴴ * I.J * N.submatrix id g = (Mᴴ * I.J * N).submatrix f g := fun M N _ _ f g => by
    ext r s
    simp [Matrix.mul_apply]
  have hpair : ∀ i t u', star (Ti i *ᵥ t) ⬝ᵥ (I.J *ᵥ (T' *ᵥ u')) = star t ⬝ᵥ fun s => u' ⟨i, s⟩ := fun i t u' => by
    rw [form_mulVec, hT, ← Matrix.submatrix_id_id T', hsub, h3]
    congr 1
    ext s
    simp [mulVec, dotProduct, Matrix.one_apply]
  refine ⟨Λ, x₀, Ti, fun i => T'.submatrix id fun s => ⟨i, s⟩, B * γ.1, he, hn, hΛ, fun i k => ⟨?_, ?_, fun h => ?_⟩,
    fun i => ⟨?_, ?_, ?_⟩, hG, fun z => ⟨fun hz => ?_, ?_⟩, hS⟩
  · rw [hT, hT, hsub, h1]; rfl
  · rw [hsub, h2]; rfl
  · rw [hT, hsub, h3]
    ext r s
    simp [h]
  · rw [hT, hsub, h3]
    ext r s
    simp [Matrix.one_apply]
  · rw [← Matrix.mul_assoc, hT, ← Matrix.submatrix_id_id B, hsub, h4]
    simp
  · rw [← Matrix.mul_assoc, ← Matrix.submatrix_id_id B, hsub, h5]
    simp
  · obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := hdec z hz
    obtain ⟨v, hv, hv'⟩ := (hlast _).1 hu
    have hy' : ((B * γ.1) *ᵥ fun l => e (e.symm ((γ⁻¹.1 *ᵥ y) l))) = B *ᵥ y := by
      simp only [e.apply_symm_apply]
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    refine ⟨fun i s => v ⟨i, s⟩, fun i s => u' ⟨i, s⟩, fun l => e.symm ((γ⁻¹.1 *ᵥ y) l), hv, fun i t ht => ?_,
      (hx₀ _).2 (hy' ▸ hy), ?_⟩
    · rw [← hpair]
      exact (hdual _).1 hu' _ (hle _ (hone i t ht))
    · rw [hy', hv', hsum T, hsum T']
      simp only [hT]
  · rintro ⟨u, u', y, hu, hu', hy, rfl⟩
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => hle _ (hone i _ (hu i))) ?_) ((hx₀ y).1 hy)
    have e1 := hsum T' fun s => u' s.1 s.2
    refine e1 ▸ (hdual _).2 fun w hw => ?_
    obtain ⟨v, v', y', hv, -, -, rfl⟩ := hdec w hw
    obtain ⟨t, ht, ht'⟩ := (hlast _).1 hv
    rw [star_add, star_add, add_dotProduct, add_dotProduct, form_mulVec _ T', form_mulVec _ B, h2,
      gram_swap (J_herm I) T', h5, ht', hsum T, star_sum, sum_dotProduct]
    simp only [← hT, hpair, conjTranspose_zero, zero_mulVec, dotProduct_zero, add_zero]
    exact Subring.sum_mem _ fun i _ => hu' i _ (ht i)

end GlobalTheory.AdaptedExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adaptedBasis_saturatedIsotropicFlag : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  first | exact @GlobalTheory.AdaptedExists.exists_isAdapted | exact GlobalTheory.AdaptedExists.exists_isAdapted | (intros; apply GlobalTheory.AdaptedExists.exists_isAdapted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsSatFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagSat

theorem mem_of_isSat (I : AutInst) (x : I.GA) {N : Submodule (𝓞 I.E) (Fin I.n → I.E)}
    (hN : Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) N) {y : Fin I.n → I.E}
    (hy : y ∈ lamX I x) (hy' : y ∈ Submodule.span I.E (N : Set (Fin I.n → I.E))) : y ∈ N := by
  set A : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
    lamX I x ⊓ (Submodule.span I.E (N : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) with hA
  have hle : N ≤ A := fun z hz => ⟨hN.1 hz, Submodule.subset_span hz⟩
  have hAL : A ≤ lamX I x := inf_le_left
  have e : N = A := by
    by_contra hne
    have h1 := GlobalTheory.PointFlag.rkK_lt _ _ (GlobalTheory.PointFlag.frm_unit I x) (GlobalTheory.PointFlag.fg_of_le I x hAL)
      (GlobalTheory.PointFlag.isSat_of_le _ _ hN hle hAL) hne
    have h2 : Submodule.span I.E (A : Set (Fin I.n → I.E)) ≤ Submodule.span I.E (N : Set (Fin I.n → I.E)) :=
      Submodule.span_le.2 fun z hz => hz.2
    exact absurd h1 (not_lt.2 (Submodule.finrank_mono h2))
  rw [e]
  exact ⟨hy, hy'⟩

theorem exists_isSatFlag : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) (x : I.GA), x ∈ typeSet I j B → ∃ S, IsSatFlag I (lamX I (1, x.2)) j S ∧ sizesAt I x.2 S x.1 ∈ B := by
  rintro I a j B x ⟨τ, hτ, S, hS, hj⟩
  refine ⟨S, ⟨hS.1, hS.2.1.monotone, hj, fun i y => ?_, ?_⟩, ?_⟩
  · have h := GlobalTheory.PointFlag.flag_sat hS i
    exact ⟨fun hy => ⟨h.1 hy, Submodule.subset_span hy⟩, fun hy => mem_of_isSat I x h hy.1 hy.2⟩
  · rw [hS.2.2.1]
    exact (GlobalTheory.FlagIso.flag_isotropic I x).1
  · have e : sizesAt I x.2 S x.1 = τ := funext fun i => (hS.2.2.2.2.1 i).2.2.2
    rw [e]
    exact hτ

end GlobalTheory.FlagSat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolProdLeTsumSlices
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem covol_prod_le_tsum_slices : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂] [MeasurableMul G₂] (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SigmaFinite μ₁] [SigmaFinite μ₂] [μ₂.IsMulLeftInvariant] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (A : Set (G₁ × G₂)) (ι : Type) [Countable ι] (x : ι → G₂) (Γc Ac : ι → Set G₁), MeasurableSet (K : Set G₂) → (∀ c, ∀ g ∈ Γc c, ∃ γ ∈ Γ, γ.1 = g ∧ (x c)⁻¹ * γ.2 * x c ∈ K) → (∀ y ∈ A, ∃ c, ∃ γ ∈ Γ, ∃ k ∈ K, γ.2 * y.2 = x c * k ∧ γ.1 * y.1 ∈ Ac c) → μ₂ K ≠ ⊤ → covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤ μ₂ K * ∑' c, covol (Γc c) μ₁ (Ac c) := by
  intro G₁ G₂ _ _ _ _ _ μ₁ μ₂ _ _ _ Γ K A ι _ x Γc Ac hK hΓ hA hfin
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
  obtain ⟨ε', hε', hsum⟩ := ENNReal.exists_pos_sum_of_countable (ε := (ε : ENNReal))
    (by exact_mod_cast hε.ne') ι
  have key : ∀ c, ∃ D : Set G₁, MeasurableSet D ∧
      μ₂ K * μ₁ D ≤ μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c ∧
      (D = Set.univ ∨ ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D) := by
    intro c
    by_cases h0 : μ₂ K = 0
    · exact ⟨Set.univ, MeasurableSet.univ, by simp [h0], Or.inl rfl⟩
    · have hc : μ₂ K * covol (Γc c) μ₁ (Ac c) ≠ ⊤ :=
        ne_top_of_le_ne_top hb.ne (by
          gcongr
          exact le_tsum (fun i => covol (Γc i) μ₁ (Ac i)) c)
      have hlt : μ₂ K * covol (Γc c) μ₁ (Ac c) < μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c :=
        ENNReal.lt_add_right hc (by exact_mod_cast (hε' c).ne')
      have h2 : μ₂ K * covol (Γc c) μ₁ (Ac c) = ⨅ (D : Set G₁) (_ : MeasurableSet D)
          (_ : ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D), μ₂ K * μ₁ D := by
        simp only [covol, ENNReal.mul_iInf_of_ne h0 hfin]
      rw [h2] at hlt
      simp only [iInf_lt_iff] at hlt
      obtain ⟨D, hD, hcov, hlt⟩ := hlt
      rw [← h2] at hlt
      exact ⟨D, hD, hlt.le, Or.inr hcov⟩
  choose D hDm hDle hDcov using key
  have hKm : ∀ c, MeasurableSet ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)) := fun c =>
    measurable_const_mul _ hK
  have h1 : covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤
      (μ₁.prod μ₂) (⋃ c, D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂))) := by
    refine iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion fun c => (hDm c).prod (hKm c))
      (iInf_le_of_le ?_ le_rfl))
    intro y hy
    obtain ⟨c, γ, hγ, k, hk, h2, h1⟩ := hA y hy
    rcases hDcov c with hu | hcov
    · refine ⟨γ, hγ, Set.mem_iUnion.2 ⟨c, by simp [hu], ?_⟩⟩
      simpa [h2] using hk
    · obtain ⟨g, hg, hgD⟩ := hcov _ h1
      obtain ⟨δ, hδ, rfl, hδK⟩ := hΓ c g hg
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, Set.mem_iUnion.2 ⟨c, by simpa [mul_assoc] using hgD, ?_⟩⟩
      have := K.mul_mem hδK hk
      simpa [mul_assoc, h2] using this
  refine h1.trans ((measure_iUnion_le _).trans ?_)
  calc ∑' c, (μ₁.prod μ₂) (D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)))
      ≤ ∑' c, (μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        rw [Measure.prod_prod, measure_preimage_mul, mul_comm]
        exact hDle c
    _ ≤ _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        exact add_le_add le_rfl hsum.le

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBound
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagUnfold

theorem tsum_pi_prod_le {ι : Type} [Fintype ι] {α : ι → Type} (f : ∀ i, α i → ENNReal) :
    ∑' t : ∀ i, α i, ∏ i, f i (t i) ≤ ∏ i, ∑' x, f i x := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ t ∈ s, ∏ i, f i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, f i (t i) := by
        refine Finset.sum_le_sum_of_subset fun t ht => ?_
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ x ∈ s.image (fun t => t i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod' fun i _ => ENNReal.sum_le_tsum _

abbrev latRel (E : Type) [Field E] [NumberField E] (j : ℕ) :
    {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} →
      {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} → Prop :=
  fun Λ Λ' => ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1

theorem latRel_equiv (E : Type) [Field E] [NumberField E] (j : ℕ) : Equivalence (latRel E j) := by
  refine ⟨fun Λ => ⟨1, fun y => by simp⟩, ?_, ?_⟩
  · rintro Λ Λ' ⟨γ, h⟩
    refine ⟨γ⁻¹, fun y => ?_⟩
    rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · rintro Λ Λ' Λ'' ⟨γ, h⟩ ⟨δ, h'⟩
    refine ⟨δ * γ, fun y => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h', h]

theorem countable_lattices (E : Type) [Field E] [NumberField E] (j : ℕ) :
    Countable {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ} := by
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  have h : ∀ Λ : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsFullLattice E Λ},
      ∃ s : Finset (Fin j → E), Submodule.span (𝓞 E) (s : Set (Fin j → E)) = Λ.1 := fun Λ =>
    Λ.2.toIsLattice.fg
  choose s hs using h
  refine Function.Injective.countable (f := s) fun a b hab => Subtype.ext ?_
  rw [← hs a, ← hs b, hab]

theorem exists_kSub (I : AutInst) : ∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset :=
  ⟨(Formalism.UG.stabGL I.Lf).comap (Subgroup.subtype _), rfl⟩

def dcRel {G₁ G₂ : Type} [Group G₁] [Group G₂] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (x y : G₂) : Prop :=
  ∃ γ ∈ Γ, ∃ k ∈ K, γ.2 * x = y * k

theorem dcRel_equiv {G₁ G₂ : Type} [Group G₁] [Group G₂] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) :
    Equivalence (dcRel Γ K) := by
  refine ⟨fun x => ⟨1, Γ.one_mem, 1, K.one_mem, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨γ, hγ, k, hk, h⟩
    refine ⟨γ⁻¹, Γ.inv_mem hγ, k⁻¹, K.inv_mem hk, ?_⟩
    have : y = γ.2 * x * k⁻¹ := by rw [h]; group
    rw [this, Prod.snd_inv]; group
  · rintro x y z ⟨γ, hγ, k, hk, h⟩ ⟨δ, hδ, l, hl, h'⟩
    refine ⟨δ * γ, Γ.mul_mem hδ hγ, l * k, K.mul_mem hl hk, ?_⟩
    rw [Prod.snd_mul, mul_assoc, h, ← mul_assoc, h', mul_assoc]

theorem countable_dc {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
    [SecondCountableTopology G₂] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (hK : IsOpen (K : Set G₂)) :
    Countable (Quot (dcRel Γ K)) := by
  have : DiscreteTopology (G₂ ⧸ K) := QuotientGroup.discreteTopology hK
  have : Countable (G₂ ⧸ K) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  refine Function.Surjective.countable (f := fun c : G₂ ⧸ K => Quot.mk (dcRel Γ K) c.out) ?_
  rintro ⟨x⟩
  refine ⟨(x : G₂ ⧸ K), Quot.sound ?_⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  exact ⟨1, Γ.one_mem, k, k.2, by rw [hk]; simp⟩

theorem rel_out {α : Type} {r : α → α → Prop} (hr : Equivalence r) (x : α) : r x (Quot.out (Quot.mk r x)) :=
  hr.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (Quot.mk r x)).symm)

theorem sum_covol_le {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [T2Space G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SigmaFinite μ₁] [SigmaFinite μ₂] [μ₁.IsMulLeftInvariant]
    [μ₂.IsMulLeftInvariant] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (hc : (Γ : Set (G₁ × G₂)).Countable)
    (hfin : ∀ C, IsCompact C → ((Γ : Set (G₁ × G₂)) ∩ C).Finite) (hinj : ∀ γ ∈ Γ, γ.1 = 1 → γ = 1)
    (hKc : IsCompact (K : Set G₂)) (hKo : IsOpen (K : Set G₂)) :
    μ₂ K * ∑' d : Quot (dcRel Γ K),
      covol {g | ∃ γ ∈ Γ, γ.1 = g ∧ (Quot.out d)⁻¹ * γ.2 * Quot.out d ∈ K} μ₁ Set.univ ≤
      covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) Set.univ := by
  have := countable_dc Γ K hKo
  have hF : ∀ x : G₂, ∃ F : Set G₁, MeasurableSet F ∧
      (∀ y, ∃ g ∈ {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K}, g * y ∈ F) ∧
      ∀ g ∈ {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K}, ∀ y ∈ F, g * y ∈ F → g = 1 := by
    intro x
    let Δ : Subgroup G₁ :=
      { carrier := {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K}
        one_mem' := ⟨1, Γ.one_mem, rfl, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨γ, h1, rfl, h2⟩ ⟨δ, h3, rfl, h4⟩
          refine ⟨γ * δ, Γ.mul_mem h1 h3, rfl, ?_⟩
          convert K.mul_mem h2 h4 using 1
          rw [Prod.snd_mul]; group
        inv_mem' := by
          rintro _ ⟨γ, h1, rfl, h2⟩
          refine ⟨γ⁻¹, Γ.inv_mem h1, rfl, ?_⟩
          convert K.inv_mem h2 using 1
          rw [Prod.snd_inv]; group }
    have : Countable Δ := by
      refine Set.Countable.to_subtype (s := (Δ : Set G₁)) ((hc.image Prod.fst).mono ?_)
      rintro _ ⟨γ, h1, rfl, -⟩
      exact ⟨γ, h1, rfl⟩
    refine GlobalTheory.FundExists.exists_strict_domain Δ fun C hC => ?_
    refine ((hfin _ (hC.prod (hKc.image (f := fun k => x * k * x⁻¹) (by fun_prop)))).image Prod.fst).subset ?_
    rintro _ ⟨hC', γ, h1, rfl, h2⟩
    exact ⟨γ, ⟨h1, hC', _, h2, by group⟩, rfl⟩
  choose F hFm hFc hFi using hF
  let X : Quot (dcRel Γ K) → Set (G₁ × G₂) := fun d =>
    F (Quot.out d) ×ˢ ((fun z => (Quot.out d)⁻¹ * z) ⁻¹' (K : Set G₂))
  have hXm : ∀ d, MeasurableSet (X d) := fun d =>
    (hFm _).prod (measurable_const_mul _ hKo.measurableSet)
  have hkey : ∀ γ ∈ Γ, ∀ d d' y, y ∈ X d → γ * y ∈ X d' → d = d' ∧ γ = 1 := by
    intro γ hγ d d' y hy hy'
    have h1 : (Quot.out d)⁻¹ * y.2 ∈ K := hy.2
    have h2 : (Quot.out d')⁻¹ * (γ.2 * y.2) ∈ K := hy'.2
    have h3 := K.mul_mem h2 (K.inv_mem h1)
    have hd : d = d' := by
      rw [← Quot.out_eq d, ← Quot.out_eq d']
      exact Quot.sound ⟨γ, hγ, _, h3, by group⟩
    subst hd
    refine ⟨rfl, hinj γ hγ (hFi _ γ.1 ⟨γ, hγ, rfl, ?_⟩ y.1 hy.1 hy'.1)⟩
    convert h3 using 1
    group
  rw [GlobalTheory.covol_eq_measure_inter_fund (G₁ × G₂) Γ (μ₁.prod μ₂) (⋃ d, X d) Set.univ hc
    (fun γ _ => map_mul_left_eq_self _ γ) (MeasurableSet.iUnion hXm) ?_ ?_ MeasurableSet.univ (by simp),
    Set.univ_inter, measure_iUnion ?_ hXm, ← ENNReal.tsum_mul_left]
  · refine ENNReal.tsum_le_tsum fun d => ?_
    rw [Measure.prod_prod, measure_preimage_mul, mul_comm]
    gcongr
    exact iInf_le_of_le (F _) (iInf_le_of_le (hFm _) (iInf_le_of_le (fun y _ => hFc _ y) le_rfl))
  · intro d d' hd
    refine Set.disjoint_left.2 fun y hy hy' => hd (hkey 1 Γ.one_mem d d' y hy (by rwa [one_mul])).1
  · intro y
    obtain ⟨γ, hγ, k, hk, h⟩ := rel_out (dcRel_equiv Γ K) y.2
    obtain ⟨_, ⟨δ, hδ, rfl, hδK⟩, h'⟩ := hFc (Quot.out (Quot.mk (dcRel Γ K) y.2)) (γ.1 * y.1)
    refine ⟨δ * γ, Γ.mul_mem hδ hγ, Set.mem_iUnion.2 ⟨Quot.mk _ y.2, ?_, ?_⟩⟩
    · simpa [mul_assoc] using h'
    · show _ * (δ.2 * γ.2 * y.2) ∈ K
      rw [mul_assoc δ.2, h]
      convert K.mul_mem hδK hk using 1
      group
  · intro γ hγ hne
    have : (fun y => γ * y) '' (⋃ d, X d) ∩ (⋃ d, X d) = ∅ := by
      refine Set.eq_empty_of_forall_notMem ?_
      rintro _ ⟨⟨y, hy, rfl⟩, hγy⟩
      obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hy
      obtain ⟨d', hd'⟩ := Set.mem_iUnion.1 hγy
      exact hne (hkey γ hγ d d' y hd hd').2
    rw [this, measure_empty]

theorem eq_one_of_fst (I : AutInst) (x : I.GA) (hx : x ∈ I.GFset) (h : x.1 = 1) : x = 1 := by
  obtain ⟨γ, -, h1, h2⟩ := hx
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hP := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h3 := h1 v
  rw [h] at h3
  have h4 : (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) = 1 := by
    have h5 : (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v = 1 := h3.symm
    have h6 := congrArg (fun M => I.P v * M * (I.P v)⁻¹) h5
    simp only [← Matrix.mul_assoc] at h6
    rwa [Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hP, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ hP] at h6
  have h7 : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = 1 := by
    refine Matrix.map_injective (I.φ v).injective ?_
    show _ = (1 : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4
  rw [h7, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact Prod.ext h (Subtype.ext (Units.ext h2))

theorem sum_latGroup_le (I : AutInst) (Γ : Subgroup I.GA) (hΓ : (Γ : Set I.GA) = I.GFset)
    (K : Subgroup I.Gf) (hK : (K : Set I.Gf) = I.Kset) (c : InfinitePlace I.F → ℝ)
    (μ : Measure I.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] :
    ∑' d : Quot (dcRel Γ K), ENNReal.ofReal (∏ v, c v) *
      covol (latGroup I (Quot.out d)) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) Set.univ ≤ gaugeVol I c μ := by
  obtain ⟨hc, ho, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have := countable_dc Γ K (hK ▸ ho)
  have : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have h0 : μ I.Kset ≠ 0 := (ho.measure_pos μ ⟨1, hK ▸ K.one_mem⟩).ne'
  have ht : μ I.Kset ≠ ⊤ := hc.measure_lt_top.ne
  have key := sum_covol_le (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) μ Γ K
    (hΓ ▸ (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).2.1)
    (hΓ ▸ (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).2.2)
    (fun γ hγ => eq_one_of_fst I γ (hΓ ▸ hγ)) (hK ▸ hc) (hK ▸ ho)
  have e1 : ∀ x : I.Gf, {g | ∃ γ ∈ Γ, γ.1 = g ∧ x⁻¹ * γ.2 * x ∈ K} = latGroup I x := fun x => by
    unfold latGroup
    rw [← hΓ, ← hK]; rfl
  simp only [e1] at key
  rw [hΓ, hK] at key
  rw [ENNReal.tsum_mul_left, gaugeVol, mul_div_assoc]
  gcongr
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht), mul_comm]
  exact key

theorem unfoldBound : UnfoldBound := by
  intro I I₀ p q a j _ hj hq hp hsame hsig hsig₀ c μf _ _ c₀ μ₀ _ _ hc hc₀ B hB hBs
  obtain ⟨e, he⟩ := hsame
  obtain ⟨Γ, hΓ⟩ := (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).1
  obtain ⟨Γ₀, hΓ₀⟩ := (GlobalTheory.RatDiscrete.subgroup_countable_discrete I₀).1
  obtain ⟨K, hK⟩ := exists_kSub I
  obtain ⟨K₀, hK₀⟩ := exists_kSub I₀
  obtain ⟨hcK, hoK, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I₀
  have := countable_dc Γ₀ K₀ (hK₀ ▸ (GlobalTheory.adelicStab_isCompact_isOpen I₀).2.1)
  have := fun i => countable_lattices I.E (j i)
  have h0 : μf I.Kset ≠ 0 := (hoK.measure_pos μf ⟨1, hK ▸ K.one_mem⟩).ne'
  have ht : μf I.Kset ≠ ⊤ := hcK.measure_lt_top.ne
  let P : (∀ i, Quot (latRel I.E (j i))) × Quot (dcRel Γ₀ K₀) → Prop := fun t =>
    ∃ xf S T T' T₀, IsAdapted I I₀ e xf j S (fun i => (Quot.out (t.1 i)).1) (Quot.out t.2) T T' T₀
  have hP : ∀ t : {t // P t}, ∃ xf S T T' T₀,
    IsAdapted I I₀ e xf j S (fun i => (Quot.out (t.1.1 i)).1) (Quot.out t.1.2) T T' T₀ := fun t => t.2
  choose x S T T' T₀ had using hP
  have key := GlobalTheory.FlagMeas.covol_prod_le_tsum_slices I.Ginf I.Gf (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) μf Γ K (typeSet I j B)
    {t // P t} x (fun t => flagGroup I (x t) (S t)) (fun t => {g | sizesAt I (x t) (S t) g ∈ B})
    (hK ▸ hoK.measurableSet)
    (fun t g hg => by
      obtain ⟨γ, h1, h2, h3⟩ := hg.1
      exact ⟨γ, by rwa [← SetLike.mem_coe, hΓ], h2, by rwa [← SetLike.mem_coe, hK]⟩)
    (fun y hy => by
      obtain ⟨R, hR, hRB⟩ := GlobalTheory.FlagSat.exists_isSatFlag I a j B y hy
      obtain ⟨Λ, x₀, U, U', U₀, hU⟩ := GlobalTheory.T.exists_adaptedBasis_saturatedIsotropicFlag I I₀ e p q a j he hsig hp hq hsig₀ y.2 R hR
      let t : (∀ i, Quot (latRel I.E (j i))) × Quot (dcRel Γ₀ K₀) :=
        (fun i => Quot.mk _ ⟨Λ i, hU.2.2.1 i⟩, Quot.mk _ x₀)
      obtain ⟨V, V', V₀, hV⟩ := GlobalTheory.T.exists_adapted_basis_change_models I I₀ e y.2 a j R Λ x₀ U U' U₀ hj hU
        (fun i => (Quot.out (t.1 i)).1) (Quot.out t.2)
        (fun i => rel_out (latRel_equiv I.E (j i)) ⟨Λ i, hU.2.2.1 i⟩)
        (by
          obtain ⟨γ, h1, k, h2, h3⟩ := rel_out (dcRel_equiv Γ₀ K₀) x₀
          exact ⟨γ, hΓ₀ ▸ h1, k, hK₀ ▸ h2, h3⟩)
      let t' : {t // P t} := ⟨t, y.2, R, V, V', V₀, hV⟩
      obtain ⟨γ, h1, k, h2, h3, h4⟩ := GlobalTheory.T.flags_conjugate_of_same_adapted_models I I₀ e y.2 a j R _ _ V V' V₀ hj hV (x t') (S t') (T t') (T' t')
        (T₀ t') (had t')
      refine ⟨t', γ, by rwa [← SetLike.mem_coe, hΓ], k, by rwa [← SetLike.mem_coe, hK], h3, ?_⟩
      show sizesAt I (x t') (S t') (γ.1 * y.1) ∈ B
      rwa [h4])
    (hK ▸ ht)
  rw [hΓ, hK] at key
  have loc := fun t : {t // P t} => GlobalTheory.T.flagClass_measure_bound_lattice_stabiliser I I₀ e (x t) a j (S t) _ _ (T t) (T' t) (T₀ t) hj (had t)
    p q hsig c c₀ hc hc₀ B hB hBs
  set C := ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) with hC
  set Z := ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) with hZ
  let f : ∀ i, Quot (latRel I.E (j i)) → ENNReal := fun i d =>
    ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Quot.out d).1
  let g : Quot (dcRel Γ₀ K₀) → ENNReal := fun d => ENNReal.ofReal (∏ v, c₀ v) *
      covol (latGroup I₀ (Quot.out d)) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ
  have hg : ∑' d, g d ≤ gaugeVol I₀ c₀ μ₀ := sum_latGroup_le I₀ Γ₀ hΓ₀ K₀ hK₀ c₀ μ₀
  have hf : ∑' t : ∀ i, Quot (latRel I.E (j i)), ∏ i, f i (t i) ≤
      ∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * glVol I.E (j i) := by
    refine (tsum_pi_prod_le f).trans (le_of_eq (Finset.prod_congr rfl fun i _ => ?_))
    rw [ENNReal.tsum_mul_left]; rfl
  have hsum : ∑' t : {t // P t}, C * (∏ i, f i (t.1.1 i)) * g t.1.2 * Z ≤
      C * (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * glVol I.E (j i)) * gaugeVol I₀ c₀ μ₀ * Z := by
    refine (ENNReal.tsum_comp_le_tsum_of_injective (f := Subtype.val) Subtype.val_injective
      (fun t : (∀ i, Quot (latRel I.E (j i))) × Quot (dcRel Γ₀ K₀) =>
        C * (∏ i, f i (t.1 i)) * g t.2 * Z)).trans ?_
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    gcongr
  refine le_trans ?_ hsum
  refine le_trans ?_ (ENNReal.tsum_le_tsum loc)
  rw [ENNReal.tsum_mul_left, mul_div_assoc]
  gcongr
  rw [ENNReal.div_le_iff h0 ht, mul_comm]
  exact key

end GlobalTheory.FlagUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBoundStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlag_unfolding_bound : UnfoldBound := by
  first | exact @GlobalTheory.FlagUnfold.unfoldBound | exact GlobalTheory.FlagUnfold.unfoldBound | (intros; apply GlobalTheory.FlagUnfold.unfoldBound <;> assumption)
end
