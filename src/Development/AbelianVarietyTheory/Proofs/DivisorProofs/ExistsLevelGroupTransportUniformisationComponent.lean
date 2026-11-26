module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeTransportersAllComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ModelAtBare
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ModelAtPrimeToLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

end General

section Instance

variable {D : D7} {T : Top D}

theorem one_le_rank (h : LawsP T) {j : ℕ} (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have h3 := D.R.m_add_three_le_k
  simp only [Ranks.sigW]
  omega

end Instance

section Full

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

end Full

end GlobalTheory.Proof.ModelAtPrimeToLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeOfDatumImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeOfDatumImage
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.LevelLatticeCong

theorem cong_add {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ)
    {u₁ u₂ y₁ y₂ : Fin n → R} (f₁ : t • (K *ᵥ u₁ - u₁) = M • y₁) (f₂ : t • (K *ᵥ u₂ - u₂) = M • y₂) :
    t • (K *ᵥ (u₁ + u₂) - (u₁ + u₂)) = M • (y₁ + y₂) := by
  rw [smul_add, ← f₁, ← f₂, Matrix.mulVec_add, ← smul_add]
  congr 1
  abel

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t s : R) (M : ℕ)
    {u w : Fin n → R} (f : t • (K *ᵥ u - u) = M • w) :
    t • (K *ᵥ (s • u) - s • u) = M • (s • w) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, f, smul_comm]

end GlobalTheory.LevelLatticeCong

namespace GlobalTheory.LevelLatticeCong

theorem cong_on_sdLattice : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}, LatEmb V ι → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ a : La, ∃ w ∈ latGHat V 1, t • (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w) → ∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y := by
  intro D V β Λ hβ La _ _ ι hι K t M h
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [← GlobalTheory.OneMapRef.Lift.hatV_eq hβ]; rfl

  have hfv : ∀ (e : D.host.E) (v : Fin V.rank → D.host.E),
      finVec V (e • v) = ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] e) • finVec V v := by
    intro e v; funext i
    simp only [finVec, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

  have hint : ∀ c : 𝓞 D.host.E, ∀ z ∈ latHat V,
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z ∈ latHat V := by
    intro c z hz
    rw [hl] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_int Λ c hz

  have hinv : ∀ b ∈ ((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      ∀ w ∈ latGHat V 1, ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w ∈ latHat V := by
    intro b hb
    let s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
      (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b
    let H : AddSubgroup (Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) :=
      (latHat V).comap (DistribSMul.toAddMonoidHom _ s)
    suffices hle : latGHat V 1 ≤ H from fun w hw => hle hw
    rw [GlobalTheory.LevelActionPinned.latGHat_one, AddSubgroup.closure_le]
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, z, hz, rfl⟩
      have hba : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
        rw [← inv_mul_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
        exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hba
      have e : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) •
          (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) • z) =
          ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) • z := by
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        congr 2
        exact hc.symm
      show s • _ ∈ latHat V
      rw [e]; exact hint c z hz
  let P : D.host.E → Prop := fun e => ∀ x ∈ Λ, ∃ y ∈ latHat V,
    t • (K *ᵥ finVec V (e • x) - finVec V (e • x)) = M • y
  have hadd : ∀ e₁ e₂ : D.host.E, P e₁ → P e₂ → P (e₁ + e₂) := by
    intro e₁ e₂ h₁ h₂ x hx
    obtain ⟨y₁, hy₁, f₁⟩ := h₁ x hx
    obtain ⟨y₂, hy₂, f₂⟩ := h₂ x hx
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    have e0 : finVec V ((e₁ + e₂) • x) = finVec V (e₁ • x) + finVec V (e₂ • x) := by
      rw [add_smul]; funext i; exact TensorProduct.tmul_add _ _ _
    rw [e0]
    exact cong_add K t M f₁ f₂
  have hmul : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E),
      ∀ b ∈ (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E), P (a * b) := by
    intro a ha b hb x hx
    have hxL : finVec V x ∈ latHat V := by
      rw [hl]; exact GlobalTheory.Member.AALev.fv_mem_hat _ hx
    have hax : a • x ∈ latG V 1 := by
      refine Submodule.subset_span ⟨a, ha, x, ?_, rfl⟩
      refine ⟨finVec V x, hxL, ?_⟩
      simp only [map_one, Units.val_one, Matrix.one_mulVec]
    rw [← hι.2] at hax
    obtain ⟨a', ha'⟩ := hax
    obtain ⟨w, hw, e⟩ := h a'
    rw [ha'] at e
    refine ⟨((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] b) • w, hinv b hb w hw, ?_⟩
    have e1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    rw [e1, hfv b]
    exact cong_smul K t _ M e
  have h1 : (1 : D.host.E) ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) *
      (((D.host.AA)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (GlobalTheory.MarkCoset.AA_ne_zero D)]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have hP : P 1 := Submodule.mul_induction_on h1 hmul hadd
  intro x hx
  simpa only [one_smul] using hP x hx

end GlobalTheory.LevelLatticeCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeOfDatumImageStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_on_selfDual_lattice_of_datum_image : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}, LatEmb V ι → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ a : La, ∃ w ∈ latGHat V 1, t • (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w) → ∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y := by
  first | exact @GlobalTheory.LevelLatticeCong.cong_on_sdLattice | exact GlobalTheory.LevelLatticeCong.cong_on_sdLattice | (intros; apply GlobalTheory.LevelLatticeCong.cong_on_sdLattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeCompletion
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatHatCong

theorem cong_zero {R : Type} [CommRing R] {n : ℕ} (K : Matrix (Fin n) (Fin n) R) (t : R) (M : ℕ) :
    t • (K *ᵥ 0 - 0) = M • (0 : Fin n → R) := by
  rw [Matrix.mulVec_zero, sub_zero, smul_zero, smul_zero]

theorem cong_add {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u w y y' : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) (e' : t • (K *ᵥ w - w) = M • y') :
    t • (K *ᵥ (u + w) - (u + w)) = M • (y + y') := by
  rw [Matrix.mulVec_add, add_sub_add_comm, smul_add, e, e', smul_add]

theorem cong_neg {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (-u) - (-u)) = M • (-y) := by
  rw [Matrix.mulVec_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, smul_neg, e, smul_neg]

theorem cong_smul {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {t c : R} {M : ℕ} {u y : Fin n → R}
    (e : t • (K *ᵥ u - u) = M • y) : t • (K *ᵥ (c • u) - c • u) = M • (c • y) := by
  rw [Matrix.mulVec_smul, ← smul_sub, smul_comm t, e, smul_comm]

theorem cong_on_hat : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y) → ∀ z ∈ latHat V, ∃ y ∈ latHat V, t • (K *ᵥ z - z) = M • y := by
  intro D V β Λ hβ K t M h z hz
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  rw [hl] at h hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    obtain ⟨y, hy, e⟩ := h x hx
    have hm : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have hy' := GlobalTheory.PrincInLevel.smul_mem_hat Λ _ hm y hy
    have hc : (Algebra.TensorProduct.comm D.host.F _ D.host.E).symm ((1 : D.host.E) ⊗ₜ[D.host.F] a) =
        a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc] at hy'
    have hv : (fun i => a ⊗ₜ[D.host.F] x i) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • finVec V x := by
      funext i
      change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    refine ⟨_, hy', ?_⟩
    rw [hv]
    exact cong_smul e
  | zero =>
    exact ⟨0, AddSubgroup.zero_mem _, cong_zero K t M⟩
  | add u w _ _ hu hw =>
    obtain ⟨y, hy, e⟩ := hu
    obtain ⟨y', hy', e'⟩ := hw
    exact ⟨y + y', add_mem hy hy', cong_add e e'⟩
  | neg u _ hu =>
    obtain ⟨y, hy, e⟩ := hu
    exact ⟨-y, neg_mem hy, cong_neg e⟩

end GlobalTheory.LatHatCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeCompletionStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_on_selfDual_lattice_completion : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y) → ∀ z ∈ latHat V, ∃ y ∈ latHat V, t • (K *ᵥ z - z) = M • y := by
  first | exact @GlobalTheory.LatHatCong.cong_on_hat | exact GlobalTheory.LatHatCong.cong_on_hat | (intros; apply GlobalTheory.LatHatCong.cong_on_hat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroup
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise

namespace GlobalTheory.LevelFaithful

theorem bc_eq_one_of_cong {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (y : GL (Fin n) S) (s : S)
    (hx : ∀ z ∈ H, ∃ w ∈ H, (s : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹ : GL (Fin n) R).1 *ᵥ z - z) = N • w)
    {k : Type} [CommRing k] (φ : S →+* k) (hN : (N : k) = 0) (hs : IsUnit (φ s)) : Formalism.UG.bc φ y = 1 := by
  have key : ∀ i j, φ (y.1 i j) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    have e0 : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    obtain ⟨w, hw, e⟩ := hx (β.1 *ᵥ Pi.single j 1) ((hH _).2 fun i => by
      rw [e0, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _])
    have e1 := congrArg (fun v => ((β⁻¹).1 *ᵥ v) i) e
    have hy : (Formalism.UG.bc S.subtype y).1 i j = (y.1 i j : R) := rfl
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, e0, Units.val_mul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul] at e1
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.mulVec_single_one] at e1
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.col_apply, hy] at e1
    have hc := (hH w).1 hw i
    have e2 : s * (y.1 i j - (Pi.single j 1 : Fin n → S) i) = N • (⟨_, hc⟩ : S) := by
      apply Subtype.ext
      change (s : R) * ((y.1 i j : R) - ((Pi.single j (1 : S) : Fin n → S) i : R)) =
        N • (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w) i
      rw [← e1]
      congr 2
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have e3 := congrArg φ e2
    rw [map_mul, map_nsmul, nsmul_eq_mul, hN, zero_mul, hs.mul_right_eq_zero, map_sub, sub_eq_zero] at e3
    rw [e3, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact key i j

theorem cong_swap_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (t : FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      t • (K *ᵥ z - z) = N • y) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      Algebra.TensorProduct.comm F _ E t • (K.map (Algebra.TensorProduct.comm F _ E) *ᵥ z - z) = N • y := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ z hz)
  refine ⟨_, GlobalTheory.PrincInLevel.swap_mem_hatL Λ y hy, funext fun i => ?_⟩
  have := congrArg (Algebra.TensorProduct.comm F _ E) (congrFun e i)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_nsmul, Matrix.mulVec, dotProduct, map_sum,
    AlgEquiv.apply_symm_apply, Matrix.map_apply] using this

end GlobalTheory.LevelFaithful

namespace GlobalTheory.LevelFaithful

variable {D : D7}

theorem smul_mem_latGHat {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (c : 𝓞 D.host.E) {w : Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ latGHat V 1) :
    ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) • w ∈ latGHat V 1 := by
  have hl' : latHat V = GlobalTheory.AdLat.hat D.host.F ((Λ : Submodule (𝓞 D.host.E) _) : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  set s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E) with hs
  have e : ∀ z : Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E,
      Matrix.diagonal (fun _ => s) *ᵥ z = s • z := fun z => by
    funext j; rw [Matrix.mulVec_diagonal]; rfl
  have hN : ∀ z ∈ latHat V, Matrix.diagonal (fun _ => s) *ᵥ z ∈ latHat V := by
    intro z hz
    rw [e]
    rw [hl'] at hz ⊢
    have := GlobalTheory.PrincInLevel.smul_mem_hat Λ _ (Formalism.L2.DIV.oToS D.host.F D.host.E c).2 z hz
    convert this using 2
    rw [Formalism.L2.DIV.oToS_coe, Algebra.TensorProduct.comm_symm_tmul]
  rw [← e]
  exact GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN w hw


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cong_of_trivial {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} {Mb Mh : Ideal (𝓞 D.host.E)}
    (hprod : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) {c : 𝓞 D.host.E} (hc : c ∈ Mh) {f : La →ₗ[𝓞 D.host.E] La}
    (hd : ∀ a, f a - a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La))
    (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
    (hcong : ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w) (a : La) :
    ∃ w ∈ latGHat V 1,
      (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) •
        (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w := by
  set s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E) with hs
  obtain ⟨w, hw, e⟩ := hcong (c • a) (Submodule.smul_mem_smul hc Submodule.mem_top)
  have hdm : c • (f (c • a) - c • a) ∈ (M : 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) La) := by
    have := Submodule.smul_mem_smul hc (hd (c • a))
    rw [← Submodule.mul_smul, mul_comm, hprod, Submodule.ideal_span_singleton_smul] at this
    exact this
  obtain ⟨m, -, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hdm
  set F := GlobalTheory.LevelActionPinned.fvec V ι with hF
  have eF : ∀ (b : 𝓞 D.host.E) x, F (b • x) =
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • F x :=
    fun b x => GlobalTheory.LevelActionPinned.fvec_smul V ι b x
  have E1 : F (c • a) = s • F a := eF c a
  have eM : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (((M : ℕ) : 𝓞 D.host.E) : D.host.E)) =
      ((M : ℕ) : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := by
    have h0 : (((M : ℕ) : 𝓞 D.host.E) : D.host.E) = ((M : ℕ) : D.host.E) := by simp
    rw [h0]
    exact map_natCast (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] _) _
  have E2 : s • (F (f (c • a)) - F (c • a)) = M • F m := by
    rw [← map_sub, ← eF, ← hm', eF, eM, Nat.cast_smul_eq_nsmul]
  have e' : F (f (c • a)) - K *ᵥ F (c • a) = M • w := e
  refine ⟨F m - s • w, sub_mem (((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1
    (hι.2 ▸ LinearMap.mem_range_self ι m)) (smul_mem_latGHat hβ c hw), ?_⟩
  show (s * s) • (K *ᵥ F a - F a) = _
  calc (s * s) • (K *ᵥ F a - F a) = s • (K *ᵥ (s • F a) - s • F a) := by
        rw [mul_smul, Matrix.mulVec_smul K s (F a), smul_sub]
    _ = s • ((F (f (c • a)) - F (c • a)) - M • w) := by
        rw [← E1, ← e']; congr 1; abel
    _ = M • (F m - s • w) := by
        rw [smul_sub, E2, smul_comm s M w, smul_sub]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rTup_eq_one_of_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {M : ℕ} {c : 𝓞 D.host.E}
    (hM : ∀ PP ∈ L.Pg, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hc : ∀ PP ∈ L.Pg, c - 1 ∈ PP.asIdeal) {κ : GA D V}
    (hκ : Lev.finE V κ ∈ Formalism.L2.DIV.St β)
    (h : ∀ z ∈ latHat V, ∃ y ∈ latHat V,
      (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) •
        ((finHom V κ).1 *ᵥ z - z) = M • y) :
    Formalism.L2.DIV.rTup β L (Lev.finE V κ) = 1 := by
  have hl' : latHat V = GlobalTheory.AdLat.hat D.host.F ((Λ : Submodule (𝓞 D.host.E) _) : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  rw [hl'] at h
  have hS := cong_swap_smul Λ M _ _ h
  obtain ⟨yi, hyi⟩ := hκ
  obtain ⟨cc, hfr, -⟩ := hβ
  have hx : ∀ z ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)), ∃ w ∈
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)),
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (c * c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) •
        ((β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 *ᵥ z - z) =
        M • w := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hS z hz
    refine ⟨y, hy, ?_⟩
    have hs' : ((Formalism.L2.DIV.oToS D.host.F D.host.E (c * c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
        Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E
          (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
            ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) := by
      rw [Formalism.L2.DIV.oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.comm_tmul, map_mul]
    have e2 : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ = Formalism.L2.DIV.frGL β yi := rfl
    have hK' : (β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
        (finHom V κ).1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [e2, hyi]
      rfl
    rw [hs', hK']
    exact e
  have hred : ∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn β PP (Lev.finE V κ) = 1 := by
    intro PP hP
    have hN : ((M : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (hM PP hP)
    have hsu : IsUnit (Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E (c * c))) := by
      rw [Formalism.L2.DIV.resS_oToS]
      have e1 : Ideal.Quotient.mk PP.asIdeal c = 1 := by
        rw [← map_one (Ideal.Quotient.mk PP.asIdeal)]
        exact Ideal.Quotient.eq.2 (hc PP hP)
      rw [map_mul, e1, mul_one]
      exact isUnit_one
    have hr := bc_eq_one_of_cong (Formalism.L2.Herm.intAf D.host.F D.host.E) β
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)) M hfr yi
      (Formalism.L2.DIV.oToS D.host.F D.host.E (c * c)) hx (Formalism.L2.DIV.resS D.host.F PP) hN hsu
    rw [← hyi, Formalism.L2.DIV.redFn_frGL, hr]
  have e3 : Formalism.L2.DIV.rTup β L (Lev.finE V κ) = Formalism.L2.DIV.rTup β L 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ _ = Formalism.L2.DIV.upperLeftBlock _ _
    rw [hred PP.1 PP.2, Formalism.L2.DIV.redFn_one]
  rw [e3, Formalism.L2.DIV.rTup_one]

end GlobalTheory.LevelFaithful


open GlobalTheory.LevelFaithful in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.LevelFaithful.lev_mul_and_faithful : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m), (∀ g g' : p.P.Gp, r.lev i (g * g') = r.lev i g * r.lev i g') ∧ ∀ g : p.P.Gp, r.lev i g = 1 → g = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i
  obtain ⟨v⟩ := GlobalTheory.ShareOn.nonempty_place D
  have hlev := h.level v i
  have hι := GlobalTheory.TraceLattice.latEmb_iotaW (h.laws v) i
  have hβ : IsSDFrame (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) 1 := p.charW.base.lev.βW i
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs (R2 p) i hι hβ h.half hlev
  refine ⟨fun g g' => ?_, fun g hg => ?_⟩
  · refine LinearEquiv.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e1 := liftLa_spec (r.lev i (g * g')) a
    have e2 := liftLa_spec (r.lev i g) (liftLa (r.lev i g') a)
    have e3 := liftLa_spec (r.lev i g') a
    simp only [Submodule.mkQ_apply] at e1 e2 e3
    rw [LinearEquiv.mul_apply, ← e3, ← e2, ← e1]
    exact (Submodule.Quotient.eq _).2 (hm g g' a)
  · apply (R2 p).eG.injective
    rw [map_one]
    obtain ⟨κ, hκ, hcong⟩ := hlev g
    rw [← hκ.2.2]
    have hd : ∀ a, liftLa (r.lev i g) a - a ∈
        p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
      intro a
      rw [hg, ← Submodule.Quotient.eq]
      exact liftLa_spec 1 a
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1
      (p.T.Q.l.coprime ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ p.T.Q.l.Mb ⊔ Mfr p.T.Q.l)
    have hc1 : c - 1 ∈ p.T.Q.l.Mb := by
      have e : c - 1 = -b := by rw [← hbc]; ring
      rw [e]; exact neg_mem hb
    have hMbP : ∀ PP ∈ (R2 p).Pg, p.T.Q.l.Mb ≤ PP.asIdeal := fun PP hP => by
      rw [h.half]; exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
    have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
    have hMm : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
      have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb * Mfr p.T.Q.l := by
        rw [hp]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf.trans (inf_le_left : p.T.Q.l.Mb ⊓ Mfr p.T.Q.l ≤ p.T.Q.l.Mb)) h0
    have hA := cong_of_trivial hβ hι hp hc hd _ hcong
    have hB := GlobalTheory.T.congruence_on_selfDual_lattice_completion (Wc D i) hβ _ _ _ (GlobalTheory.T.congruence_on_selfDual_lattice_of_datum_image (Wc D i) hβ hι _ _ _ hA)
    exact rTup_eq_one_of_cong hβ ((R2 p).datWp i (R2 p).triv) (fun PP hP => hMbP PP hP hMm)
      (fun PP hP => hMbP PP hP hc1) (Formalism.L2.DIV.parLev_St hκ.2.1) hB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMulAndFaithfulFiniteGroupStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_mul_and_faithful_finiteGroup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m), (∀ g g' : p.P.Gp, r.lev i (g * g') = r.lev i g * r.lev i g') ∧ ∀ g : p.P.Gp, r.lev i g = 1 → g = 1 := by
  first | exact @GlobalTheory.LevelFaithful.lev_mul_and_faithful | exact GlobalTheory.LevelFaithful.lev_mul_and_faithful | (intros; apply GlobalTheory.LevelFaithful.lev_mul_and_faithful <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMul
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_const_of_forall_unit_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {O : Set V} (hO : IsOpen O) (hc : IsPreconnected O) (hne : O.Nonempty) {ι : Type} (P Q : ι → V → ℂ)
    (hP : ∀ j, DifferentiableOn ℂ (P j) O) (hQ : ∀ j, DifferentiableOn ℂ (Q j) O)
    (h : ∀ x ∈ O, ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ j, P j x = u * Q j x) :
    ∃ c : ℂˣ, ∀ j, ∀ x ∈ O, P j x = c * Q j x := by
  by_cases h0 : ∃ j, ∃ x₁ ∈ O, Q j x₁ ≠ 0
  · obtain ⟨j₀, x₁, hx₁, hq⟩ := h0
    obtain ⟨u₁, hu₁, hPu⟩ := h x₁ hx₁
    have hu0 : u₁ ≠ 0 := by
      intro e
      rw [e, norm_zero] at hu₁
      exact zero_ne_one hu₁

    have step : ∀ j, ∀ x ∈ O, P j x + (1 - Q j x₁) / Q j₀ x₁ * P j₀ x =
        u₁ * (Q j x + (1 - Q j x₁) / Q j₀ x₁ * Q j₀ x) := by
      intro j
      set μ : ℂ := (1 - Q j x₁) / Q j₀ x₁ with hμ
      obtain ⟨-, c', hc'⟩ := GlobalTheory.exists_eq_const_mul_of_forall_exists_norm_eq V Unit O hO hc hne
        (fun x => P j x + μ * P j₀ x) (fun _ x => Q j x + μ * Q j₀ x)
        ((hP j).add ((hP j₀).const_smul μ))
        (fun _ => (hQ j).add ((hQ j₀).const_smul μ))
        (fun x hx => by
          obtain ⟨u, hu, hPx⟩ := h x hx
          refine ⟨(), ?_⟩
          simp only [hPx, ← mul_add, mul_left_comm μ u, norm_mul, hu, one_mul])
      have hQ1 : Q j x₁ + μ * Q j₀ x₁ = 1 := by
        rw [hμ, div_mul_cancel₀ _ hq]
        ring
      have hc1 : c' = u₁ := by
        have e := hc' x₁ hx₁
        rw [hQ1, mul_one, hPu j, hPu j₀, mul_left_comm μ u₁, ← mul_add, hQ1, mul_one] at e
        exact e.symm
      intro x hx
      rw [hc' x hx, hc1]
    have h₀ : ∀ x ∈ O, P j₀ x = u₁ * Q j₀ x := by
      intro x hx
      have e := step j₀ x hx
      have hne' : 1 + (1 - Q j₀ x₁) / Q j₀ x₁ ≠ 0 := by
        rw [add_div' _ _ _ hq]
        simp [hq]
      have : (1 + (1 - Q j₀ x₁) / Q j₀ x₁) * (P j₀ x - u₁ * Q j₀ x) = 0 := by
        linear_combination e
      rcases mul_eq_zero.1 this with h1 | h1
      · exact (hne' h1).elim
      · exact sub_eq_zero.1 h1
    refine ⟨Units.mk0 u₁ hu0, fun j x hx => ?_⟩
    have e := step j x hx
    rw [Units.val_mk0]
    linear_combination e - (1 - Q j x₁) / Q j₀ x₁ * h₀ x hx
  · push_neg at h0
    refine ⟨1, fun j x hx => ?_⟩
    obtain ⟨u, -, hPx⟩ := h x hx
    rw [hPx j, h0 j x hx, mul_zero, mul_zero]

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem transp_reads_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  intro D L hT Gi Gl Kc Y cX eX Csz p hp r h hr i v ψ γ k k' a ht
  obtain ⟨hm, hb, -⟩ := ht
  have hl := h.laws v
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  have hU : IsUnf (uAt r v i) := hl.p.unf _ hj _ hσ
  have hpins := hl.p.pins
  have hpq : 1 ≤ ((r.used v).full.Q.Dw ((i : ℕ) + 1)).p + ((r.used v).full.Q.Dw ((i : ℕ) + 1)).q := by
    rw [(hpins.2.2.2 _ hj).1, (hpins.2.2.2 _ hj).2.1]
    have := hj.1; have := hj.2; have := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega
  have hL := GlobalTheory.T.actLev_full_level_group_framedPoints D (r.used v).full.Q ((i : ℕ) + 1) hpq hpins.2.1.2
  have hsecF : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      F.1 ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    ((mem_cusp _ _ _ _ _ _).1 (Submodule.mem_inf.1 F.2).1).1
  have hsecG : ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
      actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1 ∈
        sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n := fun F =>
    actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ (hsecF F)
  have P1 : ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom)
      (hy : castFrame hm.psi (lact a x) ∈ ((uAt r v i).X k').dom) (t : _)
      (hbt : FrBor t ((uAt r v i).un k' ⟨castFrame hm.psi (lact a x), hy⟩)
        (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c γ ((uAt r v i).un k ⟨x, hx⟩)))
      (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t : CAt (r.used v).full.σ₀) *
          rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx hy t hbt F
    have e1 : rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
        toC (evR _ _ (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1)
          ((uAt r v i).un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) =
        toC (evR _ _ F.1 ((uAt r v i).un k' ⟨_, hy⟩)) := dif_pos hy
    have e3 := evalAt_actL hL (hl.p.evalWD _ hj) frMap_trans_id γ (hsecF F).1 ((uAt r v i).un k ⟨x, hx⟩)
    have e4 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ _ _).2.2.2.2.2.2 (CAt _)
      (inferInstanceAs (IsReduced ℂ)) _ _ F.1 (hsecF F) t _ _ hbt
    rw [e1, e2]
    exact congrArg toC (e3.trans e4)
  have hUf : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) := hU
  have hσf : Formalism.L2.PjFree.GoodEmb (r.used v).full.Q.c (r.used v).full.σ₀ := hσ
  have hr1 : 1 ≤ D.R.r := hU.1 ▸ hpq
  have hxi : ∀ k k' (τ : D.host.E →+* ℂ), ‖τ ((uAt r v i).X k).ξ0‖ = ‖τ ((uAt r v i).X k').ξ0‖ :=
    fun k k' τ => (hl.p.xiAbs _ hj _ hσ k τ).trans (hl.p.xiAbs _ hj _ hσ k' τ).symm
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf
  have hsk : ∀ (f : Rul ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c),
      f ∈ sec ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (wtA (p.κ i)) (p.κ i).n → ∀ k,
      ((uAt r v i).X k).IsSec (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) (rdU (uAt r v i) f k) :=
    fun f hf k => hU.2.2.2.2.1 _ _ (dom_wtA _) f hf k
  have key : ∀ x ∈ ((uAt r v i).X k).dom, ∃ u : ℂ, ‖u‖ = 1 ∧
      ∀ F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i),
        rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x =
          u * rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)) := by
    intro x hx
    obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀'⟩, -⟩ := hun1 k ⟨x, hx⟩
    have e₀ : x₀.1 = rmul x b₀ := e₀'
    obtain ⟨hy₀, t₀, hbt₀⟩ := hb x₀.1 x₀.2
    obtain ⟨ρ, ν, -, -, hmv⟩ := mvPt_spec hL.total γ ((uAt r v i).un k x₀)
    have hx₀' : GlobalTheory.FrameNorm.IsUnitFr ((uAt r v i).X k') (castFrame hm.psi (lact a x₀.1)) := fun τ j => by
      exact (congrArg norm (hm.dmin_eq x₀.1 τ j)).trans (hx₀ _ _)
    obtain ⟨-, -, -, -, -, -, ht1⟩ := GlobalTheory.LevelCusp.exists_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hσf hUf hr1
      hxi (x := x₀) (x' := ⟨castFrame hm.psi (lact a x₀.1), hy₀⟩) hmv hbt₀ hx₀ hx₀'
    refine ⟨toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀), ?_, fun F => ?_⟩
    · have : toC (wchar (ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n) t₀ : CAt (r.used v).full.σ₀) =
          ∏ j, toC (t₀ j : CAt (r.used v).full.σ₀) ^ ex ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (wtA (p.κ i)) (p.κ i).n j := rfl
      rw [this, norm_prod]
      exact Finset.prod_eq_one fun j _ => by
        rw [norm_pow, show ‖toC (t₀ j : CAt (r.used v).full.σ₀)‖ = 1 from ht1 j, one_pow]
    · have A := P1 x₀.1 x₀.2 hy₀ t₀ hbt₀ F
      have B := (hsk _ (hsecG F) k).2.1 x hx b₀ hb₀
      have C := (hsk _ (hsecF F) k').2.1 _ (hb x hx).1 _ (GlobalTheory.Dict.Pull.cast_bor hm.psi hb₀)
      have e5 : castFrame hm.psi (lact a x₀.1) = rmul (castFrame hm.psi (lact a x)) (GlobalTheory.Dict.castFr hm.psi b₀) := by
        rw [e₀]
        exact (congrArg (castFrame hm.psi) (GlobalTheory.Dict.Extend.lact_rmul a x b₀)).trans (GlobalTheory.Dict.Pull.cast_rmul hm.psi _ _)
      have e6 : bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k') (GlobalTheory.Dict.castFr hm.psi b₀) =
          bchar (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) b₀ :=
        GlobalTheory.Dict.Pull.cast_bchar hm.psi (GlobalTheory.LevelCusp.laU_match (U := Formalism.L2.PjFree.Unf.ofPj (uAt r v i)) hm _ _) b₀
      rw [e5, C, e6, e₀, B] at A
      have hβ := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne ((uAt r v i).X k) (laU (uAt r v i) (wtA (p.κ i)) (p.κ i).n k) hb₀
      apply mul_left_cancel₀ hβ
      rw [A]
      ring
  obtain ⟨c, hc⟩ := exists_const_of_forall_unit_mul (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).isPreconnected
    (GlobalTheory.frames_isConnected D.host.E D.R.r ((uAt r v i).X k)).nonempty
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) (actLev (Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (levFull ((r.used v).full.Q.Dw ((i : ℕ) + 1)) (r.used v).full.Q.l) γ F.1) k x)
    (fun (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) x =>
      rdU (uAt r v i) F.1 k' (castFrame hm.psi (lact a x)))
    (fun F => (hsk _ (hsecG F) k).1)
    (fun F => (hsk _ (hsecF F) k').1.comp
      ((GlobalTheory.Dict.Pull.cast_diff hm.psi).comp (GlobalTheory.Dict.Extend.differentiable_lact a)).differentiableOn
      (fun x hx => (hb x hx).1))
    key
  refine ⟨c, fun F x hx h2 => ?_⟩
  exact hc F x hx

end GlobalTheory.ShareOn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMulStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  first | exact @GlobalTheory.ShareOn.transp_reads_const_mul | exact GlobalTheory.ShareOn.transp_reads_const_mul | (intros; apply GlobalTheory.ShareOn.transp_reads_const_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportComp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportComp
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isTransp_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v ψ γ γ' k k₁ k₂ a a' h₁ h₂
  obtain ⟨m₁, f₁, l₁⟩ := h₁
  obtain ⟨m₂, f₂, l₂⟩ := h₂
  have hP := (h.laws v).p
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left 1 _, i.isLt⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1)
    (GlobalTheory.Proof.ModelAtPrimeToLevel.one_le_rank hP hj) hP.pins.2.1.2
  have hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k₂) (a * a') :=
    { psi := m₁.psi.trans m₂.psi
      p0 := m₁.p0.trans m₂.p0
      xi := m₁.xi.trans m₂.xi
      iso := fun u w => by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, m₂.iso, m₁.iso]
      lat := fun w => by
        rw [m₁.lat, m₂.lat, Units.val_mul, Matrix.mulVec_mulVec] }
  refine ⟨hm, fun x hx => ?_, fun w => ?_⟩
  · obtain ⟨hy₁, t₁, b₁⟩ := f₁ x hx
    obtain ⟨hy₂, t₂, b₂⟩ := f₂ _ hy₁
    have ef : castFrame hm.psi (lact (a * a') x) =
        castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) := by
      funext τ
      simp only [castFrame, lact, mat, Units.val_mul, Matrix.map_mul, Matrix.of_apply]
      rw [mul_assoc]
      rfl
    set Xo := (r.used v).full.Q.Xo ((i : ℕ) + 1)
    set c := (r.used v).full.Q.c
    set y₀ := (uAt r v i).un k ⟨x, hx⟩
    set y₁ := (uAt r v i).un k₁ ⟨castFrame m₁.psi (lact a' x), hy₁⟩
    have e1 := hL.mul γ' γ _ y₀ _ _ (mvPt_spec hL.total γ' y₀) (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e2 := hL.func (γ' * γ) _ y₀ _ _ (mvPt_spec hL.total (γ' * γ) y₀) e1
    have e3 : mvLev Xo c γ (mvLev Xo c γ' y₀) = mvLev Xo c (γ' * γ) y₀ :=
      ((GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).1 _ _ e2
        (GlobalTheory.Frames.frMap_unique_refl_iff _ _ _ _ _ _ _ _ (AlgHom.id _ _) _).2.1)
    have e4 := hL.bor γ _ t₁ y₁ _ (mvLev Xo c γ' y₀) _ b₁ (mvPt_spec hL.total γ y₁)
      (mvPt_spec hL.total γ (mvLev Xo c γ' y₀))
    have e5 := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ _ _ _ _ _ _).2.1 t₂ t₁ _ _ _ b₂ e4
    have key : ∀ (z : Frame ((uAt r v i).X k₂).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k₂).dom),
        z = castFrame m₂.psi (lact a (castFrame m₁.psi (lact a' x))) →
        FrBor (t₂ * t₁) ((uAt r v i).un k₂ ⟨z, hz⟩) (mvLev Xo c (γ' * γ) y₀) := by
      rintro z hz rfl
      rw [← e3]
      exact e5
    exact ⟨ef ▸ hy₂, t₂ * t₁, key _ _ ef⟩
  · obtain ⟨hw₁, q₁⟩ := l₁ w
    obtain ⟨hw₂, q₂⟩ := l₂ ⟨_, hw₁⟩
    have e : ((a * a' : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E) =
        (a : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec
          ((a' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec (w : Fin D.R.r → D.host.E)) := by
      rw [Units.val_mul, Matrix.mulVec_mulVec]
    have hs : ∀ z, (γ' * γ).symm z = γ.symm (γ'.symm z) := fun z =>
      (γ' * γ).injective (by
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply])
    rw [e]
    refine ⟨hw₂, q₂.trans ?_⟩
    refine congrArg (ψ k₂) ?_
    refine (congrArg γ.symm ((congrArg (ψ k₁).symm q₁).trans ((ψ k₁).symm_apply_apply _))).trans ?_
    exact (hs _).symm

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportCompStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelComponentTransport_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  first | exact @GlobalTheory.ShareOn.isTransp_comp | exact GlobalTheory.ShareOn.isTransp_comp | (intros; apply GlobalTheory.ShareOn.isTransp_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGroupTransportUniformisationComponent
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem exists_transport : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ (act : p.P.Gp → (uAt r v i).Comp → (uAt r v i).Comp) (tr : p.P.Gp → (uAt r v i).Comp → GL (Fin D.R.r) D.host.E),
    (∀ k, act 1 k = k) ∧ (∀ g g' k, act (g * g') k = act g (act g' k)) ∧
    (∀ g k, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (act g k)) (tr g k)) ∧
    (∀ g k γ, γ ∈ ((uAt r v i).X k).Γ ↔ tr g k * γ * (tr g k)⁻¹ ∈ ((uAt r v i).X (act g k)).Γ) ∧
    (∀ g g' k, tr (g * g') k * (tr g (act g' k) * tr g' k)⁻¹ ∈ ((uAt r v i).X (act (g * g') k)).Γ) ∧
    (∀ g k, act g k = k → tr g k ∈ ((uAt r v i).X k).Γ → g = 1) ∧
    (∃ a : p.P.Gp → (uAt r v i).Comp → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp)
      (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom →
      ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X (act g k)).Ψ),
        rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
            (r.lev i g⁻¹) F.1) k x =
          (a g k : ℂ) * rdU (uAt r v i) F.1 (act g k) (castFrame h2 (lact (tr g k) x))) ∧
    ∀ Lf : (uAt r v i).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E), (∀ k, Lf k = lattice₂ D ((uAt r v i).X k).Λ) →
      ∃ φ : ∀ k, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
          (Lf k ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k)))),
        ∀ (k : (uAt r v i).Comp) (g : p.P.Gp), act g k = k → ∃ n : ℤ, ∀ w : Lf k,
          ∃ hw : Matrix.mulVec (tr g k : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ Lf k,
            Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k))) ⟨_, hw⟩ =
              φ k ((r.lev i g ^ n) ((φ k).symm (Submodule.Quotient.mk w))) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp r h hr i v
  obtain ⟨ψ, hex⟩ := GlobalTheory.T.exists_levelChange_transporters_all_components p hp r h hr i v
  have uniq := GlobalTheory.T.unique_up_to_target_group p hp r h hr i v ψ
  have one := GlobalTheory.T.identity_transports_component_to_itself p hp r h hr i v ψ
  have comp := GlobalTheory.T.isLevelComponentTransport_comp p hp r h hr i v ψ
  have gam := GlobalTheory.T.isTransport_identity_of_mem_componentGroup p hp r h hr i v ψ
  obtain ⟨lmul, linj⟩ := GlobalTheory.T.levelAction_mul_and_faithful_finiteGroup p hp r h hr i
  have c8 := GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul p hp r h hr i v ψ
  choose act tr htr using fun (g : p.P.Gp) k => hex (r.lev i g⁻¹) k
  have lev1 : r.lev i 1 = 1 := by
    have e := lmul 1 1
    rw [mul_one] at e
    exact (mul_eq_left.1 e.symm)
  have levinv : ∀ g, r.lev i g⁻¹ = (r.lev i g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_left (by rw [← lmul, inv_mul_cancel, lev1])
  have levmul : ∀ g g', r.lev i (g * g')⁻¹ = r.lev i g'⁻¹ * r.lev i g⁻¹ := fun g g' => by
    rw [mul_inv_rev, lmul]
  have hco : ∀ g g' k, IsTransp p r i v ψ (r.lev i (g * g')⁻¹) k (act g (act g' k)) (tr g (act g' k) * tr g' k) :=
    fun g g' k => by
      rw [levmul]
      exact comp _ _ _ _ _ _ _ (htr g' k) (htr g (act g' k))
  refine ⟨act, tr, fun k => ?_, fun g g' k => ?_, fun g k => (htr g k).1, fun g k γ => ?_, fun g g' k => ?_,
    fun g k hk hΓ => ?_, ⟨fun g k => (c8 _ _ _ _ (htr g k)).choose, fun F g k x hx h2 =>
      (c8 _ _ _ _ (htr g k)).choose_spec F x hx h2⟩, fun Lf hLf => ?_⟩
  · have e := htr 1 k
    rw [inv_one, lev1] at e
    exact (uniq _ _ _ _ _ _ e (one k)).1
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).1
  · constructor
    · intro hγ
      have e1 := comp _ _ _ _ _ _ _ (gam k γ hγ) (htr g k)
      rw [one_mul] at e1
      have := (uniq _ _ _ _ _ _ e1 (htr g k)).2
      simpa [mul_assoc] using this
    · intro hγ
      obtain ⟨k'', b, hb⟩ := hex (r.lev i g⁻¹)⁻¹ (act g k)
      have e1 := comp _ _ _ _ _ _ _ (htr g k) hb
      rw [mul_inv_cancel] at e1
      obtain ⟨hk'', hb1⟩ := uniq _ _ _ _ _ _ e1 (one k)
      rw [hk''] at hb hb1
      have e2 := comp _ _ _ _ _ _ _ (gam _ _ hγ) hb
      have e3 := comp _ _ _ _ _ _ _ (htr g k) e2
      rw [one_mul, mul_inv_cancel] at e3
      have hb2 := (uniq _ _ _ _ _ _ e3 (one k)).2
      rw [inv_one, mul_one] at hb1 hb2
      have key : γ = (b * tr g k)⁻¹ * (b * (tr g k * γ * (tr g k)⁻¹) * tr g k) := by group
      rw [key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb1) hb2
  · exact (uniq _ _ _ _ _ _ (htr (g * g') k) (hco g g' k)).2
  · have e1 := gam k (tr g k) hΓ
    have e2 := htr g k
    rw [hk] at e2
    have e3 := IsTransp.eq_of_eq e2 e1
    have : g⁻¹ = 1 := linj _ e3
    simpa using this
  · have keyg : ∀ g, (r.lev i g⁻¹).symm = r.lev i g ^ (1 : ℤ) := fun g => by
      rw [zpow_one, levinv]
      rfl
    obtain rfl : Lf = fun k => lattice₂ D ((uAt r v i).X k).Λ := funext hLf
    refine ⟨ψ, fun k g hk => ⟨1, fun w => ?_⟩⟩
    beta_reduce at w ⊢
    have e2 := htr g k
    rw [hk] at e2
    obtain ⟨-, -, hm⟩ := e2
    obtain ⟨hw, e⟩ := hm w
    refine ⟨hw, e.trans (congrArg (ψ k) (congrFun (congrArg DFunLike.coe (keyg g)) _))⟩

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGroupTransportUniformisationComponentStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelGroup_transport_uniformisation_components : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ (act : p.P.Gp → (uAt r v i).Comp → (uAt r v i).Comp) (tr : p.P.Gp → (uAt r v i).Comp → GL (Fin D.R.r) D.host.E),
    (∀ k, act 1 k = k) ∧ (∀ g g' k, act (g * g') k = act g (act g' k)) ∧
    (∀ g k, GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X (act g k)) (tr g k)) ∧
    (∀ g k γ, γ ∈ ((uAt r v i).X k).Γ ↔ tr g k * γ * (tr g k)⁻¹ ∈ ((uAt r v i).X (act g k)).Γ) ∧
    (∀ g g' k, tr (g * g') k * (tr g (act g' k) * tr g' k)⁻¹ ∈ ((uAt r v i).X (act (g * g') k)).Γ) ∧
    (∀ g k, act g k = k → tr g k ∈ ((uAt r v i).X k).Γ → g = 1) ∧
    (∃ a : p.P.Gp → (uAt r v i).Comp → ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (g : p.P.Gp)
      (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom →
      ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X (act g k)).Ψ),
        rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)
            (r.lev i g⁻¹) F.1) k x =
          (a g k : ℂ) * rdU (uAt r v i) F.1 (act g k) (castFrame h2 (lact (tr g k) x))) ∧
    ∀ Lf : (uAt r v i).Comp → Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E), (∀ k, Lf k = lattice₂ D ((uAt r v i).X k).Λ) →
      ∃ φ : ∀ k, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E]
          (Lf k ⧸ (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k)))),
        ∀ (k : (uAt r v i).Comp) (g : p.P.Gp), act g k = k → ∃ n : ℤ, ∀ w : Lf k,
          ∃ hw : Matrix.mulVec (tr g k : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w ∈ Lf k,
            Submodule.Quotient.mk (p := p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (Lf k))) ⟨_, hw⟩ =
              φ k ((r.lev i g ^ n) ((φ k).symm (Submodule.Quotient.mk w))) := by
  first | exact @GlobalTheory.ShareOn.exists_transport | exact GlobalTheory.ShareOn.exists_transport | (intros; apply GlobalTheory.ShareOn.exists_transport <;> assumption)
end
