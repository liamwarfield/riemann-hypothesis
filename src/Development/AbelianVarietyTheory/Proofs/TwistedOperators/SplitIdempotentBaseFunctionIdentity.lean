module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SizesOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocLineOfMatches

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelOntoLocal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SymmetricBilinearHalf

variable {D : D7}

theorem sb_zero {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem sb_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have ne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (ne t ht), k, hk, fun u hu hh t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hh t],
    fun t ht => h3 t (ne t ht)⟩

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (k : ℕ) (h : IsHalf e u) : IsHalf e (k • u) := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at h ⊢
  rw [smul_comm, h]

theorem sb_add {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) (h' : IsSBHalf e Λ Ψ) : IsSBHalf e Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have ne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  refine ⟨fun t ht => (ne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (half_nsmul k' hh) t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (half_nsmul k hh) t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases ne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem wAt_of_half {m n : ℕ} {p : Place D} {a c : AE D} (hac : a * c = 0) (hs : a + c = idem D p)
    {x : Mx D m n} (hx : IsHalf a x) : wAt p x = x := by
  funext i j
  show idem D p * x i j = x i j
  have := hx i j
  rw [← hs]
  linear_combination (1 - c) * this + (x i j) * hac

theorem placeModel_onto_local : ∀ (D : Formalism.BasicNotions.D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥(Formalism.BasicNotions.D7.host D).F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (S T : Formalism.BasicNotions.TH.HSp D) (sS : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank S)) (Fin (Formalism.BasicNotions.HSpace.rank S)) ℂ) (sT : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank T)) (Fin (Formalism.BasicNotions.HSpace.rank T)) ℂ) (ΛS : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank S) → (Formalism.BasicNotions.D7.host D).E)) (ΛT : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank T) → (Formalism.BasicNotions.D7.host D).E)) (f₀ : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.FinPl D) (a : Formalism.L2.Theta.AE D), Formalism.L2.Theta.IsSplitIdem D a → a + (Formalism.L2.Theta.cA D) a = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (Sum.inl v) → (∃ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm) ∧ ∀ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm → (∀ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ → GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) (Tm Φ)) ∧ ∀ (x : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) x → ∃ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ ∧ Tm Φ = x := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb v a ha hs
  have h1 : a * a = a := ha.1
  have h2 : a * cA D a = 0 := ha.2.1
  have c1 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  have hψ := base_std hb
  have hθ := base_inf hb
  have hS := hb.2.2.1
  have hT := hb.2.2.2.1
  obtain ⟨hgen, hspan⟩ := GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT hψ hS hT a h1 h2 (GlobalTheory.PlaceModelSum.infPart_split ha)
  have st := fun f (hf : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f) =>
    (GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ f hf.1).2 (.inl v) hf
  have l0 := base_isLocal hb (.inl v)
  have lz : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) 0 := by
    have := (st f₀ l0).2.1 (-1) f₀ l0
    rwa [neg_one_smul, neg_add_cancel] at this
  refine ⟨?_, fun Tm hTm => ⟨fun Φ hΦ => ?_, fun x hx => ?_⟩⟩
  · have ho : GlobalTheory.PlaceModelSum.IsOrthSum a :=
      ⟨Unit, {()}, fun _ => a, fun _ _ => ha, fun _ _ _ _ h => absurd rfl h, by rw [Finset.sum_singleton]⟩
    exact ho.exists_model hψ hS hT h2 hb.2.2.2.2.2.lat
  · refine Submodule.span_induction (p := fun Φ _ => IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ))
      ?_ ?_ ?_ ?_ (hspan Φ hΦ)
    · rintro _ ⟨x, y, hx, hy, rfl⟩
      rw [(hgen x y hx hy).2 f₀ Tm hTm]
      have e1 := (st f₀ l0).1 x
      rw [wAt_of_half h2 hs hx] at e1
      have e2 := (st _ e1).1 y
      rwa [wAt_of_half ((mul_comm _ _).trans h2) ((add_comm _ _).trans hs) hy] at e2
    · rw [map_zero]; exact lz
    · intro x y _ _ hx hy
      have := (st _ hx).2.1 1 _ hy
      rw [one_smul] at this
      rw [map_add (f := _)]; exact this
    · intro c x _ hx
      have := (st _ hx).2.1 c _ lz
      rw [add_zero] at this
      rw [map_smul]; exact this
  · refine Submodule.span_induction
      (p := fun x _ => ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x)
      ?_ ?_ ?_ ?_ (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)
    · rintro _ ⟨w, rfl⟩
      have hx : IsHalf a (a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, h1]
      have hy : IsHalf (cA D a) (cA D a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, c1]
      obtain ⟨g1, g2⟩ := hgen _ _ hx hy
      refine ⟨_, sb_smul (ψ (-symplOH S T (cA D a • w) (a • w))) g1, ?_⟩
      rw [map_smul, g2 f₀ Tm hTm, GlobalTheory.SplitScalar.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, one_smul, ← add_smul, add_comm, hs]
      rfl
    · exact ⟨0, sb_zero _ _, map_zero _⟩
    · rintro _ _ _ _ ⟨Φ, hΦ, rfl⟩ ⟨Ψ, hΨ, rfl⟩
      exact ⟨Φ + Ψ, sb_add hΦ hΨ, map_add _ _ _⟩
    · rintro c _ _ ⟨Φ, hΦ, rfl⟩
      exact ⟨c • Φ, sb_smul c hΦ, map_smul _ _ _⟩

end GlobalTheory.SymmetricBilinearHalf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceModelOnto

variable {D : D7}

theorem isSBHalf_zero {m n : ℕ} (a : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf a Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem isSBHalf_smul {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf a Λ Φ) : IsSBHalf a Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (hne t ht), k, hk,
    fun u hu hu' t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hu' t], fun t ht => h3 t (hne t ht)⟩

theorem isSBHalf_add {m n : ℕ} {a : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf a Λ Φ) (h' : IsSBHalf a Λ Ψ) : IsSBHalf a Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have hne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf a u → IsHalf a (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hu' t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (hh _ _ hu') t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (hh _ _ hu') t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem placeModel_onto_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → a + cA D a = idem D (.inl v) → (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧ ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → (∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ)) ∧ ∀ x, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x := by
  first
  | exact @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local
  | (apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SymmetricBilinearHalf.placeModel_onto_local ..)

end GlobalTheory.PlaceModelOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentBaseFunctionIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_idempotent_base_function_identity : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (a : AE D), IsSplitIdem D a → a + cA D a = idem D (.inl v) → (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧ ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → (∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ)) ∧ ∀ x, IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x := by
  first | exact @GlobalTheory.PlaceModelOnto.placeModel_onto_local | exact GlobalTheory.PlaceModelOnto.placeModel_onto_local | (intros; apply GlobalTheory.PlaceModelOnto.placeModel_onto_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralOfPowEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section
namespace GlobalTheory.RowEx

theorem exists_nf_of_finite (S : Set ℂ) (hS : S.Finite) (hi : ∀ z ∈ S, IsIntegral ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ S ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hi, fun z hz => ?_⟩
  exact ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩

theorem rootsOne_finite {n : ℕ} (hn : 0 < n) : {z : ℂ | z ^ n = 1}.Finite :=
  (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
    simpa [Polynomial.mem_nthRoots hn] using hz

theorem isIntegral_of_pow_eq_one {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z ^ n = 1) : IsIntegral ℚ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by simp [hz]⟩

theorem isIntegral_sqrt_nat (k : ℕ) : IsIntegral ℚ ((Real.sqrt k : ℝ) : ℂ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C ((k : ℚ)), Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
  have h0 : ((Real.sqrt k : ℝ) : ℂ) ^ 2 = (k : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  simp [Polynomial.eval₂_sub, h0]

end GlobalTheory.RowEx
end

namespace GlobalTheory.RowEx

theorem nfRoot : NFRoot := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hs ch _ _ => ?_⟩⟩
  haveI : Finite T := hs.fin
  classical
  set G := ch.G
  set S := ch.S.toGridChoice
  have hN : ∀ w : Pl D.host.E, 0 < Ideal.absNorm w.asIdeal ^ depthAt G w := fun w =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)) _
  let P : Set (Pl D.host.E) := {w | w ∈ S.PA ∨ ∃ t, w ∈ locPl G t}
  have hP : P.Finite := by
    refine ((S.PA.finite_toSet).union (Set.finite_iUnion fun t => (locPl G t).finite_toSet)).subset ?_
    rintro w (hw | ⟨t, hw⟩)
    · exact Or.inl hw
    · exact Or.inr (Set.mem_iUnion.2 ⟨t, hw⟩)
  let Q : Set (Pl D.host.E) := ⋃ t, (locPl G t : Set (Pl D.host.E))
  have hQ : Q.Finite := Set.finite_iUnion fun t => (locPl G t).finite_toSet
  let X : Set ℂ := {z | z ^ 8 = 1} ∪ (⋃ w ∈ Q, {z : ℂ | z ^ (Ideal.absNorm w.asIdeal ^ depthAt G w) = 1}) ∪
    (fun w : Pl D.host.E => ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)) '' P
  have hX : X.Finite :=
    ((rootsOne_finite (by norm_num)).union (hQ.biUnion fun w _ => rootsOne_finite (hN w))).union (hP.image _)
  have hi : ∀ z ∈ X, IsIntegral ℚ z := by
    rintro z ((hz | hz) | ⟨w, -, rfl⟩)
    · exact isIntegral_of_pow_eq_one (by norm_num) hz
    · obtain ⟨w, -, hz⟩ := Set.mem_iUnion₂.1 hz
      exact isIntegral_of_pow_eq_one (hN w) hz
    · exact isIntegral_sqrt_nat _
  obtain ⟨M, hM, hMX⟩ := exists_nf_of_finite X hX hi
  refine ⟨M, hM, fun z hz => hMX (Or.inl (Or.inl hz)), fun t w hw z hz => hMX (Or.inl (Or.inr ?_)), fun w hw => hMX (Or.inr ⟨w, hw, rfl⟩)⟩
  exact Set.mem_iUnion₂.2 ⟨w, Set.mem_iUnion.2 ⟨t, hw⟩, hz⟩

end GlobalTheory.RowEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExOfSeparates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols Separates rowForm)

noncomputable section

namespace GlobalTheory.RowEx

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}


set_option maxHeartbeats 1000000 in
theorem inj_of_sep_conv {ch : Choice R} (hM : R.IsModels) (hsep : Separates R ch.W ch.M ch.w ch.ρ ch.ξ)
    (hconv : ∀ a u, ConvK ch a u) (u : R.HE.H) (hu : ∀ a, psiK ch a u = 0) : u = 0 := by
  by_contra h0
  have hmem : R.HE.e u ∈ R.EEat R.triv := hM.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have hne : R.HE.e u ≠ 0 := fun h => h0 (hM.HE.1 (h.trans (map_zero _).symm))
  obtain ⟨Ψ, hΨ, Φ, -, hf⟩ := hsep _ hmem hne
  apply hf
  rw [← span_col_eq_cols ch Φ] at hΨ
  have key : ∀ x ∈ Submodule.span ℂ (ch.col '' {a | ch.Phi a = Φ}),
      BplusConv ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) ∧
        Bplus ch.W ch.M (pairVec (coefPlus ch.G ch.W.θ) ch.ξ x)
          (thetaChi ch.W ch.M ch.ρ Φ (rowForm R ch.w (R.HE.e u))) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha' : ch.Phi a = Φ := ha
      have h1 : FConv ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) := hconv a u
      have h2 : fPsiPhi ch.W ch.M ch.ρ ch.ξ (ch.col a) (ch.Phi a) (ch.form u) = 0 := hu a
      rw [ha'] at h1 h2
      exact ⟨h1.2, h2⟩
    | zero =>
      rw [LinearMap.map_zero (pairVec (coefPlus ch.G ch.W.θ) ch.ξ)]; exact bplusConv_zero ch.W ch.M _
    | add x y _ _ hx hy =>
      rw [LinearMap.map_add (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) x y]
      obtain ⟨hc, he⟩ := bplusConv_add ch.W ch.M hx.1 hy.1
      exact ⟨hc, by rw [he, hx.2, hy.2, add_zero]⟩
    | smul c x _ hx =>
      rw [LinearMap.map_smul (pairVec (coefPlus ch.G ch.W.θ) ch.ξ) c x]
      obtain ⟨hc, he⟩ := bplusConv_smul ch.W ch.M c hx.1
      exact ⟨hc, by rw [he, hx.2, mul_zero]⟩
  exact (key Ψ hΨ).2


set_option maxHeartbeats 1000000 in
theorem isEx_of_separates (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) (hB : BaseEx) : IsEx := by
  obtain ⟨C1, hL⟩ := hL
  obtain ⟨C2, hB⟩ := hB
  refine ⟨max 6510 (max C1 C2), fun ε CF hCF => ?_⟩
  obtain ⟨x1, hS⟩ := hS ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, hL⟩ := hL ε CF (le_trans (le_max_left _ _) (le_of_max_le_right hCF))
  obtain ⟨x3, hB⟩ := hB ε CF (le_trans (le_max_right _ _) (le_of_max_le_right hCF))
  refine ⟨max x1 (max x2 x3), fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset G W hW S₀ => ?_⟩
  have hx1 : x1 ≤ large₂.sc.x := le_of_max_le_left hx
  have hx2 : x2 ≤ large₂.sc.x := le_trans (le_max_left _ _) (le_of_max_le_right hx)
  have hx3 : x3 ≤ large₂.sc.x := le_trans (le_max_right _ _) (le_of_max_le_right hx)
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS0, hbase⟩ := hB D large₂ hε hx3 Γ Pl0 T A Ks R F hset G W hW S₀
  obtain ⟨ρ', ξ', hsep⟩ := hS D large₂ hε hx1 hset.size hset.eser Γ Pl0 T A Ks R hset.core.lev hset.grp G W hbase.weil M
    hbase.vol _ hbase.w_ne
  have hconv := hL D large₂ hε hx2 Γ Pl0 T A Ks R F hset _ rfl (hbase.withReal ρ' ξ')
  exact ⟨M, ρ', ξ', cv, rm, S, rp, n, e, c, hS0,
    hbase.is_withReal (inj_of_sep_conv hset.core.models hsep hconv)⟩

end GlobalTheory.RowEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExKeyOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowEx


set_option maxHeartbeats 1600000 in
theorem exKey_of (h1 : GridEx) (h2 : IsEx) (h3 : NFAll) (cG : CarryG) (cW : CarryW) (cS : CarryS)
    (t1 : TrEasy) (t2 : TrPhase) (t3 : TrJet) (t4 : TrBot) : ExKey := by
  classical
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_right (le_of_max_le_right hC))
  refine ⟨max x1 (max x2 x3), fun s he hx P f κ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_right (le_of_max_le_right hx)
  by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
      (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
      (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks X.toD7.what₂.LL)
      (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ
  swap
  · exact ⟨∅, by simp, fun X f' a b large₂ c Γ _ _ Pl0 T A Ks _ _ _ R F d e g i _ =>
      absurd ⟨X, f', a, b, large₂, c, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, d, e, g, i⟩ H⟩
  obtain ⟨X0, f0, a0, b0, Lg0, rfl, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, d0, e0, g0, i0⟩ := H
  obtain ⟨G0, W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 g0
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G0 W0 hW0 S0
  obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
  refine ⟨Finset.univ.image fun i => ((b i : N) : ℂ), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
  intro X f' a b' large₂ hs Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i hz
  have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
  have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
  have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
    rintro P _ rfl k k' h x hx
    obtain rfl := eq_of_heq h
    exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
  have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
    obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
    exact ⟨t0, h⟩
  choose ι hι using hι
  have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
  have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
    rw [d0.core.lev.xi_base]
    have := (hι A.μ0).1
    rw [d.core.lev.xi_base] at this
    exact eq_of_heq (this.symm.trans (one _ _ hpre)))
  have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
    ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX, d.betaX⟩
  obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G0
  obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G0 G hG W0
  obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G0 G hG W0 W hWA S.toGridChoice
  have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
  have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
  rw [hs] at h2'
  obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
  refine ⟨_, hIs', rfl, ?_⟩
  obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
  have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root, t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase,
    t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios, t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
  subst hS2
  refine hAll'.numbersIn.mono ?_
  rintro _ ⟨y, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr y, map_sum]
  refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hz _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

end GlobalTheory.RowEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeAlgebraMapMono
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

section Mono

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
  {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {S : GridChoice W Set.univ}

theorem charsIn_mono (h : CharsIn G σ) (hσ : Set.range σ ⊆ Set.range σ') : CharsIn G σ' :=
  ⟨fun j w x => hσ (h.mu0 j w x), fun t w x => hσ (h.xi t w x),
    fun i a b w x => hσ (h.chi i a b w x), fun v hv => hσ (h.eta v hv), fun v hv => hσ (h.chiPsi v hv),
    fun v hv => hσ (h.del v hv), fun v hv => hσ (h.del' v hv)⟩

theorem rootCl_mono (h : RootCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : RootCl σ' S :=
  ⟨fun z hz => hσ (h.1 z hz), fun t w hw z hz => hσ (h.2.1 t w hw z hz), fun w hw => hσ (h.2.2 w hw)⟩

theorem phaseCl_mono (h : PhaseCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : PhaseCl σ' S :=
  fun t Φ β hβ w x y e a b => hσ (h t Φ β hβ w x y e a b)

theorem jetCl_mono (h : JetCl σ S) (hσ : Set.range σ ⊆ Set.range σ') : JetCl σ' S :=
  fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hσ ((h t Φ β hβ τ hτ d hd c).1 j a b),
    fun i a b => hσ ((h t Φ β hβ τ hτ d hd c).2 i a b)⟩

theorem lRatios_mono {μ₀ : T} (h : ∀ i j, LRatiosIn G σ μ₀ i j) (hσ : Set.range σ ⊆ Set.range σ') :
    ∀ i j, LRatiosIn G σ' μ₀ i j :=
  fun i j t Λ Λ₀ a b s c d e => hσ (h i j t Λ Λ₀ a b s c d e)

theorem botCl_mono (h : BotCl W σ) (hσ : Set.range σ ⊆ Set.range σ') : BotCl W σ' := by
  intro i j
  obtain ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, H⟩ := h i j
  exact ⟨A, A', WW, X, h1, Ω, Ω', h2, h3, fun t g hg =>
    ⟨fun k hk => hσ ((H t g hg).1 k hk), fun k hk => hσ ((H t g hg).2 k hk)⟩⟩

end Mono

theorem range_algebraMap_mono {M M' : IntermediateField ℚ ℂ} (h : M ≤ M') :
    Set.range (algebraMap M ℂ) ⊆ Set.range (algebraMap M' ℂ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.1, h x.2⟩, rfl⟩

theorem InNF.and {Q Q' : ∀ M : IntermediateField ℚ ℂ, (M →+* ℂ) → Prop}
    (hQ : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q M (algebraMap M ℂ) → Q M' (algebraMap M' ℂ))
    (hQ' : ∀ M M' : IntermediateField ℚ ℂ, M ≤ M' → Q' M (algebraMap M ℂ) → Q' M' (algebraMap M' ℂ))
    (h : InNF Q) (h' : InNF Q') : InNF fun M σ => Q M σ ∧ Q' M σ := by
  obtain ⟨M, hM, hq⟩ := h
  obtain ⟨M', hM', hq'⟩ := h'
  exact ⟨M ⊔ M', IntermediateField.finiteDimensional_sup M M', hQ _ _ le_sup_left hq, hQ' _ _ le_sup_right hq'⟩

theorem nfAll_of : NFChars → NFRoot → NFPhase → NFJet → NFRatio → NFBot → NFAll := by
  intro h1 h2 h3 h4 h5 h6
  obtain ⟨CF0, H⟩ := Big.and h1 (Big.and h2 (Big.and h3 (Big.and h4 (Big.and h5 h6))))
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi ha
  have k := InNF.and (fun M M' h q => charsIn_mono q (range_algebraMap_mono h))
    (fun M M' h q => rootCl_mono q (range_algebraMap_mono h)) c1 c2
  have k := InNF.and (fun M M' h q => ⟨charsIn_mono q.1 (range_algebraMap_mono h), rootCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => phaseCl_mono q (range_algebraMap_mono h)) k c3
  have k := InNF.and (fun M M' h q => ⟨⟨charsIn_mono q.1.1 (range_algebraMap_mono h), rootCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      phaseCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => jetCl_mono q (range_algebraMap_mono h)) k c4
  have k := InNF.and (fun M M' h q => ⟨⟨⟨charsIn_mono q.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => lRatios_mono q (range_algebraMap_mono h)) k c5
  have k := InNF.and (fun M M' h q => ⟨⟨⟨⟨charsIn_mono q.1.1.1.1 (range_algebraMap_mono h),
      rootCl_mono q.1.1.1.2 (range_algebraMap_mono h)⟩, phaseCl_mono q.1.1.2 (range_algebraMap_mono h)⟩,
      jetCl_mono q.1.2 (range_algebraMap_mono h)⟩, lRatios_mono q.2 (range_algebraMap_mono h)⟩)
    (fun M M' h q => botCl_mono q (range_algebraMap_mono h)) k c6
  obtain ⟨M, hM, ⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩⟩ := k
  exact ⟨M, hM, ⟨q1, q2, q3, q4, q5, q6⟩⟩

end GlobalTheory.RowEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrEasy
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx


set_option maxHeartbeats 1000000 in
theorem trEasy : TrEasy := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ
  obtain ⟨⟨hpre, -, -, hC, hbase, hxi, hQ, -⟩, hg, -, hs⟩ := h
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B
  cases B'
  dsimp only at hpre
  subst hpre
  obtain ⟨f, f', hff, hLC, hLC'⟩ := hC
  have hf : f' = f := eq_of_heq hff
  subst hf
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hxi' : ∀ t, L'.xiH t = L.xiH (ι t) := fun t => eq_of_heq (hxi t)
  have hQ' : ∀ t, L'.Q t = L.Q (ι t) := fun t => eq_of_heq (hQ t)
  have hPA : S'.PA = S.PA := eq_of_heq hs.PA
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : ∀ t, locPl G' t = locPl G (ι t) := fun t => by
    unfold locPl
    rw [hW0, hQ' t]
    rfl
  have hdep : ∀ w, depthAt G' w = depthAt G w := fun w => by
    unfold depthAt cosExp Places.depth
    rw [hW0, hv0]
    rfl
  refine ⟨fun hch => ?_, fun hr => ?_, fun hr => ?_⟩
  · refine ⟨fun j => ?_, fun t => ?_, fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · have := hch.mu0 j
      rw [hLC] at this
      rw [hLC']
      exact this
    · rw [hxi' t]
      exact hch.xi (ι t)
    · rw [hchi]
      exact hch.chi i h1 h2
    · have := hch.eta
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.chiPsi
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del'
      rw [hLC] at this
      rw [hLC']
      exact this
  · refine ⟨hr.1, fun t w hwt => ?_, fun w hw' => ?_⟩
    · rw [hdep]
      rw [hloc] at hwt
      exact hr.2.1 (ι t) w hwt
    · rcases hw' with hw' | ⟨t, hw'⟩
      · rw [hPA] at hw'
        exact hr.2.2 w (Or.inl hw')
      · rw [hloc] at hw'
        exact hr.2.2 w (Or.inr ⟨ι t, hw'⟩)
  · intro i j t Λ Λ₀ h1 h2 s hs1 hs2 hΛ
    have hν : ∀ t, SqNum.nuH G' t i j = SqNum.nuH G (ι t) i j := fun t => by
      unfold SqNum.nuH
      rw [hLC', hLC, hxi' t, hchi]
      rfl
    rw [hν] at h1
    rw [hν, hbase] at h2
    exact hr i j (ι t) Λ Λ₀ h1 h2 s hs1 hs2 hΛ

end GlobalTheory.RowEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrPhaseOfTrFlip
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

open GlobalTheory.SplitWeil GlobalTheory.SplitFlip MeasureTheory
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.RowEx.PhaseCarry

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {K : Type} [Field K] (σ : K →+* ℂ)

def PhW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  ∀ x y e, (unfTerm ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T β).datum x y ≠ 0 →
    moved Γ keep ((Reps.through hs J (stair Γ ϖ c)).elt β) T (fill hs x y e) ≠ 0 → (ψ (phase x e) : ℂ) ∈ Set.range σ

def SuW (Γ : Grid k) (hs : 1 ≤ Γ.s) (J : Γ.Level) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool) (ϖ : kˣ) (c : ℕ)
    (T : Γ.Args → ℂ) (β : Cosets hs J) : Prop :=
  β ∈ unfSupport ψ ν keep (Reps.through hs J (stair Γ ϖ c)) T

end Loc

section Loc2

variable {k : Type} {_ : Field k} {_ : ValuativeRel k} {_ : TopologicalSpace k} {_ : IsNonarchimedeanLocalField k}
  {_ : MeasurableSpace k} {_ : BorelSpace k} {K : Type} [Field K] (σ : K →+* ℂ)

theorem congrW {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    {ψ ψ' : AddChar k Circle} (hψ : ψ = ψ') {ν ν' : Measure k} (hν : ν = ν') {keep keep' : Bool} (hk : keep = keep')
    (ϖ : kˣ) {c c' : ℕ} (hc : c = c') {T : Γ.Args → ℂ} {T' : Γ'.Args → ℂ} (hT : HEq T T') {β : Cosets hs J}
    {β' : Cosets hs' J'} (hβ : HEq β β') :
    (PhW σ Γ hs J ψ ν keep ϖ c T β ↔ PhW σ Γ' hs' J' ψ' ν' keep' ϖ c' T' β') ∧
      (SuW Γ hs J ψ ν keep ϖ c T β ↔ SuW Γ' hs' J' ψ' ν' keep' ϖ c' T' β') := by
  subst hΓ hψ hν hk hc
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hT
  obtain rfl := eq_of_heq hβ
  exact ⟨Iff.rfl, Iff.rfl⟩

def castCos {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level} (hJ : HEq J J')
    (β : Cosets hs J) : Cosets hs' J' := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  exact β

theorem castCos_heq {Γ Γ' : Grid k} (hΓ : Γ = Γ') {hs : 1 ≤ Γ.s} {hs' : 1 ≤ Γ'.s} {J : Γ.Level} {J' : Γ'.Level}
    (hJ : HEq J J') (β : Cosets hs J) : HEq (castCos hΓ (hs' := hs') hJ β) β := by
  subst hΓ
  obtain rfl := eq_of_heq hJ
  rfl

end Loc2


set_option maxHeartbeats 4000000 in
theorem trPhase_of_trFlip : TrFlip → TrPhase := by
  intro hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA M σ hS t' Φ' β' hβ'
  obtain ⟨Φ, hΦ⟩ := hF X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι hA Φ'
  have hpre := hA.l.pre
  have hv0 := hA.g.v0
  have hw := hA.g.w
  have hQ := hA.l.Q t'
  have hψ := hA.w.ψ
  clear hF hA
  rcases X with ⟨⟨P⟩, _, _, _, _, _, _⟩
  rcases X' with ⟨⟨P'⟩, _, _, _, _, _, _⟩
  dsimp only at hpre
  subst hpre
  replace hv0 := eq_of_heq hv0
  replace hw := eq_of_heq hw
  replace hQ := eq_of_heq hQ
  replace hψ := eq_of_heq hψ
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : locPl G' t' = locPl G (ι t') := by
    unfold locPl
    rw [hW0, hQ]
    rfl
  have hcos : ∀ w, cosExp G' w = cosExp G w := fun w => by
    unfold cosExp Places.depth
    rw [hW0, hv0]
    rfl
  have hkeep : ∀ w, keepAt G' w = keepAt G w := fun w => by
    unfold keepAt
    rw [hW0]
    rfl
  have hpsi : ∀ w, psiAt W' w = psiAt W w := fun w => by
    ext x
    show (W'.ψ _ : ℂ) = W.ψ _
    rw [hψ]
    rfl
  have hmem : ∀ w, w ∈ locPl G (ι t') → w ∈ locPl G' t' := fun w h => hloc ▸ h
  have hF3 := fun w (h : w ∈ locPl G' t') => hΦ t' w w HEq.rfl h
  have hΓ : ∀ w (h : w ∈ locPl G' t'), locGrid G' t' w = locGrid G (ι t') w := fun w h => eq_of_heq (hF3 w h).1
  let β : CosFam G (ι t') := fun w => castCos (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (β' ⟨w.1, hmem _ w.2⟩)
  have hβh : ∀ w : locPl G (ι t'), HEq (β' ⟨w.1, hmem _ w.2⟩) (β w) := fun w => (castCos_heq _ _ _).symm
  have hβ : β ∈ S.supp (ι t') Φ := fun w =>
    ((congrW σ (hΓ w.1 (hmem _ w.2)) (hF3 w.1 (hmem _ w.2)).2.1 (hpsi w.1) rfl (hkeep w.1) (unifAt w.1)
      (hcos w.1) (hF3 w.1 (hmem _ w.2)).2.2 (hβh w)).2).mp (hβ' ⟨w.1, hmem _ w.2⟩)
  intro w'
  have hw' : w'.1 ∈ locPl G (ι t') := hloc ▸ w'.2
  exact ((congrW σ (hΓ w'.1 w'.2) (hF3 w'.1 w'.2).2.1 (hpsi w'.1) rfl (hkeep w'.1) (unifAt w'.1)
      (hcos w'.1) (hF3 w'.1 w'.2).2.2 (hβh ⟨w'.1, hw'⟩)).1).mpr (hS (ι t') Φ β hβ ⟨w'.1, hw'⟩)

end GlobalTheory.RowEx.PhaseCarry
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparatesLinB
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

theorem injK_of_separates_linB (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate) (hL : LinB) : InjK := by
  refine GlobalTheory.RowTest.injK_of_separates hS ?_
  rcases hL with ⟨C0, hL⟩
  refine ⟨C0, fun ε CF hCF => ?_⟩
  obtain ⟨x0, hL⟩ := hL ε CF hCF
  refine ⟨x0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc ρ ξ a u => ?_⟩
  exact hL D large₂ hε hx Γ Pl0 T A Ks R F hset (ch.withReal ρ ξ) hsc (hch.toIsBase.withReal ρ ξ) a u


end GlobalTheory.RowEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizeGap_of_sizes : SizeGap :=
  fun _ => ⟨0, fun _ large₂ _ _ h => GlobalTheory.RowSizes.sizes_of_sizeRows large₂ h⟩

end GlobalTheory.SepRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.largeScaleSizes_imply_gapConditions : SizeGap := by
  first | exact @GlobalTheory.SepRows.sizeGap_of_sizes | exact GlobalTheory.SepRows.sizeGap_of_sizes | (intros; apply GlobalTheory.SepRows.sizeGap_of_sizes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colMapV (S : GridChoice W U) (t : T) (v : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U) (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (v ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairV (S : GridChoice W U) (t : T) {δ : Type} (τ : δ →₀ ℂ)
    (c : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (colMapV S t (c d) x) (rowMapV S (r d) y)

theorem pairPts_eq_pairV (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) :
    pairPts S τ x y = pairV S t τ (fun d j => S.Z.vec (d.1 j)) (fun d i => S.Z.vec (d.2 i)) x y := rfl

def movedCol (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => S.Z.vec (d.1 j')) ⟨j, by omega⟩
      (W.om (.top t j) (1, (g : GA D (G.V (.top (j + 1))))) (S.Z.vec (d.1 ⟨j, by omega⟩))))
    ⟨j + 1, hj⟩ (W.om (.top t (j + 1)) ((g : GA D (G.V (.top (j + 1)))), 1) (S.Z.vec (d.1 ⟨j + 1, hj⟩)))

end GlobalTheory.ExpansionInvariance

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerie
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerie
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLine

theorem itLine_of_discreteSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  intro hCover hModules D

  rcases GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis hCover hModules with ⟨X, hParam, -, -, -, -, hAR3, -⟩

  have hBridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra hCover hModules D
  have hVac : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := GlobalTheory.T.thetaVacuumCharacters_realPlaces D
  exact itLine D X hParam hAR3 hVac hBridge hModules

end GlobalTheory.Chain.RealLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerieStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  first | exact @GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | exact GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | (intros; apply GlobalTheory.Chain.RealLine.itLine_of_discreteSeries <;> assumption)
end
end
