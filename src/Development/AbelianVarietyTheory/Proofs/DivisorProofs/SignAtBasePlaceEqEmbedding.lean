module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffRealStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemOfCoeffReal
open Formalism.L2.DIV

namespace GlobalTheory.CuspMult

theorem idemOf_coeff_real : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ)
    (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X →
    ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  intro K G _ _ _ σ X hX hS g
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_idemOf, map_sum, star_sum]
  refine Finset.sum_nbij' (fun χ t => χ t⁻¹) (fun χ t => χ t⁻¹) hS hS
    (fun χ _ => by simp) (fun χ _ => by simp) fun χ hχ => ?_
  have h1 := (hX χ hχ).map_inv σ 1
  have h2 := (hX χ hχ).map_inv σ g⁻¹
  simp only [map_mul, map_div₀, map_natCast, star_mul', star_div₀, star_natCast]
  rw [h1, h2]
  rfl

end GlobalTheory.CuspMult
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_idemOf_coeff_eq_self : ∀ {K G : Type} [Field K] [Group G] [Fintype G] (σ : K →+* ℂ) (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → GoodStable X → ∀ g, star (σ ((idemOf X).coeff g)) = σ ((idemOf X).coeff g) := by
  first | exact @GlobalTheory.CuspMult.idemOf_coeff_real | exact GlobalTheory.CuspMult.idemOf_coeff_real | (intros; apply GlobalTheory.CuspMult.idemOf_coeff_real <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqTrans

theorem asAlg_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (x : MonoidAlgebra ℂ H) :
    Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) x =
      ρ.asAlgebraHom (MonoidAlgebra.domCongr ℂ ℂ e x) := by
  have : Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) =
      ρ.asAlgebraHom.comp (MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp
    · exact Subsingleton.elim _ _
  rw [this]; rfl

theorem killed_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (I : Set (MonoidAlgebra ℂ H)) (I' : Set (MonoidAlgebra ℂ H'))
    (h1 : ∀ x ∈ I, MonoidAlgebra.domCongr ℂ ℂ e x ∈ I')
    (h2 : ∀ x ∈ I', MonoidAlgebra.domCongr ℂ ℂ e.symm x ∈ I) :
    killed (ρ.comp e.toMonoidHom : Representation ℂ H X) I = killed ρ I' := by
  ext v
  rw [mem_killed, mem_killed]
  constructor
  · intro h x hx
    have := h _ (h2 x hx)
    rw [asAlg_comp, ← MonoidAlgebra.domCongr_symm, AlgEquiv.apply_symm_apply] at this
    exact this
  · intro h x hx
    rw [asAlg_comp]
    exact h _ (h1 x hx)

theorem isDC_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (J : Subgroup H) (J' : Subgroup H')
    (hJ : ∀ g, g ∈ J ↔ e g ∈ J') (x : H) (R : Finset H) (h : Bridge.IsDC J x R) :
    Bridge.IsDC J' (e x) (R.map e.toEquiv.toEmbedding) := by
  have hJ' : ∀ g' : J', e.symm g' ∈ J := fun g' => (hJ _).2 (by simp)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨⟨e k₁, (hJ _).1 k₁.2⟩, ⟨e k₂, (hJ _).1 k₂.2⟩, by simp⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 (e.symm k₁ * x * e.symm k₂) ⟨⟨_, hJ' k₁⟩, ⟨_, hJ' k₂⟩, rfl⟩
    refine ⟨e a, ⟨Finset.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · have := (hJ _).1 ha'
      simpa using this
    · rintro b ⟨hb, hb'⟩
      obtain ⟨b, hbR, rfl⟩ := Finset.mem_map.1 hb
      have : b = a := hu b ⟨hbR, (hJ _).2 (by simpa using hb')⟩
      rw [this]; rfl

variable {D : D7}

theorem mem_levG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GfC V) :
    (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      finE V (k : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ∧
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (k : GA D V)) : G0 Pg r) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩

theorem levChi_eq (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GA D V) :
    levChi V β (withP (princDat V.rank r t hr Pg χ) P) k =
      ((ext1 P.H P.chi (rTup β (princDat V.rank r t hr Pg χ) (finE V k) : G0 Pg r) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  congr 1
  have h1 : (withP (princDat V.rank r t hr Pg χ) P).s = 0 := rfl
  have h2 : (withP (princDat V.rank r t hr Pg χ) P).Q = ∅ := rfl
  rw [h1, h2]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem map_mem (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank)
    (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃* GfC V')
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (hrk : V.rank = V'.rank)
    (h1 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔
      finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ'))
    (h2 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) →
      (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) =
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r))
    (h3 : ∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α))
    (x : MonoidAlgebra ℂ (GfC V)) (hx : x ∈ eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) :
    MonoidAlgebra.domCongr ℂ ℂ Φ x ∈ eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg := by
  have hlev : ∀ (P : LevelP Pg r ℂ) (k : GfC V), (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      (Φ k : GA D V') ∈ levG V' β' (withP (princDat V'.rank r t hr' Pg χ') P) := by
    intro P k
    rw [mem_levG, mem_levG]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨(h1 k).1 a, by rw [h2 k a]; exact b⟩
    · rintro ⟨a, b⟩
      have a' := (h1 k).2 a
      exact ⟨a', by rw [← h2 k a']; exact b⟩
  rcases hx with (⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩
  · refine Or.inl (Or.inl ⟨Φ k, (hlev P k).1 hk, ?_⟩)
    rw [levChi_eq, levChi_eq, h2 k ((mem_levG V β r t hr Pg χ P k).1 hk).1, map_sub, MonoidAlgebra.domCongr_single,
      MonoidAlgebra.domCongr_single, map_one Φ]
  · refine Or.inl (Or.inr ⟨fun g => Φ (κ g), fun g => ⟨(Φ (κ g)).2, (h1 _).1 (hκ g).2.1, ?_⟩, ?_⟩)
    · exact (h2 _ (hκ g).2.1).trans (hκ g).2.2
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ]
        simp only [MonoidAlgebra.domCongr_single]
  · refine Or.inr ⟨P0, hP0, k, hrk ▸ hk, Φ α, R.map Φ.toEquiv.toEmbedding, (h3 P0 hP0 k α).1 hα, ?_, ?_⟩
    · rw [← map_inv Φ]
      exact isDC_map Φ _ _ (fun g => hlev (LevelP.triv Pg r ℂ) g) _ _ hR
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ, Finset.sum_map]
        simp only [MonoidAlgebra.domCongr_single]
        rfl

theorem killed_eqSet_comp : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃ₜ* GfC V') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), V.rank = V'.rank → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) → (∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α)) → killed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC V) X) (eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) = killed ρ (eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg) := by
  intro D V V' β β' r t hr hr' Pg χ χ' Φ G _ _ eG c P Pl0 ok pl q Sg X _ _ ρ hrk h1 h2 h3
  refine killed_comp ρ Φ.toMulEquiv _ _
    (map_mem V V' β β' r t hr hr' Pg χ χ' Φ.toMulEquiv eG c P ok pl q Sg hrk h1 h2 h3) ?_
  have e : ∀ κ : GfC V', Φ (Φ.toMulEquiv.symm κ) = κ := fun κ => Φ.toMulEquiv.apply_symm_apply κ
  refine map_mem V' V β' β r t hr' hr Pg χ' χ Φ.toMulEquiv.symm eG c P ok pl q Sg hrk.symm ?_ ?_ ?_
  · intro κ
    rw [h1, e]
  · intro κ hκ
    have := h2 (Φ.toMulEquiv.symm κ) ((h1 _).2 (by rw [e]; exact hκ))
    rw [e] at this
    exact this.symm
  · intro P0 hP0 k α
    rw [h3 P0 hP0, e]

end GlobalTheory.CuspMult.EqTrans
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIsoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelTypeHecke_killed_correspond_matching_iso : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃ₜ* GfC V') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), V.rank = V'.rank → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) → (∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α)) → killed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC V) X) (eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) = killed ρ (eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg) := by
  first | exact @GlobalTheory.CuspMult.EqTrans.killed_eqSet_comp | exact GlobalTheory.CuspMult.EqTrans.killed_eqSet_comp | (intros; apply GlobalTheory.CuspMult.EqTrans.killed_eqSet_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMulRight
noncomputable section

open NumberField IsDedekindDomain Filter Topology
open scoped TensorProduct

namespace GlobalTheory.FiniteRingMultiplication

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def multN (N : ℕ) : AddSubgroup (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {z | ∃ s ∈ Formalism.L2.Herm.intAf F E, z = (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s}
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s + t, add_mem hs ht, (mul_add _ _ _).symm⟩
  zero_mem' := ⟨0, zero_mem _, (mul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨-s, neg_mem hs, (mul_neg _ _).symm⟩

theorem isOpen_intAd : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have h := RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

theorem exists_nat_mul_int (e : E) : ∃ m : ℕ, m ≠ 0 ∧ (m : E) * e ∈ Formalism.UG.intOE E := by
  have h : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic e)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  have h2 : IsIntegral ℤ ((y.natAbs : E) * e) := by
    rcases Int.natAbs_eq y with h3 | h3
    · have : (y.natAbs : E) * e = y • e := by
        conv_rhs => rw [h3]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * e = -(y • e) := by
        conv_rhs => rw [h3]
        simp
      rw [this]; exact hi.neg
  exact ⟨⟨_, h2⟩, rfl⟩

variable {F E}

theorem eventually_mul_right (N : ℕ) (hN : N ≠ 0) (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ a in 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), c * ((1 : E) ⊗ₜ[F] a) ∈ multN F E N := by
  induction c using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun a => by rw [zero_mul]; exact zero_mem _
  | add c d hc hd =>
    filter_upwards [hc, hd] with a h1 h2
    rw [add_mul]; exact add_mem h1 h2
  | tmul e u =>
    obtain ⟨m, hm, hme⟩ := exists_nat_mul_int E e
    set w : F := ((N : F) * (m : F))⁻¹ with hw
    have hc : Continuous fun a : FiniteAdeleRing (𝓞 F) F => (algebraMap F _ w * u) * a := continuous_const.mul continuous_id
    have h0 : (fun a : FiniteAdeleRing (𝓞 F) F => (algebraMap F _ w * u) * a) ⁻¹' (Formalism.UG.intAd F : Set _) ∈ 𝓝 0 :=
      ((isOpen_intAd F).preimage hc).mem_nhds (by
        show (algebraMap F _ w * u) * 0 ∈ Formalism.UG.intAd F
        rw [mul_zero]; exact zero_mem _)
    filter_upwards [h0] with a ha
    refine ⟨(((m : E) * e) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] ((algebraMap F _ w * u) * a)),
      mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, hme⟩, rfl⟩)) (Subring.subset_closure (Or.inr ⟨⟨_, ha⟩, rfl⟩)), ?_⟩
    have hN' : (N : F) ≠ 0 := by exact_mod_cast hN
    have hm' : (m : F) ≠ 0 := by exact_mod_cast hm
    have e1 : (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (N : F) := (map_natCast _ _).symm
    have e2 : (m : E) * e = (m : F) • e := by rw [Algebra.smul_def, map_natCast]
    rw [e1, e2, ← Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_assoc,
      ← Algebra.smul_def, mul_one, mul_one, one_mul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, smul_smul]
    have : (N : F) * (m : F) * w = 1 := by rw [hw]; field_simp
    rw [this, one_smul]

theorem eventually_mul_hom (N : ℕ) (hN : N ≠ 0)
    [TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E)] [IsModuleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)]
    (φ : AdeleRing (𝓞 F) F ⊗[F] E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hφ : ∀ a e, φ (a ⊗ₜ[F] e) = e ⊗ₜ[F] a.2) (c : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∀ᶠ b in 𝓝 (0 : AdeleRing (𝓞 F) F ⊗[F] E), c * φ b ∈ multN F E N := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set B := Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) (Module.finBasis F E) with hB
  have h1 : ∀ i, ∀ᶠ b in 𝓝 (0 : AdeleRing (𝓞 F) F ⊗[F] E),
      (c * (Module.finBasis F E i ⊗ₜ[F] 1)) * ((1 : E) ⊗ₜ[F] (B.coord i b).2) ∈ multN F E N := by
    intro i
    have hc : Continuous (B.coord i) := IsModuleTopology.continuous_of_linearMap _
    have hs : Continuous fun a : AdeleRing (𝓞 F) F => a.2 := continuous_snd
    have ht : Tendsto (fun b => (B.coord i b).2) (𝓝 0) (𝓝 0) := by
      refine (hs.comp hc).tendsto' 0 0 ?_
      show (B.coord i 0).2 = 0
      rw [map_zero]; rfl
    exact ht.eventually (eventually_mul_right N hN _)
  filter_upwards [eventually_all.2 h1] with b hb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← B.sum_repr b, map_sum, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  have := hb i
  rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
  rw [hB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, hφ]
  exact this

end General

theorem eventually_conj {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] {n : ℕ}
    (φ : A →+* B) (W : AddSubgroup B) (hφ : ∀ c, ∀ᶠ a in 𝓝 (0 : A), c * φ a ∈ W) (β : GL (Fin n) B) :
    ∀ᶠ g in 𝓝 (1 : GL (Fin n) A), ∀ x : GL (Fin n) B, x.val = g.val.map φ → ∀ i j, ((β⁻¹ * x * β).val - 1) i j ∈ W := by
  have h1 : ∀ i j k l, ∀ᶠ g in 𝓝 (1 : GL (Fin n) A), ((β⁻¹).val i k * β.val l j) * φ ((g.val - 1) k l) ∈ W := by
    intro i j k l
    have hc : Continuous fun g : GL (Fin n) A => (g.val - 1) k l :=
      (Units.continuous_val.sub continuous_const).matrix_elem k l
    have ht : Tendsto (fun g : GL (Fin n) A => (g.val - 1) k l) (𝓝 1) (𝓝 0) := hc.tendsto' 1 0 (by simp)
    exact ht.eventually (hφ _)
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
    eventually_all.2 fun l => h1 i j k l] with g hg x hx i j
  have e : (β⁻¹ * x * β).val - 1 = (β⁻¹).val * (g.val - 1).map φ * β.val := by
    have : (g.val - 1).map φ = x.val - 1 := by
      rw [hx]
      exact (map_sub φ.mapMatrix _ _).trans (by rw [map_one]; rfl)
    rw [this, Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine sum_mem fun k _ => ?_
  have := hg i j k l
  rw [Matrix.map_apply, mul_right_comm]
  exact this

section Group

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def finRing (D : D7) : AF D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (swapAE D).comp (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem finRing_tmul (D : D7) (a : AF D.host.F) (e : D.host.E) :
    finRing D (a ⊗ₜ[D.host.F] e) = e ⊗ₜ[D.host.F] a.2 := rfl

variable {D : D7} {V : HSp D}

theorem finE_val (g : GA D V) : (finE V g).val = (matHom V g).val.map (finRing D) := rfl

theorem finRing_sig (b : AF D.host.F ⊗[D.host.F] D.host.E) :
    finRing D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig b) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (finRing D b) := by
  induction b using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add c d hc hd => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hc, hd]
  | tmul a e => rfl

theorem finE_mem_UA (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).val * JR (AF D.host.F) V.gram *
    (matHom V g).val = JR (AF D.host.F) V.gram := g.2
  have h2 := congrArg (finRing D).mapMatrix h
  rw [map_mul, map_mul] at h2
  have e1 : (finRing D).mapMatrix (JR (AF D.host.F) V.gram) =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
    ext i j; rfl
  have e2 : (finRing D).mapMatrix (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (matHom V g).val) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (finE V g).val := by
    ext i j; exact finRing_sig _
  rw [e1, e2] at h2
  exact h2

theorem isModTop : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩

theorem isTopRing : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := by
  haveI := isModTop (D := D)
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  exact IsModuleTopology.isTopologicalRing (AF D.host.F) _

theorem isTopGroup : IsTopologicalGroup (GA D V) := by
  haveI := isTopRing (D := D)
  exact (inferInstance : IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

theorem eventually_entry (β : GL (Fin V.rank) (EAf D)) (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ g in 𝓝 (1 : GA D V), ∀ i j, ((β⁻¹ * finE V g * β).val - 1) i j ∈ multN D.host.F D.host.E N := by
  haveI := isModTop (D := D)
  haveI := isTopRing (D := D)
  have h1 : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  have ht : Tendsto (fun g : GA D V => matHom V g) (𝓝 1) (𝓝 1) := h1.tendsto' 1 1 rfl
  have h2 := ht.eventually (eventually_conj (finRing D) (multN D.host.F D.host.E N)
    (eventually_mul_hom N hN (finRing D) (finRing_tmul D)) β)
  filter_upwards [h2] with g hg
  exact hg _ (finE_val g)

end Group

section Princ

open Formalism.L2.DIV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem entry_int {N : ℕ} {m : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ i j, (m - 1) i j ∈ multN F E N) (i j : Fin n) : m i j ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨s, hs, e⟩ := h i j
  have : m i j = (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s + (1 : Matrix (Fin n) (Fin n) _) i j := by
    rw [← e, Matrix.sub_apply, sub_add_cancel]
  rw [this]
  refine add_mem (mul_mem (natCast_mem _ _) hs) ?_
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem mem_St_red {N : ℕ} (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h : ∀ i j, ((β⁻¹ * x * β).val - 1) i j ∈ multN F E N)
    (h' : ∀ i j, ((β⁻¹ * x⁻¹ * β).val - 1) i j ∈ multN F E N) :
    x ∈ St β ∧ ∀ PP : Pl E, (N : 𝓞 E) ∈ PP.asIdeal → redFn β PP x = 1 := by
  set S := Formalism.L2.Herm.intAf F E with hS
  let a : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, entry_int h i j⟩
  let b : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, entry_int h' i j⟩
  have ha : S.subtype.mapMatrix a = (β⁻¹ * x * β).val := rfl
  have hb : S.subtype.mapMatrix b = (β⁻¹ * x⁻¹ * β).val := rfl
  have hinj : Function.Injective (S.subtype.mapMatrix : Matrix (Fin n) (Fin n) S → _) := by
    intro u v huv
    ext i j
    exact congrFun (congrFun huv i) j
  let y : GL (Fin n) S :=
    ⟨a, b, hinj (by rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]; congr 1; group),
      hinj (by rw [map_mul, ha, hb, map_one, ← Units.val_mul, ← Units.val_one]; congr 1; group)⟩
  have hy : frGL β y = x := by
    have h1 : intGL F E n y = β⁻¹ * x * β := Units.ext rfl
    show β * intGL F E n y * β⁻¹ = x
    rw [h1]; group
  refine ⟨⟨y, hy⟩, fun PP hP => ?_⟩
  rw [← hy, redFn_frGL]
  apply Units.ext
  ext i j
  show resS F PP (a i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  obtain ⟨s, hs, e⟩ := h i j
  have h2 : a i j = (N : S) * ⟨s, hs⟩ + (1 : Matrix (Fin n) (Fin n) S) i j := by
    apply Subtype.ext
    have h3 : (((1 : Matrix (Fin n) (Fin n) S) i j : S) : E ⊗[F] Formalism.L2.Herm.Af F) =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, h3]
    show (β⁻¹ * x * β).val i j = _ * s + _
    rw [← e, Matrix.sub_apply, sub_add_cancel]
  have h4 : (N : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hP
  rw [h2, map_add (f := _), map_mul, map_natCast, h4, zero_mul, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem exists_nat_mem (T : Finset (Pl E)) : ∃ N : ℕ, N ≠ 0 ∧ ∀ PP ∈ T, (N : 𝓞 E) ∈ PP.asIdeal := by
  refine ⟨∏ PP ∈ T, Ideal.absNorm PP.asIdeal, Finset.prod_ne_zero_iff.2 fun PP _ h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h),
    fun PP hP => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Pl E => Ideal.absNorm PP.asIdeal) hP
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

end Princ

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.L2.DIV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem eventually_princ (β : GL (Fin V.rank) (EAf D)) (T : Finset (Pl D.host.E)) :
    ∀ᶠ g in 𝓝 (1 : GA D V), finE V g ∈ St β ∧ ∀ PP ∈ T, redFn β PP (finE V g) = 1 := by
  haveI := isTopGroup (D := D) (V := V)
  obtain ⟨N, hN, hT⟩ := exists_nat_mem T
  have h1 := eventually_entry β N hN
  have ht : Tendsto (fun g : GA D V => g⁻¹) (𝓝 1) (𝓝 1) := continuous_inv.tendsto' 1 1 inv_one
  filter_upwards [h1, ht.eventually h1] with g hg hg'
  rw [map_inv] at hg'
  obtain ⟨h2, h3⟩ := mem_St_red β (finE V g) hg hg'
  exact ⟨h2, fun PP hP => h3 PP (hT PP hP)⟩

theorem isOpen_stabiliser {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {β : GL (Fin V.rank) (EAf D)}
    {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G] {eG : G ≃* G0 L.Pg L.r} {c : G → ℂ}
    {P : LevelP L.Pg L.r ℂ} {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} {Sg : Pl0 → Polynomial ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ (GfC V) X} (hs : L.s = 0) (hQ : L.Q = ∅) {x : X}
    (hx : x ∈ GlobalTheory.CuspMult.killed ρ (GlobalTheory.CuspMult.eqSet V β L eG c P ok pl q Sg)) :
    IsOpen {g : GfC V | ρ g x = x} := by
  haveI := isTopGroup (D := D) (V := V)
  let S : Subgroup (GfC V) :=
    { carrier := {g | ρ g x = x}
      one_mem' := by show ρ 1 x = x; rw [map_one]; rfl
      mul_mem' := by
        intro a b ha hb
        show ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, show ρ b x = x from hb]; exact ha
      inv_mem' := by
        intro a ha
        show ρ a⁻¹ x = x
        conv_lhs => rw [← show ρ a x = x from ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  have ht : Tendsto (fun g : GfC V => (g : GA D V)) (𝓝 1) (𝓝 1) := continuous_subtype_val.tendsto' 1 1 rfl
  filter_upwards [ht.eventually (eventually_princ β L.Pg)] with k hk
  have hK : finE V k ∈ Kg D.sp.cm V.gram β L.Pg :=
    ⟨⟨finE_mem_UA _, hk.1⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hk.1, hk.2 PP hP⟩⟩
  have hlev : (k : GA D V) ∈ levG V β (withP L P) :=
    ⟨k.2, Kg_le_lev (D := withP L P) (Finset.Subset.refl _) (by show L.Q ⊆ _; rw [hQ]; exact Finset.empty_subset _) hK⟩
  have hr : rTup β (withP L P) (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk.2 PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  have hchi : levChi V β (withP L P) k = 1 := by
    have h1 : levFn β (withP L P) (finE V k) = 1 := by
      unfold levFn
      rw [hr, blockDiagonalExtendByOnePrimeField_one, show (withP L P).s = 0 from hs, show (withP L P).Q = ∅ from hQ]
      simp
    unfold levChi
    rw [h1, Units.val_one]
  have h0 := GlobalTheory.CuspMult.mem_killed.1 hx _ (Or.inl (Or.inl ⟨k, hlev, rfl⟩))
  rw [hchi, map_sub, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul, one_smul, map_one,
    LinearMap.sub_apply, sub_eq_zero] at h0
  exact h0

end Main

end GlobalTheory.FiniteRingMultiplication

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.PartDims

section Lin

theorem finrank_comap {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V U : Submodule ℂ X} {ip : X → X → ℂ}
    (h : M.Is V ip) (hU : U ≤ V) : Module.finrank ℂ (U.comap M.e) = Module.finrank ℂ U ∧ FiniteDimensional ℂ U := by
  have e : U.comap M.e ≃ₗ[ℂ] U :=
    (Submodule.equivMapOfInjective M.e h.1 (U.comap M.e)).trans
      (LinearEquiv.ofEq _ _ (Submodule.map_comap_eq_self (h.2.1.symm ▸ hU)))
  exact ⟨e.finrank_eq, e.finiteDimensional⟩

theorem homInto_comp {H H' S X : Type} [Group H] [Group H'] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ H S) (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃* H') :
    homInto σ (ρ.comp Φ.toMonoidHom : Representation ℂ H X) C =
      homInto (σ.comp Φ.symm.toMonoidHom : Representation ℂ H' S) ρ C := by
  ext f
  refine and_congr_right fun _ => ⟨fun h g s => ?_, fun h g s => ?_⟩
  · have := h (Φ.symm g) s
    simpa using this
  · have := h (Φ g) s
    simpa using this

end Lin

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

theorem mem_levi_flag_of_mem_parabolic (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) {κ : GA D V} (hκ : κ ∈ levG V β (flag1L L)) :
    κ ∈ levG V β (withP L P) ∧ levChi V β (withP L P) κ = 1 ∧ levChi V β (flag1L L) κ = 1 := by
  have h1 : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  refine ⟨⟨hκ.1, hκ.2.1, ?_⟩, ?_, ?_⟩
  · show rTup β L (finE V κ) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · rw [levChi_withP hs hQ, h1, blockDiagonalExtendByOnePrimeField_one]; rfl
  · have h := levChi_flag (β := β) hs hQ κ
    unfold levChi at h ⊢
    rw [levFn_flag1, h]

theorem mult_le {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' := by
  refine Submodule.span_mono fun T hT => ⟨hT.aut, hT.cusp, fun v k hk g => ?_, hT.equiv, hT.cont⟩
  rw [← (h k hk).2]
  exact hT.lev v k (h k hk).1 g

theorem goodPart_le_flag {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) :
    goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) e ≤
      goodPart θ M (levS V β (flag1L L)) (levChi V β (flag1L L)) e :=
  inf_le_inf_right _ (mult_le θ M fun k hk => by
    obtain ⟨h1, h2, h3⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
    exact ⟨h1, h2.trans h3.symm⟩)

variable {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)

theorem gaL_star (hs : L.s = 0) (hQ : L.Q = ∅) (hc : ∀ g, star (c g) = c g) (φ : GA D V → ℂ) :
    gaL V β L eG c (star φ) = star (gaL V β L eG c φ) := by
  funext h
  have h1 : ∀ g, actG0 V β L (eG g) (star φ) h = star (actG0 V β L (eG g) φ h) := by
    intro g
    unfold actG0
    split_ifs with hk
    · simp [levChi_flag hs hQ]
    · simp
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, Pi.star_apply, star_sum,
    smul_eq_mul, star_mul', hc]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (h1 g)

variable {eG c} {P : LevelP L.Pg L.r ℂ} {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ} {Sg : Pl0 → ℂ[X]}
  {X : Type} [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ (GfC V) X}

theorem fixed_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg))
    {k : GfC V} (hk : (k : GA D V) ∈ levG V β (flag1L L)) : ρ k x = x := by
  obtain ⟨h1, h2, -⟩ := mem_levi_flag_of_mem_parabolic hs hQ P hk
  have := mem_killed.1 hx _ (Or.inl (Or.inl ⟨k, h1, rfl⟩))
  simpa [h2, sub_eq_zero] using this

theorem isTopologicalGroup_GA (V : HSp D) : IsTopologicalGroup (GA D V) := by
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))

theorem isOpen_stab (hs : L.s = 0) (hQ : L.Q = ∅) {x : X} (hx : x ∈ killed ρ (eqSet V β L eG c P ok pl q Sg)) :
    IsOpen {g : GfC V | ρ g x = x} := by
  first
  | (rename_i h_5 h_6 h_16 h_17; revert D V β L G h_5 h_6 eG c P Pl0 ok pl q Sg X h_16 h_17 ρ hs hQ x hx; exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser)
  | exact @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser
  | (apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteRingMultiplication.isOpen_stabiliser ..)

theorem isGoodRep_of_killed (hs : L.s = 0) (hQ : L.Q = ∅) (hl : LiftsExist V β L)
    (h : killed ρ (eqSet V β L eG c P ok pl q Sg) ≠ ⊥) : IsGoodRep V β L eG c ρ := by
  obtain ⟨x, hx, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  choose κ hκ using fun g => hl (eG g)
  refine ⟨x, h0, fun k hk => fixed_of_killed hs hQ hx hk, fun g => ⟨κ g, (hκ g).1⟩, hκ, ?_⟩
  have := mem_killed.1 hx _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [sub_eq_zero, map_sum, LinearMap.sum_apply] using this

end Level

section Hecke

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Subgroup (GA D V)} {Pl0 : Type} {ok : Set Pl0}
  {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

theorem mem_hPart {Sg : Pl0 → ℂ[X]} {x : MMap M} : x ∈ hPart M J ok pl q Sg ↔
    ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α R, IsHeckeAt V (pl P) k α → Bridge.IsDC J α⁻¹ R →
      heckeOn M R x = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) • x := by
  simp only [hPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]
  exact ⟨fun h P hP k hk α R ha hR => h P hP k hk α ha R hR, fun h P hP k hk α ha R hR => h P hP k hk α R ha hR⟩

theorem exists_conjModel {S' : D.what₂.Tau → SPar} (h : ∀ τ, S' τ = dualPar (S τ)) (M : DSModel V S) :
    ∃ (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ),
      ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w) := by
  obtain rfl : S' = fun τ => dualPar (S τ) := funext h
  exact GlobalTheory.T.discrete_series_model_of_dual_parameter M

end Hecke

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem rank_zeroth_component_eq : (Yc D 0).rank = D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]
  simp [Ranks.rankY]

theorem rank_weight_component_eq (i : Fin D.R.m) : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2

theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem star_levChi (b : Bool) {κ : GA D (Yc D 0)} (hκ : κ ∈ levS _ (R.βY 0) (R.dat0 (R.levR F b))) :
    levChi _ (R.βY 0) (R.dat0 (R.levL F b D.what₂.embLL)) κ = star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) κ) := by
  have hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) κ) ∈ (R.levR F b).H := hκ.2.2
  have h1 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) κ
  have h2 := levChi_withP (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) κ
  replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
  replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
  refine h1.trans (Eq.trans ?_ (congrArg star h2).symm)
  have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
    exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
  have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
    have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
  rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
  rfl

end GlobalTheory.PartDims

end
