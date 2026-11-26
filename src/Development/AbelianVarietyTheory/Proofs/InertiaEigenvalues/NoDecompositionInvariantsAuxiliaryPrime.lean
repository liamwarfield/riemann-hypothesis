module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElemCyclotomicPeriodNotRootOfUnity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.ScalarInvariants

theorem eq_zero_of_scalar {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (d : O) (hd : d ≠ 1)
    (x : Fin n → FractionRing O)
    (h : ((d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O))).mulVec x = x) : x = 0 := by
  have e : (d • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O (FractionRing O)) =
      algebraMap O (FractionRing O) d • (1 : Matrix (Fin n) (Fin n) (FractionRing O)) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  have h1 : algebraMap O (FractionRing O) d - 1 ≠ 0 := fun h0 =>
    hd (IsFractionRing.injective O (FractionRing O) (by rw [map_one]; exact sub_eq_zero.1 h0))
  have h2 : (algebraMap O (FractionRing O) d - 1) • x = 0 := by rw [sub_smul, h, one_smul, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left h1

theorem inv_unit_smul_one {O : Type} [CommRing O] {n : ℕ} (d : Oˣ) :
    ((d : O) • (1 : Matrix (Fin n) (Fin n) O))⁻¹ = ((d⁻¹ : Oˣ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.inv_mul, one_smul]

theorem noInv_pD : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i,
    NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h v hv
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have hv' : v ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hv
  have hp : (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  have hl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp hlp ?_ hv'
    split_ifs with hh
    · rw [hh]; exact D.host.pde_ne.symm
    · exact fun e => hh e.symm
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k => by
    refine GlobalTheory.TwSys.TameScalar.not_mem_placesOver hp (D.host.g_prime k) ?_ hv'
    split_ifs
    exacts [(D.host.pde_ne_g k).2, (D.host.pde_ne_g k).1]
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ z ∈ Dec (F := D.host.E) A,
      ∃ d : (D.ntw.O0 i)ˣ, d ≠ 1 ∧
        Tmat i s z = (d : D.ntw.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) ∧ eps0 D.ntw i z = 1 := by
    intro A hA
    have h15 := D.ntw.delta_15 i v hv A hA
    obtain ⟨z, hzA, hz⟩ : ∃ z ∈ Ine (F := D.host.E) A, D.ntw.delta i z ≠ 1 := by
      by_contra hc
      push Not at hc
      have hb : (Ine (F := D.host.E) A).map (D.ntw.delta i) = ⊥ :=
        (Subgroup.map_eq_bot_iff _).2 fun z hz => hc z hz
      rw [hb, Subgroup.card_bot] at h15
      exact absurd h15 (by norm_num)
    have h1 : D.ntw.rhoS i s z = 1 := h v hl hg A hA z hzA
    have h2 : chiS i s z = if D.ntw.side i s then D.ntw.delta i z else (D.ntw.delta i z)⁻¹ :=
      D.ntw.twistCharacterFamily_at_auxiliaryPlaces i _ _ v hv A hA z hzA
    refine ⟨z, Ine_le_Dec A hzA, (chiS i s z)⁻¹, ?_, ?_, ?_⟩
    · rw [h2]
      split_ifs
      · exact inv_ne_one.2 hz
      · rw [inv_inv]; exact hz
    · rw [Tmat, h1, Units.val_one]
    · have h4 : cycZ D.host.E D.nd.Om (D.ntw.l i) z = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.1 fun n => ?_)
        rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hzA.2 x hx) n]
        simp
      simp [eps0, h4]
  refine ⟨fun A hA x hx => ?_, fun A hA x hx => ?_⟩
  · obtain ⟨z, hz, d, hd, hT, -⟩ := key A hA
    have e := hx z hz
    rw [hT] at e
    exact eq_zero_of_scalar _ (fun h0 => hd (Units.ext h0)) x e
  · obtain ⟨z, hz, d, hd, hT, he⟩ := key A hA
    have e := hx z hz
    rw [Tdual, hT, he, inv_unit_smul_one, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one] at e
    exact eq_zero_of_scalar _ (fun h0 => inv_ne_one.2 hd (Units.ext h0)) x e

end GlobalTheory.TripleGal.ScalarInvariants
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrimeStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDecompositionInvariants_auxiliaryPrime : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → ∀ v ∈ D.ntw.pD i, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  first | exact @GlobalTheory.TripleGal.ScalarInvariants.noInv_pD | exact GlobalTheory.TripleGal.ScalarInvariants.noInv_pD | (intros; apply GlobalTheory.TripleGal.ScalarInvariants.noInv_pD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletion
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CDelta

variable {l : ℕ} [hl : Fact l.Prime] {L Q : Type} [CommRing L] [CommRing Q] {i : L →+* Q} {J : Ideal L}


omit hl in
theorem smul_top_eq (n : ℕ) : ((J.map i) ^ n • ⊤ : Submodule Q Q) = (J ^ n).map i := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]


omit hl in
theorem eq_of_forall (hc : IsCompl i J) {u v : Q} (h : ∀ n, u - v ∈ (J ^ n).map i) : u = v := by
  refine sub_eq_zero.1 (hc.complete.toIsHausdorff.haus (u - v) fun n => ?_)
  rw [SModEq.sub_mem, sub_zero, smul_top_eq]; exact h n

omit hl in
theorem mem_succ {x : Q} {n : ℕ} (h : x ∈ (J ^ (n + 1)).map i) : x ∈ (J ^ n).map i :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) h

theorem key (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) {x : Q} {a b : L} {n : ℕ}
    (ha : x - i a ∈ (J ^ (n + 1)).map i) (hb : x - i b ∈ (J ^ (n + 1)).map i) :
    i (D.δ a) - i (D.δ b) ∈ (J ^ n).map i := by
  have hab : a - b ∈ J ^ (n + 1) := hc.ker _ _ (by
    have := sub_mem hb ha
    rw [map_sub]; convert this using 1; ring)
  have h := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l L D J hlJ n b (a - b) hab
  rw [add_sub_cancel] at h
  rw [← map_sub]; exact Ideal.mem_map_of_mem _ h

theorem exists_lim (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) (x : Q) :
    ∃ z : Q, ∀ (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i → z - i (D.δ a) ∈ (J ^ n).map i := by
  choose ap hap using hc.surj x
  obtain ⟨z, hz⟩ := hc.complete.toIsPrecomplete.prec (f := fun n => i (D.δ (ap (n + 1)))) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_top_eq]
    exact key hc hlJ D (hap (m + 1)) (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hap (n + 1)))
  refine ⟨z, fun n a ha => ?_⟩
  have h1 := hz n
  rw [SModEq.sub_mem, smul_top_eq] at h1
  have h2 := key hc hlJ D (hap (n + 1)) ha
  have := sub_mem h2 h1
  convert this using 1; ring

end GlobalTheory.BSP.CDelta


open GlobalTheory.BSP.CDelta in
theorem GlobalTheory.BSP.exists_delta_completion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  intro l _ L _ Q _ i J hc hlJ D
  choose d hd using exists_lim hc hlJ D
  have sep : ∀ u v : W2 l Q, (∀ n, W2.map (Ideal.Quotient.mk ((J ^ n).map i)) u =
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) v) → u = v := by
    intro u v h
    have h1 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.fst = Ideal.Quotient.mk ((J ^ n).map i) v.fst :=
      fun n => congrArg W2.fst (h n)
    have h2 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.snd = Ideal.Quotient.mk ((J ^ n).map i) v.snd :=
      fun n => congrArg W2.snd (h n)
    exact W2.ext (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h1 n))
      (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h2 n))
  have ap : ∀ (x : Q) (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i →
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) (⟨x, d x⟩ : W2 l Q) =
        W2.map ((Ideal.Quotient.mk ((J ^ n).map i)).comp i) (deltaSectionToWittLengthTwo D a) := by
    intro x n a ha
    have h1 : Ideal.Quotient.mk ((J ^ n).map i) x = Ideal.Quotient.mk ((J ^ n).map i) (i a) :=
      Ideal.Quotient.eq.2 (mem_succ ha)
    have h2 : Ideal.Quotient.mk ((J ^ n).map i) (d x) = Ideal.Quotient.mk ((J ^ n).map i) (i (D.δ a)) :=
      Ideal.Quotient.eq.2 (hd x n a ha)
    exact W2.ext h1 h2
  let s : Q →+* W2 l Q :=
    { toFun := fun x => ⟨x, d x⟩
      map_one' := sep _ _ fun n => by
        rw [ap 1 n 1 (by simp), map_one, map_one, map_one]
      map_zero' := sep _ _ fun n => by
        rw [ap 0 n 0 (by simp), map_zero, map_zero, map_zero]
      map_add' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x + y - i (a + b) ∈ (J ^ (n + 1)).map i := by
          rw [map_add (f := _)]; convert add_mem ha hb using 1; ring
        show W2.map _ (⟨x + y, d (x + y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) + ⟨y, d y⟩)
        rw [ap _ n _ hab, map_add (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_add (deltaSectionToWittLengthTwo D),
          map_add]
      map_mul' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x * y - i (a * b) ∈ (J ^ (n + 1)).map i := by
          have : x * y - i (a * b) = y * (x - i a) + i a * (y - i b) := by rw [map_mul]; ring
          rw [this]; exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
        show W2.map _ (⟨x * y, d (x * y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) * ⟨y, d y⟩)
        rw [ap _ n _ hab, map_mul (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_mul (deltaSectionToWittLengthTwo D),
          map_mul] }
  refine ⟨deltaStructureOfWittLengthTwoSection s fun _ => rfl, fun a => ?_⟩
  show i (D.δ a) = d (i a)
  exact (eq_of_forall hc fun n => hd (i a) n a (by simp)).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureAdicCompletionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaRingStructure_adicCompletion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  first | exact @GlobalTheory.BSP.exists_delta_completion | exact GlobalTheory.BSP.exists_delta_completion | (intros; apply GlobalTheory.BSP.exists_delta_completion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal TensorProduct

noncomputable section
namespace GlobalTheory.ConsCompare

theorem autCongr_continuous_cyc_inertia : ∀ (E Ω Ω₁ : Type) [Field E] [NumberField E] [Field Ω] [Field Ω₁] [Algebra E Ω] [Algebra E Ω₁] [IsAlgClosure E Ω] [IsAlgClosure E Ω₁] (σ : Ω ≃ₐ[E] Ω₁), Continuous (fun g : G E Ω => (AlgEquiv.autCongr σ g : G E Ω₁)) ∧ (∀ (p : ℕ) [Fact p.Prime] (g : G E Ω), cycZ E Ω₁ p (AlgEquiv.autCongr σ g) = cycZ E Ω p g) ∧ ∀ (A : ValuationSubring Ω) (A₁ : ValuationSubring Ω₁), (∀ y, σ y ∈ A₁ ↔ y ∈ A) → ∀ g : G E Ω, g ∈ Ine (F := E) A → (AlgEquiv.autCongr σ g : G E Ω₁) ∈ Ine (F := E) A₁ := by
  intro E Ω Ω₁ _ _ _ _ _ _ _ _ σ
  refine ⟨?_, fun p _ g => ?_, fun A A₁ hA g hg => ?_⟩
  · apply continuous_of_continuousAt_one (AlgEquiv.autCongr σ).toMonoidHom
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨F, hF, hs⟩ := hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    refine ⟨F.map σ.symm.toAlgHom,
      (IntermediateField.equivMap F σ.symm.toAlgHom).toLinearEquiv.finiteDimensional, fun g hg => hs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
    intro x hx
    have := hg (σ.symm x) ⟨x, hx, rfl⟩
    show σ (g (σ.symm x)) = x
    rw [this, σ.apply_symm_apply]
  · have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    have : IsAlgClosed Ω₁ := IsAlgClosure.isAlgClosed E
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have : CharZero Ω₁ := charZero_of_injective_algebraMap (algebraMap E Ω₁).injective
    have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    have : NeZero ((p : ℕ) : Ω₁) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    apply Units.ext
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ n)
    have hζ' : IsPrimitiveRoot (σ ζ) (p ^ n) := hζ.map_of_injective σ.injective
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ E Ω p g : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G E Ω) Ω g) ζ hζ.pow_eq_one
    have h2 : σ (g (σ.symm (σ ζ))) = σ ζ ^ (PadicInt.toZModPow n
        ((cycZ E Ω₁ p (AlgEquiv.autCongr σ g) : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω₁) p
        (MulSemiringAction.toRingAut (G E Ω₁) Ω₁ (AlgEquiv.autCongr σ g)) (σ ζ) hζ'.pow_eq_one
    rw [σ.symm_apply_apply, h1, map_pow] at h2
    apply ZMod.val_injective
    exact (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2).symm
  · have hv : ∀ y, A₁.valuation (σ y) < 1 ↔ A.valuation y < 1 := fun y => by
      rw [valuation_lt_one_iff', valuation_lt_one_iff', hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]
    refine ⟨?_, fun x hx => ?_⟩
    · show AlgEquiv.autCongr σ g ∈ Dec (F := E) A₁
      rw [mem_Dec]
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      obtain ⟨z, rfl⟩ := σ.surjective y
      have : (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G E Ω) z) := by
        rw [← map_inv]
        show σ ((g⁻¹ : G E Ω) (σ.symm (σ z))) = _
        rw [σ.symm_apply_apply]
      rw [this, hA, hA]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hg.1) z
    · obtain ⟨z, rfl⟩ := σ.surjective x
      have : (AlgEquiv.autCongr σ g) (σ z) - σ z = σ (g z - z) := by
        rw [map_sub]
        show σ (g (σ.symm (σ z))) - _ = _
        rw [σ.symm_apply_apply]
      rw [this, hv]
      apply hg.2
      rwa [ValuationSubring.valuation_le_one_iff, hA, ← ValuationSubring.valuation_le_one_iff] at hx

section CharpolySeries
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cpOn (k : Type) [Field k] [Algebra k A] (a : A) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] : Polynomial k :=
  LinearMap.charpoly (Algebra.lsmul k k M a)

variable (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
  [FiniteDimensional k M']

theorem cpOn_congr (e : M ≃ₗ[A] M') : cpOn k a M = cpOn k a M' := by
  unfold cpOn
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply]

instance finiteDimensional_sub (N : Submodule A M) : FiniteDimensional k N :=
  inferInstanceAs (FiniteDimensional k (N.restrictScalars k))

theorem cpOn_sub_quot (N : Submodule A M) : cpOn k a M = cpOn k a N * cpOn k a (M ⧸ N) :=
  GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (N.restrictScalars k) (Algebra.lsmul k k M a)
    fun _ hx => N.smul_mem a hx

theorem last_eq_mul_prod {P : Type} [CommMonoid P] : ∀ (n : ℕ) (u : Fin (n + 1) → P) (c : Fin n → P),
    (∀ j, u j.succ = u j.castSucc * c j) → u (Fin.last n) = u 0 * ∏ j, c j
  | 0, u, c, _ => by simp
  | n + 1, u, c, h => by
    have := last_eq_mul_prod n (fun j => u j.castSucc) (fun j => c j.castSucc) fun j => h j.castSucc
    rw [Fin.prod_univ_castSucc, ← Fin.succ_last, h, this, mul_assoc]
    rfl

theorem cpOn_series (s : CompositionSeries (Submodule A M)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    cpOn k a M = ∏ j : Fin s.length,
      cpOn k a (↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) := by
  have := last_eq_mul_prod s.length (fun j => cpOn k a (s j)) _ fun j =>
    (cpOn_sub_quot a ((s j.castSucc).submoduleOf (s j.succ))).trans (congrArg (· * _)
      (cpOn_congr a (Submodule.submoduleOfEquivOfLe (s.step j).le)))
  have e1 : cpOn k a (s (Fin.last _)) = cpOn k a M :=
    cpOn_congr a (LinearEquiv.ofTop _ h1)
  have e0 : cpOn k a (s 0) = 1 := by
    have : Subsingleton (s 0) := by
      have h0' : s 0 = ⊥ := h0
      rw [h0']
      infer_instance
    unfold cpOn
    rw [← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  rw [← e1, this, e0, one_mul]

end CharpolySeries

end GlobalTheory.ConsCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPolyEqZeroOfDiscDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPolyEqZeroOfDiscDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DiscRem

theorem norm_add_le_max' (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (x y : Disc l u ρ) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add (f := _), norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

theorem norm_toDisc_l_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖toDisc l u ρ (l : A)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  exact (norm_ofPre l u ρ _).trans_le (gauge_le l u ρ (by positivity)
    (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], by simp⟩))

theorem coeff_mul_disc (l : ℕ) {R : Type} [CommRing R] (ρ : ℝ≥0)
    (a : ℕ → (Disc l (X : R⟦X⟧) ρ →+ Disc l (0 : R) 1))
    (h1 : ∀ n x, a n (toDisc l (X : R⟦X⟧) ρ x) = toDisc l (0 : R) 1 (coeff n x))
    (hc : ∀ n, Continuous (a n)) (s : R⟦X⟧) (n : ℕ) (y : Disc l (X : R⟦X⟧) ρ) :
    a n (toDisc l (X : R⟦X⟧) ρ s * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, toDisc l (0 : R) 1 (coeff p.1 s) * a p.2 y := by
  refine (denseRange_ofPre l (X : R⟦X⟧) ρ).induction_on y
    (isClosed_eq ((hc n).comp (continuous_const.mul continuous_id))
      (continuous_finsetSum _ fun p _ => continuous_const.mul (hc p.2))) fun z => ?_
  obtain ⟨k, b, h⟩ := IsLocalization.Away.surj (l : R⟦X⟧) z
  have h' : (l ^ k : ℕ) • ofPre l (X : R⟦X⟧) ρ z = toDisc l (X : R⟦X⟧) ρ b := by
    have := congrArg (ofPre l (X : R⟦X⟧) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at this
    rw [nsmul_eq_mul, Nat.cast_pow, mul_comm]
    exact this
  refine ((isUnit_l_disc l (0 : R) 1).pow k).mul_left_cancel ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Nat.cast_pow, ← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← mul_smul_comm, h', ← map_mul, h1,
    coeff_mul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← mul_smul_comm, ← map_nsmul, h', h1, map_mul]

theorem rho_zero {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) :
    0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
  have he : (0 : ℝ) < bk.Ep.natDegree := Nat.cast_pos.2 bk.deg_pos
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith), ?_⟩
  rw [BK.ρ₀, NNReal.coe_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), neg_mul,
    one_div_mul_cancel he.ne', Real.rpow_neg_one, NNReal.coe_natCast]

theorem eq_zero_of_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (r : Polynomial (Wq l bk.a)),
    r.degree < bk.Ep.degree →
    toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) → r = 0 := by
  intro l hl K bk r hr ⟨y, hy⟩
  obtain ⟨h0, h1, hpow⟩ := rho_zero bk
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk bk.ρ₀ h0 h1
  obtain ⟨-, -, hinj, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have h1' : (bk.ρ₀ : ℝ) < 1 := h1
  have hc : ∀ n, Continuous (a n) := fun n =>
    AddMonoidHomClass.continuous_of_bound _ ((bk.ρ₀ : ℝ) ^ n)⁻¹ fun z => by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact ha2 n z
  have hy0 : y = 0 := by
    refine norm_le_zero_iff.1 (ha3 y 0 le_rfl fun m₀ => ?_)
    by_contra hneg
    push Not at hneg
    set c := ‖a m₀ y‖ * (bk.ρ₀ : ℝ) ^ m₀ with hcdef
    have hfin : {n | c ≤ ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n}.Finite := by
      have := (ha4 y).eventually (gt_mem_nhds hneg)
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at this
      simpa only [not_lt] using this
    obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal ⟨m₀, le_refl c⟩
    have hlt : ∀ n, m < n → ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n < c := fun n hn => by
      by_contra h
      exact (hmax (not_lt.1 h) hn.le).not_gt hn
    have key := coeff_mul_disc l bk.ρ₀ a ha1 hc bk.E (bk.Ep.natDegree + m) y
    have hz : coeff (bk.Ep.natDegree + m) (r : bk.S) = 0 := by
      rw [Polynomial.coeff_coe]
      refine Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le ?_)
      rw [Polynomial.degree_eq_natDegree bk.monic.ne_zero]
      exact_mod_cast Nat.le_add_right _ _
    rw [← hy, ha1, hz, map_zero, ← Finset.add_sum_erase _ _
      (show (bk.Ep.natDegree, m) ∈ Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m) by simp)] at key
    have hlead : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [Polynomial.coeff_coe]; exact bk.monic
    simp only [hlead, map_one, one_mul] at key
    have hsum : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m)).erase (bk.Ep.natDegree, m),
        toDisc l (0 : Wq l bk.a) 1 (coeff p.1 bk.E) * a p.2 y‖ * (bk.ρ₀ : ℝ) ^ m < c := by
      refine Finset.sum_induction _ (fun x => ‖x‖ * (bk.ρ₀ : ℝ) ^ m < c) (fun x z hx hz => ?_)
        (by simpa using hneg) fun p hp => ?_
      · refine (mul_le_mul_of_nonneg_right (norm_add_le_max' l _ _ x z) (by positivity)).trans_lt ?_
        rcases max_cases ‖x‖ ‖z‖ with h | h <;> rw [h.1] <;> assumption
      · obtain ⟨i, j⟩ := p
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
        rw [Polynomial.coeff_coe]
        rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
        · obtain ⟨w, hw⟩ := bk.dvd_coeff i h
          have hn : ‖toDisc l (0 : Wq l bk.a) 1 (bk.Ep.coeff i)‖ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := by
            rw [hw, map_mul, hpow]
            exact (norm_mul_le _ _).trans ((mul_le_mul (norm_toDisc_l_le l _ _) (norm_toDisc_le _)
              (norm_nonneg _) (by positivity)).trans (mul_one _).le)
          refine lt_of_le_of_lt ?_ (hlt j (by omega))
          have hp2 : (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) ≤ (bk.ρ₀ : ℝ) ^ j :=
            pow_le_pow_of_le_one h0'.le h1'.le (by omega)
          calc _ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree * ‖a j y‖ * (bk.ρ₀ : ℝ) ^ m :=
                mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) (by positivity)
            _ = ‖a j y‖ * (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (norm_nonneg _)
        · exact (hp.1 ⟨h, by omega⟩).elim
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
          simpa using hneg
    rw [eq_neg_of_add_eq_zero_right key.symm, norm_neg] at hsum
    exact hsum.not_ge hm
  apply Polynomial.ext
  intro n
  apply hinj
  have := ha1 n (r : bk.S)
  rw [hy, hy0, mul_zero, map_zero, Polynomial.coeff_coe] at this
  rw [← this, Polynomial.coeff_zero, map_zero]

end GlobalTheory.BSP.DiscRem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPolyEqZeroOfDiscDvdStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_poly_eq_zero_of_disc_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (r : Polynomial (Wq l bk.a)), r.degree < bk.Ep.degree → toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) → r = 0 := by
  first | exact @GlobalTheory.BSP.DiscRem.eq_zero_of_dvd | exact GlobalTheory.BSP.DiscRem.eq_zero_of_dvd | (intros; apply GlobalTheory.BSP.DiscRem.eq_zero_of_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieConclusion
section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SelmerSumLargePrime
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Exceptional

variable {D : D7} (L : SizeData₂ D)

end Exceptional

section Terms

variable (D : D7) (i : D.nd.Loc)

def ramLen : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def ccLen (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)

def selLen (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (π : D.nd.X i) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i (fun _ => ρ) π)

def shaSum : ℕ∞ :=
  ∑ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def zetaP (P : HeightOneSpectrum (𝓞 D.host.E)) : D.nd.O i :=
  ((D.ntw.psiL i (D.nd.gam0 i P) : (D.nd.O i)ˣ) : D.nd.O i)

def twistLen : ℕ∞ :=
  (D.R.t : ℕ∞) * ∑ P ∈ D.nd.Q i,
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {zetaP D i P - 1})

end Terms

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerSumLargePrime

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.Proof.QuotientLengthInfimum

open GlobalTheory.IndefiniteRowSideFullHecke

theorem length_quot_eq_iInf {O : Type} [CommRing O] [IsPrincipalIdealRing O] (I : Ideal O) :
    Module.length O (O ⧸ I) = ⨅ x ∈ I, Module.length O (O ⧸ Ideal.span {x}) := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem _).2 hx
    exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
      Ideal.span_singleton_generator I
    refine iInf₂_le_of_le (Submodule.IsPrincipal.generator I)
      (Submodule.IsPrincipal.generator_mem I) ?_
    rw [hg]

theorem mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X) (y : O) :
    y ∈ ccAt T Z π ↔ ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = y := by
  have hs : Function.Surjective ((Pi.evalRingHom (fun _ : X => O) π).comp T.val.toRingHom) :=
    fun a => ⟨algebraMap O T a, by simp⟩
  unfold ccAt
  rw [Ideal.mem_map_iff_of_surjective _ hs]
  rfl

theorem div_le_iff_lengths (e c s h v q : ℕ∞) (he0 : e ≠ 0) (he : e ≠ ⊤) :
    ((c : ℝ≥0∞) / (e : ℝ≥0∞) ≤ (s : ℝ≥0∞) / (e : ℝ≥0∞) + (h : ℝ≥0∞) + (v : ℝ≥0∞) + (q : ℝ≥0∞) / (e : ℝ≥0∞)) ↔
      c ≤ s + e * h + e * v + q := by
  have he0' : (e : ℝ≥0∞) ≠ 0 := by simpa using he0
  have he' : (e : ℝ≥0∞) ≠ ⊤ := by simpa using he
  rw [← ENat.toENNReal_le, ← ENNReal.mul_le_mul_iff_right he0' he']
  simp only [mul_add, ENNReal.mul_div_cancel he0' he', ENat.toENNReal_add, ENat.toENNReal_mul]

theorem toENNReal_sum {ι : Type} (s : Finset ι) (f : ι → ℕ∞) :
    ((∑ a ∈ s, f a : ℕ∞) : ℝ≥0∞) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ENat.toENNRealRingHom f s

section Hyp

end Hyp

section Terms

variable (D : D7) (i : D.nd.Loc)

theorem ramLen_ne : SelmerSumLargePrime.ramLen D i ≠ 0 ∧ SelmerSumLargePrime.ramLen D i ≠ ⊤ := by
  have h := BaseSizes.vO_l D i
  unfold BaseSizes.vO BaseSizes.nlen at h
  change ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) / ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) = 1 at h
  constructor
  · intro h0; rw [h0] at h; simp at h
  · intro h0; rw [h0] at h; simp at h

theorem vCC_eq (π : D.nd.X i) :
    BaseSizes.vCC D i π = (SelmerSumLargePrime.ccLen D i π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.vCC BaseSizes.vO BaseSizes.nlen SelmerSumLargePrime.ccLen
  change ⨅ f ∈ D.nd.cc i, _ / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) = _
  apply le_antisymm
  · set I := ccAt (D.nd.T i) (D.nd.Z i) π with hI
    have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I := Ideal.span_singleton_generator I
    obtain ⟨f, hf, hfx⟩ := (mem_ccAt _ _ π _).1 (Submodule.IsPrincipal.generator_mem I)
    refine iInf₂_le_of_le f hf ?_
    rw [hfx, hg]
  · refine le_iInf₂ fun f hf => ?_
    refine ENNReal.div_le_div_right ?_ _
    rw [ENat.toENNReal_le, length_quot_eq_iInf]
    exact iInf₂_le _ ((mem_ccAt _ _ π _).2 ⟨f, hf, rfl⟩)

theorem sPi_eq (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    BaseSizes.sPi D i π ρ = (SelmerSumLargePrime.selLen D i ρ π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := rfl

theorem shaSum_eq : BaseSizes.shaSum D i = (SelmerSumLargePrime.shaSum D i : ℝ≥0∞) := by
  unfold BaseSizes.shaSum SelmerSumLargePrime.shaSum
  rw [toENNReal_sum]

theorem vClass_eq :
    BaseSizes.vClass D i = (((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) : ℝ≥0∞) := by
  unfold BaseSizes.vClass hE
  simp

theorem zetaP_eq (P : HeightOneSpectrum (𝓞 D.host.E)) : BaseSizes.zetaP D i P = SelmerSumLargePrime.zetaP D i P := rfl

theorem epsQ_eq : BaseSizes.epsQ D i = (SelmerSumLargePrime.twistLen D i : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.epsQ SelmerSumLargePrime.twistLen BaseSizes.vO BaseSizes.nlen
  rw [ENat.toENNReal_mul, toENNReal_sum, mul_div_assoc, div_eq_mul_inv (∑ _ ∈ _, _), Finset.sum_mul]
  rfl

theorem conclusion_iff (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    (BaseSizes.vCC D i π ≤ BaseSizes.sPi D i π ρ + BaseSizes.shaSum D i + BaseSizes.vClass D i + BaseSizes.epsQ D i) ↔
      SelmerSumLargePrime.ccLen D i π ≤ SelmerSumLargePrime.selLen D i ρ π + SelmerSumLargePrime.ramLen D i * SelmerSumLargePrime.shaSum D i +
        SelmerSumLargePrime.ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + SelmerSumLargePrime.twistLen D i := by
  rw [vCC_eq, sPi_eq, shaSum_eq, vClass_eq, epsQ_eq]
  exact div_le_iff_lengths _ _ _ _ _ _ (ramLen_ne D i).1 (ramLen_ne D i).2

end Terms

end GlobalTheory.Proof.QuotientLengthInfimum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaUniq

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem σO_intToOC (g : ↥(GK K)) (c : ↥(OL K)) : Per.σO (g : GQ l) (intToOC K c) = intToOC K c :=
  Subtype.ext ((GlobalTheory.RingIface.sigO_coe l (g : GQ l) (intToOC K c)).trans
    ((GlobalTheory.RingBasics.σC_coe (g : GQ l) _).trans (congrArg _
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (c : ↥K.1).2))))

theorem theta_gal_ev (g : ↥(GK K)) (s : bk.S) :
    Per.θ l (Per.σA (g : GQ l) (bk.ev s)) = Per.θ l (bk.ev s) := by
  rw [GlobalTheory.RingBasics.θ_σA, bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s)) s (bk.str.apply_symm_apply _).symm,
    σO_intToOC]

theorem theta_eq_zero_iff (a : Ainf l) : Per.θ l a = 0 ↔ bk.ev bk.E ∣ a := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  GlobalTheory.BSP.AinfDiv.cc_E_ne bk (by rw [h, map_zero])

theorem l_ne_zero_OC : ((l : ℕ) : OC l) ≠ 0 := fun h =>
  GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)

end GlobalTheory.BKLim.BetaUniq

noncomputable section

namespace GlobalTheory.BKLim.BetaUniq

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem step {d : ℕ} (g : ↥(GK K)) (w : Ainf l)
    (hw : Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w)
    (hwi : ∀ i : ℕ, 1 ≤ i → Per.θ l w ^ i ≠ 1)
    (P : Fin d → Fin d → Ainf l) (hP : ∀ a c, Per.θ l (P a c) = if a = c then 1 else 0)
    (m i : ℕ) (hi : 1 ≤ i) (him : i < m) (δ : Fin d → Fin d → bk.S)
    (hδ : ∀ a b, bk.ev bk.E ^ m ∣ ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b))
    (hdiv : ∀ a b, bk.E ^ i ∣ δ a b) : ∀ a b, bk.E ^ (i + 1) ∣ δ a b := by
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  choose δ' hδ' using hdiv
  intro a b
  have hX : ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b) =
      bk.ev bk.E ^ i * (w ^ i * ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ' c b)) - bk.ev (δ' a b)) := by
    simp only [hδ', map_mul, map_pow, hw, mul_pow, Finset.mul_sum]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      ring
  have h1 : bk.ev bk.E ∣ w ^ i * ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ' c b)) - bk.ev (δ' a b) := by
    have h2 := hδ a b
    rw [hX, show m = i + (m - i) by omega, pow_add] at h2
    have h3 := (mul_dvd_mul_iff_left (pow_ne_zero i (evE_ne_zero bk))).1 h2
    exact (dvd_pow_self (bk.ev bk.E) (by omega)).trans h3
  rw [← theta_eq_zero_iff] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_mul, map_pow, map_sum, theta_gal_ev, hP, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have h4 : Per.θ l (bk.ev (δ' a b)) = 0 := by
    have h5 : (Per.θ l w ^ i - 1) * Per.θ l (bk.ev (δ' a b)) = 0 := by
      rw [sub_mul, one_mul]; exact h1
    exact (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 (hwi i hi))
  rw [theta_eq_zero_iff] at h4
  have h6 := (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk 1).2.1 (δ' a b) (by rwa [pow_one])
  rw [hδ' a b, pow_succ]
  exact mul_dvd_mul_left _ (by rwa [pow_one] at h6)

end GlobalTheory.BKLim.BetaUniq

theorem GlobalTheory.BKLim.beta_unique : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k k' : ℕ) (β β' : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → F.IsBeta m k' β' → ∀ i j, bk.E ^ m ∣ ((l : bk.S) ^ k' • β - (l : bk.S) ^ k • β') i j := by
  intro l _ K bk m N d ρ F k k' β β' hβ hβ'
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro i j; simp
  obtain ⟨g, z, ⟨w, hw, hz⟩, hzi⟩ := GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity l K bk
  have hwi : ∀ i : ℕ, 1 ≤ i → Per.θ l w ^ i ≠ 1 := by
    intro i hi h
    have h1 : Per.θD l (aDp l w) = (Per.θ l w : ℂ_[l]) := (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1 w
    apply hzi i hi
    have h2 : ((Per.θ l w : ℂ_[l])) ^ i = 1 := by exact_mod_cast congrArg Subtype.val h
    calc z ^ i = z ^ i * (Per.θ l w : ℂ_[l]) ^ i := by rw [h2, mul_one]
      _ = (z * Per.θD l (aDp l w)) ^ i := by rw [h1, mul_pow]
      _ = 1 := by rw [hz, one_pow]
  set P : Fin d → Fin d → Ainf l := fun a c => WittVector.frobenius (F.ε g a c) with hPdef
  have hent : ∀ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ a b,
      bk.ev bk.E ^ m ∣ ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (β c b)) - bk.ev (β a b) := by
    intro k β h a b
    have := h.2 g a b
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, hPdef] using this
  have hθβ : ∀ c b, Per.θ l (bk.ev (β c b)) = (l : OC l) ^ k * (if c = b then 1 else 0) := by
    intro c b
    have h2 : Per.θ l (bk.ev ((β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) c b)) = 0 :=
      (BetaUniq.theta_eq_zero_iff bk _).2 (map_dvd bk.ev (hβ.1 c b))
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub, map_mul, map_pow,
      map_natCast] at h2
    rw [sub_eq_zero] at h2
    rw [h2]; split_ifs <;> simp
  have hP : ∀ a c, Per.θ l (P a c) = if a = c then 1 else 0 := by
    intro a b
    have h := (BetaUniq.theta_eq_zero_iff bk _).2 ((dvd_pow_self _ hm.ne').trans (hent k β hβ a b))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, BetaUniq.theta_gal_ev, hθβ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [sub_eq_zero] at h
    have hl := pow_ne_zero k (BetaUniq.l_ne_zero_OC (l := l))
    apply mul_right_cancel₀ hl
    rw [h]; split_ifs <;> simp
  set δ : Fin d → Fin d → bk.S := fun a b => (l : bk.S) ^ k' * β a b - (l : bk.S) ^ k * β' a b with hδdef
  have hδ : ∀ a b, bk.ev bk.E ^ m ∣ ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b) := by
    intro a b
    have e1 : ∀ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) =
        (l : Ainf l) ^ k' * (P a c * Per.σA (g : GQ l) (bk.ev (β c b))) -
          (l : Ainf l) ^ k * (P a c * Per.σA (g : GQ l) (bk.ev (β' c b))) := by
      intro c; simp only [hδdef, map_sub, map_mul, map_pow, map_natCast]; ring
    have e : ∑ c, P a c * Per.σA (g : GQ l) (bk.ev (δ c b)) - bk.ev (δ a b) =
        (l : Ainf l) ^ k' * (∑ c, P a c * Per.σA (g : GQ l) (bk.ev (β c b)) - bk.ev (β a b)) -
          (l : Ainf l) ^ k * (∑ c, P a c * Per.σA (g : GQ l) (bk.ev (β' c b)) - bk.ev (β' a b)) := by
      rw [Finset.sum_congr rfl (fun c _ => e1 c), Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [hδdef, map_sub, map_mul, map_pow, map_natCast]; ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right (hent k β hβ a b) _) (dvd_mul_of_dvd_right (hent k' β' hβ' a b) _)
  have hbase : ∀ a b, bk.E ∣ δ a b := by
    intro a b
    have h1 := hβ.1 a b
    have h2 := hβ'.1 a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
    have e : δ a b = (l : bk.S) ^ k' * (β a b - (l : bk.S) ^ k * (1 : Matrix (Fin d) (Fin d) bk.S) a b) -
        (l : bk.S) ^ k * (β' a b - (l : bk.S) ^ k' * (1 : Matrix (Fin d) (Fin d) bk.S) a b) := by
      simp only [hδdef]; ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  have hall : ∀ i, 1 ≤ i → i ≤ m → ∀ a b, bk.E ^ i ∣ δ a b := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _ a b; rw [pow_one]; exact hbase a b
    | succ n hn ih =>
      intro hnm
      exact BetaUniq.step bk g w hw hwi P hP m n hn (by omega) δ hδ (ih (by omega))
  intro i j
  have := hall m hm le_rfl i j
  simpa [hδdef, Matrix.sub_apply, Matrix.smul_apply] using this
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k k' : ℕ) (β β' : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → F.IsBeta m k' β' → ∀ i j, bk.E ^ m ∣ ((l : bk.S) ^ k' • β - (l : bk.S) ^ k • β') i j := by
  first | exact @GlobalTheory.BKLim.beta_unique | exact GlobalTheory.BKLim.beta_unique | (intros; apply GlobalTheory.BKLim.beta_unique <;> assumption)
end
end
