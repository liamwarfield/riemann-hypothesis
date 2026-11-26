module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsLiftBaseLevelExtensionSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeA
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBaseLatticeEqSpanImages
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanImageSpan
open NumberField

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

theorem relSet_eq {n : ℕ} (S : Set (Fin n → K)) :
    {x' : Fin n → K' | ∃ x ∈ S, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = (fun x k => φ (x k)) '' S := by
  ext x'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩; exact ⟨x, hx, funext fun k => (h k k rfl).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, fun k k' hk => by rw [Fin.ext hk]⟩

theorem span_image_span {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun x k => φ (x k)) '' (Submodule.span (𝓞 K) S : Set (Fin n → K))) =
      Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [SetLike.mem_coe]
      convert Submodule.zero_mem (Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' S)) using 1
      funext k; simp
    | add y z _ _ hy hz =>
      rw [SetLike.mem_coe] at hy hz ⊢
      convert Submodule.add_mem _ hy hz using 1; funext k; simp
    | smul a y _ hy =>
      rw [SetLike.mem_coe] at hy ⊢
      convert Submodule.smul_mem _ (RingOfIntegers.mapRingHom φ a) hy using 1
      funext k
      simp [Pi.smul_apply, Algebra.smul_def, map_mul]
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem span_image_inf {n : ℕ} (X : Submodule (𝓞 K) (Fin n → K)) (V : Submodule K (Fin n → K)) :
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) '' (X : Set (Fin n → K))) ⊓
      (Submodule.span K' ((fun (x : Fin n → K) k => φ (x k)) '' (V : Set (Fin n → K)))).restrictScalars (𝓞 K') =
    Submodule.span (𝓞 K') ((fun (x : Fin n → K) k => φ (x k)) ''
      ((X ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  classical
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  set ψ : 𝓞 K →+* 𝓞 K' := RingOfIntegers.mapRingHom φ with hψdef
  have hψ : ∀ a : 𝓞 K, ((ψ a : 𝓞 K') : K') = φ (a : K) := fun a => rfl
  apply le_antisymm
  · rintro y ⟨hyX, hyV⟩

    let bQ := Module.finBasis K ((Fin n → K) ⧸ V)
    let ℓ : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → (Fin n → K) →ₗ[K] K := fun r => (bQ.coord r).comp V.mkQ
    have hℓV : ∀ x, x ∈ V ↔ ∀ r, ℓ r x = 0 := by
      intro x
      constructor
      · intro hx r
        simp [ℓ, (Submodule.Quotient.mk_eq_zero V).2 hx]
      · intro h
        have : V.mkQ x = 0 := bQ.ext_elem fun r => by simpa [ℓ] using h r
        exact (Submodule.Quotient.mk_eq_zero V).1 this
    let q : Fin (Module.finrank K ((Fin n → K) ⧸ V)) → Fin n → K := fun r k => ℓ r (Pi.single k 1)
    have hℓ : ∀ r x, ℓ r x = ∑ k, q r k * x k := by
      intro r x
      rw [LinearMap.pi_apply_eq_sum_univ (ℓ r) x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hyℓ : ∀ r, ∑ k, φ (q r k) * y k = 0 := by
      intro r
      have key : ∀ z ∈ Submodule.span K' (Φ '' V), ∑ k, φ (q r k) * z k = 0 := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨x, hx, rfl⟩ := hw
          have h0 := (hℓV x).1 hx r
          rw [hℓ] at h0
          have := congrArg φ h0
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, map_zero] at this
          rw [← this]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
        | zero => simp
        | add a b _ _ ha hb => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
        | smul a b _ hb =>
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [show ∑ k, φ (q r k) * (a * b k) = a * ∑ k, φ (q r k) * b k by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring, hb, mul_zero]
      exact key y hyV
    obtain ⟨m, r0, g, hg⟩ := Submodule.mem_span_set'.1 hyX
    choose x hxX hx using fun i => (g i).2
    have hy : ∀ k, y k = ∑ i, (r0 i : K') * φ (x i k) := by
      intro k
      rw [← hg, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def, ← hx i]
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
      (fun z : Fin m × Fin (Module.finrank K ((Fin n → K) ⧸ V)) => ℓ z.2 (x z.1))
    choose b hb using hd
    have hd0 : ((d : 𝓞 K) : K) ≠ 0 := by
      have := nonZeroDivisors.coe_ne_zero d
      exact_mod_cast this
    have hb' : ∀ i r, ((b (i, r) : 𝓞 K) : K) = ((d : 𝓞 K) : K) * ℓ r (x i) := fun i r => by
      have := hb (i, r)
      rw [Algebra.smul_def] at this
      exact this
    letI : Algebra (𝓞 K) (𝓞 K') := ψ.toAlgebra
    have hinj : Function.Injective ψ := fun a a' h => by
      have := congrArg (fun z : 𝓞 K' => (z : K')) h
      simp only [hψ] at this
      exact RingOfIntegers.ext (φ.injective this)
    haveI : Module.Flat (𝓞 K) (𝓞 K') := by
      rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
      rintro z ⟨a, ha⟩
      have ha' : ψ a * z = 0 := ha
      rcases mul_eq_zero.1 ha' with h | h
      · exact absurd (hinj (h.trans (map_zero ψ).symm)) (nonZeroDivisors.coe_ne_zero a)
      · exact h
    obtain ⟨N, a, yv, hr, ha⟩ := GlobalTheory.Proof.IdempotentLatticeSequence.flat_system (fun i r => b (i, r)) r0 (fun r => by
      apply RingOfIntegers.ext
      have h1 : ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, φ (b (i, r) : K) * (r0 i : K') := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show ((∑ i, b (i, r) • r0 i : 𝓞 K') : K') = ∑ i, ((b (i, r) • r0 i : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      rw [h1]
      simp only [hb', map_mul]
      have h2 := hyℓ r
      simp only [hy, Finset.mul_sum] at h2
      rw [Finset.sum_comm] at h2
      change _ = (0 : K')
      rw [← mul_zero (φ ((d : 𝓞 K) : K)), ← h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hℓ, map_sum]
      simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring)
    let u : Fin N → Fin n → K := fun l => ∑ i, a i l • x i
    have huX : ∀ l, u l ∈ X := fun l => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hxX i)
    have huV : ∀ l, u l ∈ V := by
      intro l
      rw [hℓV]
      intro r
      have h1 := congrArg (fun z : 𝓞 K => (z : K)) (ha l r)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hb', map_zero] at h1
      apply mul_left_cancel₀ hd0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [mul_zero, ← h1, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smul_of_tower, Algebra.smul_def]
      ring
    have hyu : y = ∑ l, yv l • Φ (u l) := by
      funext k
      rw [hy, Finset.sum_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Pi.smul_apply, hΦ, u, Finset.sum_apply, map_sum, Algebra.smul_def]
      have h2 : ∀ i, ((r0 i : 𝓞 K') : K') = ∑ l, φ (a i l : K) * (yv l : K') := by
        intro i
        rw [hr i]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show ((∑ l, a i l • yv l : 𝓞 K') : K') = ∑ l, ((a i l • yv l : 𝓞 K') : K') from
          map_sum (algebraMap (𝓞 K') K') _ _]
        rfl
      simp only [h2, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
      change _ = (algebraMap (𝓞 K') K' (yv l)) * φ (((a i l) : K) * x i k)
      rw [map_mul]
      change φ (a i l : K) * (yv l : K') * φ (x i k) = (yv l : K') * (φ (a i l : K) * φ (x i k))
      ring
    rw [hyu]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u l, ⟨huX l, huV l⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxV⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, hxX, rfl⟩, Submodule.subset_span ⟨x, hxV, rfl⟩⟩

end GlobalTheory.Mem.R3.LiftForms

namespace GlobalTheory.Mem.R3.LiftForms
variable {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K')

theorem span_rel_inf {n n' : ℕ} (hn : n = n') (S : Set (Fin n → K)) (V : Submodule K (Fin n → K))
    (S' : Set (Fin n' → K')) (V' : Submodule K' (Fin n' → K'))
    (hS : S' = {x' | ∃ x ∈ S, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)})
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    Submodule.span (𝓞 K') S' ⊓ V'.restrictScalars (𝓞 K') =
      Submodule.span (𝓞 K') {x' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
        ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)} := by
  subst hn hS hV
  have e1 : {x' : Fin n → K' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' (V : Set (Fin n → K)) := relSet_eq φ (V : Set (Fin n → K))
  have e2 : {x' : Fin n → K' | ∃ x ∈ Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K),
      ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} =
      (fun x k => φ (x k)) '' ((Submodule.span (𝓞 K) S ⊓ V.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) :
        Set (Fin n → K)) := relSet_eq φ _
  rw [relSet_eq, e1, e2, ← span_image_span φ S]
  exact span_image_inf φ _ V

end GlobalTheory.Mem.R3.LiftForms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBaseLatticeEqSpanImages
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftForms


set_option maxHeartbeats 4000000 in
theorem lift_Mj_base : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        (z'.R.FW j').Mj (z'.F.lv2.lvl false).P (z'.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.X).coeff g) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) {x' | ∃ x ∈ (z.R.FW j).Mj (z.F.lv2.lvl false).P (z.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.X).coeff g), ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro h1 h2 h3 h4 h5 h6 h7
  have hGoodForms := GlobalTheory.Mem.R3.Rw.goodForms_lift_bc h1 h2 h3 h4 h5 h6 h7
  have hSupLattice := GlobalTheory.Mem.R3.MKExt.mk_ext h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ hp => hp)
    (StepW.and hGoodForms hSupLattice)) (StepW.of_all ?_)
  rintro K B' f' T' w' - - ⟨-, H1, H2⟩ B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hW := H1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hK := H2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm e.nW j j' hj
  have key := span_rel_inf φ hn _ _ _ _ hK hW
  refine Eq.trans ?_ (key.trans ?_)
  · ext x
    simp only [Arith.FormsL.Mj, Arith.FormsL.Mall, RealDat.WL, Arith.FormsL.Wgood, Submodule.mem_inf,
      Submodule.restrictScalars_mem, and_assoc]
  · congr 1
    ext x'
    simp only [Set.mem_ofPred_eq, Arith.FormsL.Mj, Arith.FormsL.Mall, RealDat.WL, Arith.FormsL.Wgood, Submodule.mem_inf,
      Submodule.restrictScalars_mem, and_assoc]

end GlobalTheory.Mem.R3.LiftForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBaseLatticeEqSpanImagesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_lift_baseLattice_eq_span_images : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        (z'.R.FW j').Mj (z'.F.lv2.lvl false).P (z'.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.X).coeff g) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) {x' | ∃ x ∈ (z.R.FW j).Mj (z.F.lv2.lvl false).P (z.F.lv2.lvl false).ψ⁻¹ (fun g => (idemOf (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.X).coeff g), ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  first | exact @GlobalTheory.Mem.R3.LiftForms.lift_Mj_base | exact GlobalTheory.Mem.R3.LiftForms.lift_Mj_base | (intros; apply GlobalTheory.Mem.R3.LiftForms.lift_Mj_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeA
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftForms


set_option maxHeartbeats 4000000 in
theorem extendedData_liftFormsLattice_baseLevel_baseChange : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((z'.R.toCx3 z'.F).dW false j')) (Fin ((z.R.toCx3 z.F).dW false j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (z'.R.toCx3 z'.F).M false j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((z.R.toCx3 z.F).M false j : Set (Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ y : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).w0C false j' (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec G fun k => φ (y k)))) ((z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding y))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.of_all fun _ _ _ _ _ _ _ hp => hp)
    (StepW.and (StepW.and (GlobalTheory.T.goodForms_lift_baseLevel_extension_span h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.extendedData_lift_baseLattice_eq_span_images h1 h2 h3 h4 h5 h6 h7)) (GlobalTheory.T.reading_coordinatewiseImage_eq_extendedData h1 h2 h3 h4 h5 h6 h7))) (StepW.of_all ?_)
  rintro K B' f' T' w' - - ⟨-, ⟨H1, H2⟩, H3⟩ B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hW := H1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hM := H2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hJ := H3 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' e j j' hj φ hφ
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := GlobalTheory.Mem.R3.LiftForms.nat_eq_of_heq hm e.nW j j' hj
  obtain ⟨G, hGb, hGid⟩ := GlobalTheory.Mem.R3.LiftForms.exists_mat φ hn _ _ hW
  refine ⟨G, hGb, ?_, ?_⟩
  · exact GlobalTheory.Mem.R3.LiftForms.lat_coords φ hn _ _
      ((Module.finBasis _ _).linearIndependent.map' _ (Submodule.ker_subtype _)) G hGid _
      (fun x hx => GlobalTheory.Mem.R3.LiftForms.mem_span_basis _ ((z.R.FW j).Mj_sub_Wgood _ _ _ hx)) _ hM
  · intro y
    exact HEq.trans (GlobalTheory.Mem.R3.LiftForms.liftWeight_complexPoint_eq_twist z'.R z'.F j' _)
      (HEq.trans (hJ _ _ (hGid y)) (GlobalTheory.Mem.R3.LiftForms.liftWeight_complexPoint_eq_twist z.R z.F j y).symm)

end GlobalTheory.Mem.R3.LiftForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftFormsLatticeBaseLevelBaseChangeAStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendedData_liftFormsLattice_baseLevel_baseChange_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((z'.R.toCx3 z'.F).dW false j')) (Fin ((z.R.toCx3 z.F).dW false j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (z'.R.toCx3 z'.F).M false j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((z.R.toCx3 z.F).M false j : Set (Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ y : Fin ((z.R.toCx3 z.F).dW false j) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).w0C false j' (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec G fun k => φ (y k)))) ((z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding y))) := by
  first | exact @GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange | exact GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange | (intros; apply GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelComplexPointsInjectiveExtendedData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelComplexPointsInjectiveExtendedData
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftInj

section Conc

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem baseLevelComplexPoints_injective_of_independent (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool) (i : Fin D.R.m)
    (hU : ∀ (n : ℕ) (c : Fin n → (Fin (R.nW i) → D.what₂.LL)), LinearIndependent D.what₂.LL c →
      LinearIndependent ℂ fun k => (R.FW i).j (sg0 D A3.A) (c k)) :
    Function.Injective ((R.toCx3 F).w0C b i) := by
  have hb : LinearIndependent D.what₂.LL (R.toRealDat.bL F.lv2 b i) :=
    (Module.finBasis D.what₂.LL (R.toRealDat.WL F.lv2 b i)).linearIndependent.map' (R.toRealDat.WL F.lv2 b i).subtype
      (Submodule.ker_subtype _)
  refine (injective_iff_map_eq_zero _).2 fun c hc => funext fun l => ?_
  have h1 := Fintype.linearIndependent_iff.1 (hU _ _ hb) _ ((Formalism.IndefR.FWT.principal_form_tensor_expansion R F b i c).symm.trans hc) l
  have h2 := congrArg (Links.cj (twAt D.what₂.embLL A3.A.v0)) h1
  rwa [cj_cj, map_zero] at h2

end Conc


set_option maxHeartbeats 1000000 in
theorem baseLevelComplexPoints_injective_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        Function.Injective ((z'.R.toCx3 z'.F).w0C false j')) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w _ _ _ _ Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' hF _ _ j' _ _ _
  exact baseLevelComplexPoints_injective_of_independent z'.R z'.F false j'
    (GlobalTheory.TiedUnif.indep_span_of_tie z'.geo.fw z'.pins.char.base.models.HW z'.geo.bar hF.2.1.jUnif j' _).1

end GlobalTheory.Mem.R3.LiftInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelComplexPointsInjectiveExtendedDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelComplexPoints_injective_extendedData_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        Function.Injective ((z'.R.toCx3 z'.F).w0C false j')) := by
  first | exact @GlobalTheory.Mem.R3.LiftInj.baseLevelComplexPoints_injective_extendedData | exact GlobalTheory.Mem.R3.LiftInj.baseLevelComplexPoints_injective_extendedData | (intros; apply GlobalTheory.Mem.R3.LiftInj.baseLevelComplexPoints_injective_extendedData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftMatrixSolvesRelationExtendedData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftMatrixSolvesRelationExtendedData
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftMatBase

section Gen

open Formalism.IndefR.CxPass LevelOperators

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem dnLevL_of_ratZL {s : ℕ} (hok : A3.fam3.Ok3 s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    (hRZ : ∀ j t, Submodule.span ℂ ((X.jL j t) '' (X.Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)))
    {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ))
    (hE : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.DnLevL cv b := by
  intro j t
  rintro _ ⟨u, hu, rfl⟩
  have hu0 : u ∈ Submodule.span ℂ (X.jL j t '' (BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ) : Set _)) := by
    have := hu
    unfold CxData.goodPartComplexPoints at this
    rwa [hv j t] at this
  rw [lift_good_part_complex_eq_range_family (Hs j t) (hv j t)] at hu
  rw [hE j]
  refine ⟨?_, ?_⟩
  · have hle : LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA P ψ).X (A3.fam3.F.lvlA P ψ).P (A3.fam3.F.lvlA P ψ).ψ)) ≤
        LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ)) := by
      have e1 : goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ = idemOf A3.fam3.F.X :=
        goodAt_bot A3.fam3.F.X _
      rw [e1]
      exact (Hs j t).range_le A3.fam3.F.X P ψ⁻¹
    obtain ⟨u', hu', hΘ⟩ := (Hs j t).dn _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _) (hle hu)
    rw [← (Hs j t).ratLev (hRZ j t) _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _)] at hu'
    have hZeq : ((LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t) ⊓
          LinearMap.range (opF (A3.fam3.F.L j t).r (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ))) =
        LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) := by
      rw [range_toF, goodR_eq]
      rfl
    rw [hZeq] at hu'
    have h2 : Submodule.span ℂ (X.jL j t '' (LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) :
          Set _)) ≤ LinearMap.range (lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x, (X.jL_toL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩
    obtain ⟨c, hc⟩ := h2 hu'
    show X.θ' j t u ∈ principalFormsSubspace A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j
    refine Submodule.mem_iSup_of_mem t ?_
    rw [← hΘ, ← hc, ← X.tC_eq]
    exact ⟨c, rfl⟩
  · show X.θ' j t u ∈ typeSubspace A3 X j (gW j) P ψ⁻¹
    unfold typeSubspace
    rw [Submodule.mem_iInf]
    intro h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine (Hs j t).type (h : G) (((ψ⁻¹) h : Kˣ) : K) _ (fun x hx => ?_) hu0
    rw [goodR_eq] at hx
    exact opF_goodAt_type _ _ hok.ok2.irr P ψ⁻¹ h x hx

end Gen

section Conc

open Formalism.IndefR.CxPass

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tC_single_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F)
    (j : Fin D.R.m) (k : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0)) :
    (R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1) ∈ LinearMap.range ((R.toCx3 F).w0C false j) := by
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have rz : ∀ j t, Submodule.span ℂ (((R.toCx3 F).jL j t) '' ((R.toCx3 F).Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' j t)) := fun j t => by
    obtain ⟨N, ψ, hψ, hr⟩ := hL.liftTest j
    exact Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL j t)
      ((cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1).hL j t) _ (kL j t).1 (kL j t).2 (jL j t) _ ψ hψ (fun i x => hr t i x)
  have hdn : (R.toCx3 F).DnLevL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false :=
    dnLevL_of_ratZL (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) hL.ok
      (fun j t => lift_hypotheses_of_unitary hL.ok kL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) (fun _ _ _ _ => rfl) jL hL.gUnit.2 hL.gEquiv.2 j t)
      rz F.P0 F.ψ0 (fun _ _ => rfl) hL.levW
  rw [Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
  exact hdn j _ ⟨_, Submodule.subset_span ⟨_, lift_coordinates_in_good_part_family (P0 := F.P0) (ψ0 := F.ψ0) (P1 := F.P1) (ψ1 := F.ψ1)
    (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.toCx3 F) false j _ (Pi.single k 1), rfl⟩, rfl⟩

theorem liftMatC_isRat (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m) :
    Formalism.IndefR.Cx.IsRat A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMatC F.cr false j A3.A.μ0) := by
  intro i k
  obtain ⟨N, ψ, hψ, hr, hbase⟩ := hL.liftTestB j
  have hinj := (R.toCx3 F).principal_form_injective false (RealDat3.kForm_of (F := F) hL.unif false) (RealDat3.ewNorm false)
    (RealDat.nP_pos false) j
  have hmem := tC_single_mem R F hC hL j k
  obtain ⟨a, ha⟩ := Formalism.IndefR.Rat.coord_rat _ ψ hψ ((R.toCx3 F).w0C false j) hinj (fun i l => hbase i l)
    (Formalism.IndefR.Cx.solve ((R.toCx3 F).w0C false j) ((R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1)))
    (fun i' => by
      rw [Formalism.IndefR.Cx.solve_spec _ hmem, Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
      exact hr _ _ _) i
  exact ⟨a, by simpa [Formalism.IndefR.Cx.CxData.liftMatC, Formalism.IndefR.Cx.relMat] using ha⟩

theorem liftMatrix_computes_lift_rational (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0) → D.what₂.LL) :
    (R.toCx3 F).w0C false j (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding
        (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)) =
      (R.toCx3 F).tC F.cr false j A3.A.μ0 (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding x) := by
  rw [Formalism.IndefR.Cx.cpt_mulVec, Formalism.IndefR.Cx.CxData.liftMat, Formalism.IndefR.Cx.kMat_map _ (liftMatC_isRat R F hC hL j)]
  exact Formalism.IndefR.Cx.relMat_spec _ _ (tC_single_mem R F hC hL j) _

end Conc

set_option maxHeartbeats 12000000 in
theorem baseLevelLiftMatrix_solves_relation_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, (z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 *ᵥ x)) = (z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w _ _ _ _ Z hX Wt z _ _ _ hHL _ _ _ _ _ _ _ _ _ _ _ _ _ x
  exact liftMatrix_computes_lift_rational z.R z.F z.pins.char hHL _ x

end GlobalTheory.Mem.R3.LiftMatBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelLiftMatrixSolvesRelationExtendedDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLevelLiftMatrix_solves_relation_extendedData_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, (z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 *ᵥ x)) = (z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x)) := by
  exact @GlobalTheory.Mem.R3.LiftMatBase.baseLevelLiftMatrix_solves_relation_extendedData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtende
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLat0

section Key

open Formalism.IndefR.Cx

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem map_mulVec_fun (φ : K →+* K') {m n : ℕ} (θ : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    (fun k => φ ((θ *ᵥ x) k)) = θ.map φ *ᵥ fun k => φ (x k) := by
  funext k; exact RingHom.map_mulVec φ θ x k

theorem cpt_single (σ : K' →+* ℂ) {n : ℕ} (k : Fin n) : cpt σ (Pi.single k (1 : K')) = Pi.single k 1 := by
  funext i; by_cases h : i = k
  · subst h; simp [cpt]
  · simp [cpt, Pi.single_apply, h]

theorem kOf_apply (σ : K' →+* ℂ) (a : K') : kOf σ (σ a) = a := by
  classical
  have h : ∃ b : K', σ b = σ a := ⟨a, rfl⟩
  unfold kOf
  rw [dite_eq_left h]
  exact σ.injective h.choose_spec

theorem matLat_relMat_of_heq (φ : K →+* K') (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {dW dW' dZ dZ' : ℕ}
    (w0 : (Fin dW → ℂ) →ₗ[ℂ] W) (t0 : (Fin dZ → ℂ) →ₗ[ℂ] W) (w0' : (Fin dW' → ℂ) →ₗ[ℂ] W')
    (t0' : (Fin dZ' → ℂ) →ₗ[ℂ] W') (θ : Matrix (Fin dW) (Fin dZ) K) (G : Matrix (Fin dW') (Fin dW) K')
    (N : Matrix (Fin dZ') (Fin dZ) K') (hN : Function.Bijective N.mulVec)
    (hG : ∀ y : Fin dW → K, HEq (w0' (cpt σ' (G *ᵥ fun k => φ (y k)))) (w0 (cpt σ y)))
    (hNc : ∀ x : Fin dZ → K, HEq (t0' (cpt σ' (N *ᵥ fun k => φ (x k)))) (t0 (cpt σ x)))
    (hR : ∀ x : Fin dZ → K, w0 (cpt σ (θ *ᵥ x)) = t0 (cpt σ x)) (hI : Function.Injective w0')
    (L : Submodule (𝓞 K) (Fin dZ → K)) :
    Formalism.DivisionValues.matLat (kMat σ' (relMat w0' t0'))
              (Submodule.span (𝓞 K') ((fun x : Fin dZ → K => N *ᵥ fun k => φ (x k)) '' (L : Set (Fin dZ → K)))) =
      Submodule.span (𝓞 K') ((fun x : Fin dW → K => G *ᵥ fun k => φ (x k)) ''
        (Formalism.DivisionValues.matLat θ L : Set (Fin dW → K))) := by
  classical
  set eN := LinearEquiv.ofBijective (Matrix.mulVecLin N) hN with heN
  have hNe : ∀ v, eN v = N *ᵥ v := fun v => rfl
  have hb : ∀ x : Fin dZ → K, t0' (cpt σ' (N *ᵥ fun k => φ (x k))) =
      w0' (cpt σ' (G *ᵥ (θ.map φ *ᵥ fun k => φ (x k)))) := by
    intro x
    rw [← map_mulVec_fun φ θ x]
    exact eq_of_heq ((hNc x).trans ((heq_of_eq (hR x)).symm.trans (hG (θ *ᵥ x)).symm))

  have hL : ((t0'.comp (cptL σ' dZ')).comp N.mulVecLin : (Fin dZ → K') →ₛₗ[σ'] W') =
      (w0'.comp (cptL σ' dW')).comp (G.mulVecLin.comp (θ.map φ).mulVecLin) := by
    refine (Pi.basisFun K' (Fin dZ)).ext fun i => ?_
    have hs : (Pi.basisFun K' (Fin dZ)) i = fun k => φ ((Pi.single i (1 : K) : Fin dZ → K) k) := by
      rw [Pi.basisFun_apply]; funext k; by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [hs]
    simpa [cptL, Matrix.mulVecLin_apply] using hb (Pi.single i 1)

  have hθ : ∀ u : Fin dZ' → K', kMat σ' (relMat w0' t0') *ᵥ u = G *ᵥ (θ.map φ *ᵥ eN.symm u) := by
    have hk : ∀ k : Fin dZ', ∀ i, kMat σ' (relMat w0' t0') i k = (G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1))) i := by
      intro k i
      set v := G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1)) with hv
      have hw : w0' (cpt σ' v) = t0' (Pi.single k 1) := by
        have h1 := congrArg (fun f => f (eN.symm (Pi.single k 1))) hL
        simp only [LinearMap.comp_apply, cptL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply] at h1
        have h2 : N *ᵥ eN.symm (Pi.single k 1) = Pi.single k 1 := by
          rw [← hNe]; exact eN.apply_symm_apply (Pi.single k 1)
        rw [h2, cpt_single] at h1
        exact h1.symm
      have hex : ∃ y, w0' y = t0' (Pi.single k 1) := ⟨_, hw⟩
      have hsol : solve w0' (t0' (Pi.single k 1)) = cpt σ' v := by
        apply hI
        unfold solve
        rw [dite_eq_left hex]
        exact hex.choose_spec.trans hw.symm
      show kOf σ' (solve w0' (t0' (Pi.single k 1)) i) = v i
      rw [hsol]
      exact kOf_apply σ' (v i)
    have hlin : (kMat σ' (relMat w0' t0')).mulVecLin =
        G.mulVecLin.comp ((θ.map φ).mulVecLin.comp eN.symm.toLinearMap) := by
      refine (Pi.basisFun K' (Fin dZ')).ext fun k => ?_
      rw [Pi.basisFun_apply]
      funext i
      simp only [Matrix.mulVecLin_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← hk k i, Matrix.mulVec_single_one]
      rfl
    intro u
    exact congrArg (fun f => f u) hlin

  unfold Formalism.DivisionValues.matLat
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [hθ, map_mulVec_fun φ θ x]
  congr 2
  rw [← hNe]; exact eN.symm_apply_apply (fun k => φ (x k))

end Key


set_option maxHeartbeats 16000000 in
theorem liftFormsLattice_definiteLattice_baseChange_extended_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((s0Of z'.R z'.F).dW j')) (Fin ((s0Of z.R z.F).dW j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (s0Of z'.R z'.F).M j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' (((s0Of z.R z.F).M j : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL))) ∧
          Formalism.DivisionValues.matLat ((s0Of z'.R z'.F).θ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) =
            Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.and (GlobalTheory.T.extendedData_liftFormsLattice_baseLevel_baseChange_alt h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.definiteLiftLattice_baseChange_extendedData h1 h2 h3 h4 h5 h6 h7))
    (StepW.and (GlobalTheory.T.baseLevelLiftMatrix_solves_relation_extendedData_alt h1 h2 h3 h4 h5 h6 h7) (GlobalTheory.T.baseLevelComplexPoints_injective_extendedData_alt h1 h2 h3 h4 h5 h6 h7))) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨G, hGb, hM, hGc⟩ := H.1.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨N, hNb, hTl, hNc⟩ := H.1.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hR := H.2.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hI := H.2.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  refine ⟨G, hGb, hM, ?_⟩
  rw [hTl]
  exact matLat_relMat_of_heq φ _ _ _ _ _ _ _ G N hNb hGc hNc hR hI _

end GlobalTheory.Mem.R3.LiftLat0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtendeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftFormsLattice_definiteLattice_baseChange_extended : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((s0Of z'.R z'.F).dW j')) (Fin ((s0Of z.R z.F).dW j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (s0Of z'.R z'.F).M j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' (((s0Of z.R z.F).M j : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL))) ∧
          Formalism.DivisionValues.matLat ((s0Of z'.R z'.F).θ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) =
            Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)))) := by
  first | exact @GlobalTheory.Mem.R3.LiftLat0.liftFormsLattice_definiteLattice_baseChange_extended_alt | exact GlobalTheory.Mem.R3.LiftLat0.liftFormsLattice_definiteLattice_baseChange_extended_alt | (intros; apply GlobalTheory.Mem.R3.LiftLat0.liftFormsLattice_definiteLattice_baseChange_extended_alt <;> assumption)
end
