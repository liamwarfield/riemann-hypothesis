module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PutInSplitPlacesDatumProductOnHalf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProd
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLatticeComponentIntegralFrameCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLatticeComponentIntegralFrameCoords
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal.LatChar

variable {D : D7}

theorem finPart_pair_zero (α : Af D.host.F) (x : D.host.E) :
    finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = α ⊗ₜ[D.host.F] x := rfl

theorem latV_int {S : HSp D} {L : Lat S} (hL : ∀ z ∈ L, z ∈ intVec D S.rank) {P : Pl D → Prop}
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) (i : Fin S.rank) : finPart D (y i) ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    change finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) ∈ intAE D
    rw [finPart_pair_zero, one_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, ⟨x i, hL x hx i⟩, rfl⟩
  | zero => rw [Pi.zero_apply, RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Pi.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [Pi.neg_apply, RingHom.map_neg]; exact neg_mem hx

theorem lat_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
    {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    β.IsLat L Λ → (∀ z, z ∈ L ↔ z ∈ intVec D _) → ∀ x : n → k, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  intro D k _ _ _ _ p S n _ _ β L Λ hΛ hL x
  rw [hΛ x]
  constructor
  · intro h r
    exact (p.int_iff _).2 (latV_int (fun z hz => (hL z).1 hz) h r)
  · intro h
    have h1 : (fun i => p.sec ((β.b *ᵥ x) i)) =
        ∑ r, fun i => p.sec ((β.b *ᵥ x) r) * incA D ((Pi.single r 1 : Fin S.rank → D.host.E) i) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, RingHom.map_one, mul_one]
      · intro r _ hr
        rw [Pi.single_eq_of_ne hr.symm, RingHom.map_zero, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h1]
    refine sum_mem fun r _ => GlobalTheory.FinPl.FrameLat.int_mul_mem (GlobalTheory.FinPl.FrameLat.sec_mem_intAt p _ (h r)) ((hL _).2 fun i => ?_)
    by_cases hi : i = r
    · subst hi; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hi]; exact isIntegral_zero

end GlobalTheory.PhiOneVal.LatChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLatticeComponentIntegralFrameCoordsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_lattice_component_integral_frame_coords : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
    {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)),
    β.IsLat L Λ → (∀ z, z ∈ L ↔ z ∈ intVec D _) → ∀ x : n → k, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  first | exact @GlobalTheory.PhiOneVal.LatChar.lat_iff | exact GlobalTheory.PhiOneVal.LatChar.lat_iff | (intros; apply GlobalTheory.PhiOneVal.LatChar.lat_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumns
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section
namespace GlobalTheory.PhiOneVal

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_last_of_pair {a : ℕ} (Q : Pair k (Fin a)) : ∃ r : Fin a, r.1 + 1 = a := by
  rcases a with _ | a
  · exact absurd (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]) Q.fn_ne
  · exact ⟨Fin.last a, rfl⟩

theorem hasVal_finset_sum {n ι : Type} (Q : Pair k n) (s : Finset ι) (x : ι → n → k) (v : ι → 𝓀[k])
    (h : ∀ i, Q.HasVal (x i) (v i)) : Q.HasVal (∑ i ∈ s, x i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Pair.mem_ker.1 (zero_mem Q.ker)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem maps_iff_basis {n n' : Type} [Fintype n] [DecidableEq n] (Q : Pair k n) (Q' : Pair k n') (A A' : Matrix n n k)
    (hA : A' * A = 1) (hQ : ∀ x ∈ Q.lat, ∀ r, (A *ᵥ x) r ∈ 𝒪[k]) (v : n → 𝓀[k])
    (hv : ∀ r, Q.HasVal (A' *ᵥ Pi.single r 1) (v r)) (M : Matrix n' n k) :
    Maps Q Q' M ↔ ∀ r, Q'.HasVal (M *ᵥ (A' *ᵥ Pi.single r 1)) (v r) := by
  rw [maps_iff_hasVal]
  refine ⟨fun h r => h _ _ (hv r), fun h y c hy => ?_⟩
  let w : n → 𝒪[k] := fun r => ⟨_, hQ y hy.mem r⟩
  have e : y = ∑ r, w r • (A' *ᵥ Pi.single r 1) := by
    have e1 : A *ᵥ y = ∑ r, w r • (Pi.single r 1 : n → k) := by
      ext i
      simp [w, Pi.single_apply, Finset.sum_apply, Subring.smul_def]
    calc y = A' *ᵥ (A *ᵥ y) := by rw [mulVec_mulVec, hA, one_mulVec]
      _ = _ := by
        rw [e1, mulVec_sum]
        exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _
  have h1 := hasVal_finset_sum Q Finset.univ _ _ fun r => (hv r).smul (w r)
  have h2 := hasVal_finset_sum Q' Finset.univ _ _ fun r => (h r).smul (w r)
  rw [← e] at h1
  rw [hy.unique h1]
  convert h2 using 1
  conv_lhs => rw [e, mulVec_sum]
  exact Finset.sum_congr rfl fun r _ => mulVec_smul _ _ _

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (φ : E →+* k) (ψ : 𝓞 E →+* 𝒪[k])

theorem hasVal_col_iff (hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 E) E c))
    (hres : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal)
    (hint : ∀ x : E, φ x ∈ 𝒪[k] → ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E s * x)
    {b : ℕ} (Q : Pair k (Fin b)) (B B' : Matrix (Fin b) (Fin b) k) (hB : B * B' = 1)
    (hQ : ∀ x ∈ Q.lat, ∀ r, (B *ᵥ x) r ∈ 𝒪[k]) (t : 𝓞 E)
    (hv : ∀ w : Fin b → 𝓞 E, ∀ r : Fin b, r.1 + 1 = b →
      Q.HasVal (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (w r'))) (residue 𝒪[k] (ψ (t * w r))))
    (u : Fin b → E) (ε : 𝓞 E) :
    Q.HasVal (B' *ᵥ fun q => φ (u q)) (residue 𝒪[k] (ψ (t * ε))) ↔
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ c : Fin b → 𝓞 E, (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) ∧
        ∀ q : Fin b, q.1 + 1 = b → t * (c q - s * ε) ∈ P.asIdeal := by
  have key : ∀ (s : 𝓞 E) (c : Fin b → 𝓞 E), (∀ q, algebraMap (𝓞 E) E (c q) = algebraMap (𝓞 E) E s * u q) →
      (B' *ᵥ fun r' => φ (algebraMap (𝓞 E) E (c r'))) = ψ s • (B' *ᵥ fun q => φ (u q)) := by
    intro s c hc
    rw [← mulVec_smul]
    congr 1
    ext q
    rw [hc, map_mul, ← hψ]
    rfl
  have key2 : ∀ s c : 𝓞 E, t * (c - s * ε) ∈ P.asIdeal ↔
      residue 𝒪[k] (ψ (t * c)) = residue 𝒪[k] (ψ s) * residue 𝒪[k] (ψ (t * ε)) := by
    intro s c
    rw [← hres, ← map_mul, ← map_mul, show t * (c - s * ε) = t * c - s * (t * ε) by ring, map_sub, map_sub, sub_eq_zero]
  constructor
  · intro h
    have h1 := hQ _ h.mem
    rw [mulVec_mulVec, hB, one_mulVec] at h1
    choose s hs c hc using fun q => hint _ (h1 q)
    have hc' : ∀ q, algebraMap (𝓞 E) E (c q * ∏ q' ∈ Finset.univ.erase q, s q') =
        algebraMap (𝓞 E) E (∏ q', s q') * u q := by
      intro q
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q), map_mul, map_mul, hc]
      ring
    refine ⟨∏ q, s q, ?_, fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q', hc', fun q hq => ?_⟩
    · haveI := P.isPrime
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨q, -, hq⟩
      exact hs q hq
    · rw [key2]
      have h2 := hv (fun q => c q * ∏ q' ∈ Finset.univ.erase q, s q') q hq
      rw [key _ _ hc'] at h2
      exact h2.unique (h.smul _)
  · rintro ⟨s, hs, c, hc, hP⟩
    obtain ⟨q, hq⟩ := exists_last_of_pair Q
    have h2 := hv c q hq
    rw [key _ _ hc, (key2 _ _).1 (hP q hq)] at h2
    obtain ⟨v, hv'⟩ : IsUnit (ψ s) := by
      by_contra hn
      exact hs ((hres s).1 ((residue_eq_zero_iff _).2 hn))
    have h3 := h2.smul (↑v⁻¹ : 𝒪[k])
    rwa [← hv', smul_smul, Units.inv_mul, one_smul, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h3

end Local

theorem maps_rd_iff_colCond : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P →
    ∀ {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (α : Frame p S (Fin S.rank)) (β : Frame p T (Fin T.rank))
    (Q : Pair k (Fin S.rank)) (Q' : Pair k (Fin T.rank)) (LS : Lat S) (LT : Lat T) (t : 𝓞 D.host.E),
    (∀ z, z ∈ LS ↔ z ∈ intVec D _) → (∀ z, z ∈ LT ↔ z ∈ intVec D _) → α.IsLat LS Q.lat → β.IsLat LT Q'.lat →
    (∀ w ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q.HasVal (α.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    (∀ w ∈ LT, ∀ r : Fin T.rank, r.1 + 1 = T.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q'.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (Maps Q Q' (GlobalTheory.FinPl.rd α β (z.map (incA D))) ↔ ColCond P t (toHom S T hS hT z)) := by
  intro D k _ _ _ _ p P hP S T a b hS hT α β Q Q' LS LT t hLS hLT hα hβ vS vT z
  subst hS hT
  let φ : D.host.E →+* k := p.pr.comp (incA D)
  have hres := GlobalTheory.T.split_component_integer_residue_zero_iff_mem_prime p P hP
  let ψ : 𝓞 D.host.E →+* 𝒪[k] := (φ.comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _ fun c => (hres c).1
  have hψ : ∀ c, (ψ c : k) = φ (algebraMap (𝓞 D.host.E) D.host.E c) := fun c => rfl
  have hres' : ∀ c, residue 𝒪[k] (ψ c) = 0 ↔ c ∈ P.asIdeal := fun c => (hres c).2
  have hS : ∀ w : Fin S.rank → 𝓞 D.host.E, ∀ r : Fin S.rank, r.1 + 1 = S.rank →
      Q.HasVal (α.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vS (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLS _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  have hT : ∀ w : Fin T.rank → 𝓞 D.host.E, ∀ r : Fin T.rank, r.1 + 1 = T.rank →
      Q'.HasVal (β.b' *ᵥ fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E (w r'))) (residue 𝒪[k] (ψ (t * w r))) := by
    intro w r hr
    obtain ⟨s, hs, h⟩ := vT (fun r' => algebraMap (𝓞 D.host.E) D.host.E (w r')) ((hLT _).2 fun i => (w i).isIntegral_coe) r hr
    have : s = ψ (t * w r) := Subtype.ext (by rw [hs, hψ, map_mul (algebraMap (𝓞 D.host.E) D.host.E)]; rfl)
    exact this ▸ h
  obtain ⟨l, hl⟩ := exists_last_of_pair Q
  have hy : ∀ r : Fin S.rank, Q.HasVal (α.b' *ᵥ Pi.single r 1)
      (residue 𝒪[k] (ψ (t * if r.1 + 1 = S.rank then 1 else 0))) := by
    intro r
    have h := hS (Pi.single r 1) l hl
    have e1 : (fun r' => φ (algebraMap (𝓞 D.host.E) D.host.E ((Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) r'))) =
        Pi.single r 1 := by
      ext r'
      by_cases h' : r' = r <;> simp [Pi.single_apply, h']
    have e2 : (Pi.single r 1 : Fin S.rank → 𝓞 D.host.E) l = if r.1 + 1 = S.rank then 1 else 0 := by
      rw [Pi.single_apply]
      exact if_congr ⟨fun h => h ▸ hl, fun h => Fin.ext (by omega)⟩ rfl rfl
    rwa [e1, e2] at h
  rw [maps_iff_basis Q Q' α.b α.b' α.b'b (fun x hx => (GlobalTheory.T.split_place_lattice_component_integral_frame_coords α LS Q.lat hα hLS x).1 hx) _ hy]
  refine forall_congr' fun r => ?_
  have e : GlobalTheory.FinPl.rd α β (z.map (incA D)) *ᵥ (α.b' *ᵥ Pi.single r 1) = β.b' *ᵥ fun q => φ (z q r) := by
    rw [GlobalTheory.FinPl.rd, mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one, ← mulVec_mulVec, mulVec_single_one]
    rfl
  rw [e, hasVal_col_iff P φ ψ hψ hres' (GlobalTheory.PhiOneVal.exists_denom_notMem_of_pr_int p P hP) Q' β.b β.b' β.bb'
    (fun x hx => (GlobalTheory.T.split_place_lattice_component_integral_frame_coords β LT Q'.lat hβ hLT x).1 hx) t hT]
  have e3 : ∀ q, toHom S T rfl rfl z (Pi.single r 1) q = z q r := by
    intro q
    simp [toHom]
  simp only [e3, mul_ite, mul_one, mul_zero]

end GlobalTheory.PhiOneVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLevelPrimePhiOneEqOneIffColumnsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maps_rd_iff_colCond_toHom : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e P →
    ∀ {S T : HSp D} {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (α : Frame p S (Fin S.rank)) (β : Frame p T (Fin T.rank))
    (Q : Pair k (Fin S.rank)) (Q' : Pair k (Fin T.rank)) (LS : Lat S) (LT : Lat T) (t : 𝓞 D.host.E),
    (∀ z, z ∈ LS ↔ z ∈ intVec D _) → (∀ z, z ∈ LT ↔ z ∈ intVec D _) → α.IsLat LS Q.lat → β.IsLat LT Q'.lat →
    (∀ w ∈ LS, ∀ r : Fin S.rank, r.1 + 1 = S.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q.HasVal (α.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    (∀ w ∈ LT, ∀ r : Fin T.rank, r.1 + 1 = T.rank → ∃ s : 𝒪[k],
      (s : k) = p.pr (incA D ((t : D.host.E) * w r)) ∧ Q'.HasVal (β.b' *ᵥ fun r' => p.pr (incA D (w r'))) (residue 𝒪[k] s)) →
    ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (Maps Q Q' (GlobalTheory.FinPl.rd α β (z.map (incA D))) ↔ ColCond P t (toHom S T hS hT z)) := by
  first | exact @GlobalTheory.PhiOneVal.maps_rd_iff_colCond | exact GlobalTheory.PhiOneVal.maps_rd_iff_colCond | (intros; apply GlobalTheory.PhiOneVal.maps_rd_iff_colCond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnCondition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

section
variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [StarRing E] in
theorem phit_mem_loc {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M := Iff.rfl

omit [StarRing E] in
theorem phit_mem_std {n : ℕ} (y : Fin n → E) :
    y ∈ Formalism.L2.Col.stdLat E n ↔ ∀ i, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = y i := by
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

omit [StarRing E] in
theorem phit_single_std {n : ℕ} (r : Fin n) : (Pi.single r 1 : Fin n → E) ∈ Formalism.L2.Col.stdLat E n := by
  rw [phit_mem_std]
  intro i
  by_cases h : i = r
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

omit [StarRing E] in
theorem phit_mk_ne (P : HeightOneSpectrum (𝓞 E)) {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)

theorem phit_local {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E) (hd : d.Ok) (hd' : d'.Ok)
    (hN : d.N = Formalism.L2.Col.stdLat E a) (hN' : d'.N = Formalism.L2.Col.stdLat E b) (P : ST)
    (hf : ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c))
    (hf' : ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c))
    (x : Formalism.L2.Col.HomE E a b) :
    (∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) ↔ ColCond P.1 t x := by
  haveI := P.1.isPrime
  have hle : ∀ y ∈ Formalism.L2.Col.stdLat E a, y ∈ d.at P.1 := fun y hy =>
    (phit_mem_loc P.1 _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.1.isPrime.ne_top, by rw [hN, one_smul]; exact hy⟩
  have hxs : ∀ (s : 𝓞 E) (y : Fin a → E), x (s • y) = s • x y := fun s y => x.map_smul_of_tower s y

  have hfe : ∀ r : Fin a, d.f P (Pi.single r 1) =
      Ideal.Quotient.mk P.1.asIdeal (t * if r.1 + 1 = a then 1 else 0) := by
    intro r
    have hr := r.2
    refine hf _ (phit_single_std r) ⟨a - 1, by omega⟩ (by simp only; omega) _ ?_
    by_cases h : r.1 + 1 = a
    · have : (⟨a - 1, by omega⟩ : Fin a) = r := Fin.ext (by simp only; omega)
      rw [this]; simp [h]
    · have : (⟨a - 1, by omega⟩ : Fin a) ≠ r := fun e => h (by have := congrArg Fin.val e; simp only at this; omega)
      simp [h, this]
  have hsm : ∀ (s : 𝓞 E) (z : Fin b → E) (q : Fin b), (s • z) q = algebraMap (𝓞 E) E s * z q := by
    intro s z q
    rw [Pi.smul_apply, Algebra.smul_def]
  constructor
  · intro h r
    obtain ⟨h1, h2⟩ := h _ (hle _ (phit_single_std r))
    obtain ⟨s, hs, hsx⟩ := (phit_mem_loc P.1 _ _).1 h1
    rw [hN'] at hsx
    choose c hc using (phit_mem_std _).1 hsx
    refine ⟨s, hs, c, fun q => by rw [hc, hsm], fun q hq => ?_⟩
    have e1 := hf' _ hsx q hq (c q) (hc q)
    rw [hd'.f_smul P s _ h1, h2, hfe, ← map_mul] at e1
    have e2 := Ideal.Quotient.eq.1 e1.symm
    convert e2 using 1
    split_ifs <;> ring
  · intro h
    have hb : b ≠ 0 := by
      rintro rfl
      obtain ⟨z, hz, hz0⟩ := hd'.f_ne P
      apply hz0
      have h0 := hd'.f_smul P 0 0 (Submodule.zero_mem _)
      rw [Subsingleton.elim z 0]
      simpa using h0
    let M : Submodule (𝓞 E) (Fin a → E) :=
      { carrier := {y | y ∈ d.at P.1 ∧ x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y}
        add_mem' := by
          rintro y z ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
          refine ⟨Submodule.add_mem _ h1 k1, by rw [map_add (f := _)]; exact Submodule.add_mem _ h2 k2, ?_⟩
          rw [map_add (f := _), hd'.f_add P _ h2 _ k2, hd.f_add P _ h1 _ k1, h3, k3]
        zero_mem' := by
          refine ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _, ?_⟩
          have h0 := hd.f_smul P 0 0 (Submodule.zero_mem _)
          have h0' := hd'.f_smul P 0 0 (Submodule.zero_mem _)
          simp only [smul_zero, map_zero, zero_mul] at h0 h0'
          rw [map_zero, h0, h0']
        smul_mem' := by
          rintro s y ⟨h1, h2, h3⟩
          refine ⟨Submodule.smul_mem _ s h1, by rw [hxs]; exact Submodule.smul_mem _ s h2, ?_⟩
          rw [hxs, hd'.f_smul P s _ h2, hd.f_smul P s _ h1, h3] }
    have hM : ∀ y, y ∈ M ↔ (y ∈ d.at P.1 ∧ x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := fun _ => Iff.rfl
    have he : ∀ r : Fin a, (Pi.single r 1 : Fin a → E) ∈ M := by
      intro r
      obtain ⟨s, hs, c, hc, hq⟩ := h r
      have hsx : s • x (Pi.single r 1) ∈ Formalism.L2.Col.stdLat E b :=
        (phit_mem_std _).2 fun q => ⟨c q, by rw [hc, hsm]⟩
      have h1 : x (Pi.single r 1) ∈ d'.at P.1 := (phit_mem_loc P.1 _ _).2 ⟨s, hs, by rw [hN']; exact hsx⟩
      refine (hM _).2 ⟨hle _ (phit_single_std r), h1, ?_⟩
      have hq' : (⟨b - 1, by omega⟩ : Fin b).1 + 1 = b := by simp only; omega
      have e1 := hf' _ hsx _ hq' (c _) (by rw [hc, hsm])
      rw [hd'.f_smul P s _ h1] at e1
      apply mul_left_cancel₀ (phit_mk_ne P.1 hs)
      rw [e1, hfe, ← map_mul]
      refine Ideal.Quotient.eq.2 ?_
      convert hq _ hq' using 1
      split_ifs <;> ring
    have hstd : ∀ y ∈ Formalism.L2.Col.stdLat E a, y ∈ M := by
      intro y hy
      choose c hc using (phit_mem_std _).1 hy
      have : y = ∑ r, c r • (Pi.single r 1 : Fin a → E) := by
        funext i
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, ← hc]
      rw [this]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (he r)
    intro y hy
    obtain ⟨s, hs, hsy⟩ := (phit_mem_loc P.1 _ _).1 hy
    rw [hN] at hsy
    obtain ⟨-, h2, h3⟩ := (hM _).1 (hstd _ hsy)
    rw [hxs] at h2 h3
    obtain ⟨u, hu, huy⟩ := (phit_mem_loc P.1 _ _).1 h2
    have h1 : x y ∈ d'.at P.1 := (phit_mem_loc P.1 _ _).2
      ⟨u * s, fun hm => (P.1.isPrime.mem_or_mem hm).elim hu hs, by rw [mul_smul]; exact huy⟩
    refine ⟨h1, ?_⟩
    rw [hd'.f_smul P s _ h1, hd.f_smul P s _ hy] at h3
    exact mul_left_cancel₀ (phit_mk_ne P.1 hs) h3

end

theorem phiT_eq_one_iff_colCond : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (K : Type) [Field K] (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E), d.Ok → d'.Ok →
    d.N = Formalism.L2.Col.stdLat E a → d'.N = Formalism.L2.Col.stdLat E b →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    ∀ x : Formalism.L2.Col.HomE E a b, (Formalism.L2.Col.phiT K d d' x = 1 ↔ ∀ P : ST, ColCond P.1 t x) := by
  intro E _ _ _ a b ST SG SG' K _ d d' t hd hd' hN hN' hf hf' x
  classical
  unfold Formalism.L2.Col.phiT
  rw [ite_eq_left_iff]
  simp only [zero_ne_one, imp_false, not_not]
  exact forall_congr' fun P => phit_local d d' t hd hd' hN hN' P (hf P) (hf' P) x

end GlobalTheory.PhiOneVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiOneEqOneIffColumnConditionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_one_eq_one_iff_column_condition : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (K : Type) [Field K] (d : Formalism.L2.Col.Deco E a ST SG) (d' : Formalism.L2.Col.Deco E b ST SG') (t : 𝓞 E), d.Ok → d'.Ok →
    d.N = Formalism.L2.Col.stdLat E a → d'.N = Formalism.L2.Col.stdLat E b →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E a, ∀ r : Fin a, r.1 + 1 = a → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    (∀ P : ST, ∀ x ∈ Formalism.L2.Col.stdLat E b, ∀ r : Fin b, r.1 + 1 = b → ∀ c : 𝓞 E, algebraMap (𝓞 E) E c = x r →
      d'.f P x = Ideal.Quotient.mk P.1.asIdeal (t * c)) →
    ∀ x : Formalism.L2.Col.HomE E a b, (Formalism.L2.Col.phiT K d d' x = 1 ↔ ∀ P : ST, ColCond P.1 t x) := by
  first | exact @GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond | exact GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond | (intros; apply GlobalTheory.PhiOneVal.phiT_eq_one_iff_colCond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

theorem base_deco_fn : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  intro B X I l Z u a Ch A hA i hi β P x hx r hr c hc
  choose y hy using (Formalism.L2.Col.mem_stdLat x).1 hx
  have hxy : x = fun j => (y j : B.fields.E) := funext fun j => (hy j).symm
  have hyc : y r = c := NumberField.RingOfIntegers.coe_injective ((hy r).trans hc.symm)
  rw [hxy, ← hyc]
  exact GlobalTheory.BaseFn.fn_eq (hA.base i hi β).1 (hA.base i hi β).2 P r hr _ (fun j => (hA.reads i hi).k_T β P r j hr) y

end GlobalTheory.PhiOneVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  first | exact @GlobalTheory.PhiOneVal.base_deco_fn | exact GlobalTheory.PhiOneVal.base_deco_fn | (intros; apply GlobalTheory.PhiOneVal.base_deco_fn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

noncomputable section

namespace GlobalTheory.PhiOneVal


open Classical in
theorem phiT_base_eq_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  intro B X I _ _ l Z u a Ch A hA k _ _ _ _ ι p β Q L hS J hJ j hj α γ z
  have hj0 : j ≤ B.R.m := Nat.le_of_succ_le hj
  obtain ⟨⟨e, he⟩, hS2⟩ := hS
  obtain ⟨hLj, hSj⟩ := hS2 j hj0
  obtain ⟨hLj', hSj'⟩ := hS2 (j + 1) hj
  have hG := GlobalTheory.T.phi_one_eq_one_iff_column_condition B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 (B.fields.conjO (X.piT u))
    (A.p0 j α).1.1.deco.2 (A.p0 (j + 1) γ).1.1.deco.2 (hA.base j hj0 α).2 (hA.base (j + 1) hj γ).2
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA j hj0 α P x hx r hr c hc)
    (fun P x hx r hr c hc => GlobalTheory.T.baseChartDecoration_levelPrimeFunctional_eq_conj_mul I l Z u a Ch A hA (j + 1) hj γ P x hx r hr c hc)
    (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)
  have hLoc : ∀ i, (Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) ↔
      ColCond (e i).1 (B.fields.conjO (X.piT u)) (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) :=
    fun i => GlobalTheory.T.maps_rd_iff_colCond_toHom (p i) (e i).1 (he i) _ _ (β j i) (β (j + 1) i) (Q j i) (Q (j + 1) i) (L j) (L (j + 1)) _ hLj hLj'
      (hSj i).1 (hSj' i).1 (hSj i).2 (hSj' i).2 z
  have key : (∀ P : (B.primes X).vT u, ColCond P.1 (B.fields.conjO (X.piT u))
      (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z)) ↔
      ∀ i ∈ J, Maps (Q j i) (Q (j + 1) i) (GlobalTheory.FinPl.rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z)))) := by
    refine ⟨fun h i _ => (hLoc i).2 (h (e i)), fun h P => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective P
    exact (hLoc i).1 (h i (hJ.all i))
  have hprod : ∀ (J' : List ι) (c : ι → Prop), (J'.map fun i => (if c i then (1 : ℂ) else 0)).prod =
      if ∀ i ∈ J', c i then 1 else 0 := by
    intro J' c
    induction J' with
    | nil => simp
    | cons i J' ih =>
      rw [List.map_cons, List.prod_cons, ih]
      by_cases h : c i <;> simp [h]
  have hv : ∀ x, Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 1 ∨
      Formalism.L2.Col.phiT B.LL (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1 x = 0 := by
    intro x
    unfold Formalism.L2.Col.phiT
    split_ifs <;> simp
  simp only [phiOne]
  rw [hprod]
  split_ifs with hc
  · rw [hG.2 (key.2 hc), map_one]
  · rcases hv (toHom _ _ (rankN (I.rec7 l Z) j hj0) (rankN (I.rec7 l Z) (j + 1) hj) z) with h1 | h0
    · exact absurd (key.1 (hG.1 h1)) hc
    · rw [h0, map_zero]

end GlobalTheory.PhiOneVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePointsLevelDatumEqLocalProdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ J : List ι, Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ j (hj : j + 1 ≤ B.R.m) (α : Ch j) (γ : Ch (j + 1))
      (z : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E),
      B.embLL (Formalism.L2.Col.phiT _ (A.p0 j α).1.1.deco.1 (A.p0 (j + 1) γ).1.1.deco.1
          (toHom _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) z)) =
        (J.map fun i => phiOne (Q j i) (Q (j + 1) i) (rd (β j i) (β (j + 1) i) (z.map (incA (I.rec7 l Z))))).prod := by
  first | exact @GlobalTheory.PhiOneVal.phiT_base_eq_prod | exact GlobalTheory.PhiOneVal.phiT_base_eq_prod | (intros; apply GlobalTheory.PhiOneVal.phiT_base_eq_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twVec' : TwVec' := by
  intro B X I hOk hPins l Z u a Ch A hA ψ θ x vac c₀ hX k _ _ _ _ ι p β Q hStd J hPl j hj α γ cT hReps e he
  have hjm : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hL0 : ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs j hjm).2.2
  have hL1 : ∀ z, z ∈ (x (j + 1)).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs (j + 1) hj).2.2
  have hvac := hX.vc j (by omega)
  have hS0 : ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL0 z
  have hS1 : ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL1 z
  have hV : Vac ψ _ _ (x j).L (x (j + 1)).L (fun v => ∃ i, v = (p i).v) (vac j) := by
    refine ⟨hvac.2.theta, ?_⟩
    have hle : latO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) (fun v => ∃ i, v = (p i).v) ≤ stdHom _ _ := by
      rw [hS0, hS1]
      apply AddSubgroup.closure_mono
      rintro w ⟨a, ha, -, rest⟩
      exact ⟨a, ha, fun _ h => absurd trivial h, rest⟩
    exact ⟨fun u hu => hvac.2.lat.1 u (hle hu), fun e' he' u hu hh => hvac.2.lat.2 e' he' u (hle hu) hh⟩
  have hO := hReps.2 (vac j) hV
  obtain ⟨eq, heq⟩ := hStd.1
  have hF := GlobalTheory.T.putInSplitPlaces_datum_product_on_half (I.rec7 l Z) k ι p J hPl _ _ ψ hX.std _ _ (β j) (β (j + 1)) (x j).L (x (j + 1)).L
    (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z j hjm _ hL0) (GlobalTheory.T.integral_coordinate_vectors_chain_space_selfDual I hOk l Z (j + 1) hj _ hL1) hL0 hL1 _ e he ⟨eq, heq⟩ _ (vac j) _ hvac.2.theta hvac.2.lat hO
  have hval := GlobalTheory.T.chartBasePoints_levelDatum_eq_local_prod I hOk hPins l Z u a Ch A hA k ι p β Q _ hStd J hPl j hj α γ
  convert hF using 2 with z
  exact hval z

end GlobalTheory.AdForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrimeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime : GlobalTheory.AdForm.TwVec' := by
  first | exact @GlobalTheory.AdForm.twVec' | exact GlobalTheory.AdForm.twVec' | (intros; apply GlobalTheory.AdForm.twVec' <;> assumption)
end
