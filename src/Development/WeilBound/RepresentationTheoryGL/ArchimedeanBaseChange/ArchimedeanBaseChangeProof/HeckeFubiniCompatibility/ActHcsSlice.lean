module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActLoc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActEq
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace ActEq

open prime_not_mem_section_base_place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem gInf_infP_inv_mul (y : InfinitePlace E → G n) (w : InfinitePlace E) (z : GA E n) :
    gInf w ((infP n y)⁻¹ * z) = (y w)⁻¹ * gInf w z := by
  rw [map_mul, map_inv, gInf_infP]

theorem gFin_infP_inv_mul (y : InfinitePlace E → G n) (z : GA E n) : gFin ((infP n y)⁻¹ * z) = gFin z := by
  rw [map_mul, map_inv, gFin_infP, inv_one, one_mul]

theorem entA_place [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (hk : IsMults μ k val T) (v : InfinitePlace E)
    (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : IxA M) (z : GA E n) :
    entA k I J ((infP n (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * z) =
      ∑ l, ent (M v) ((M v).ρ u⁻¹) (I v) l * entA k (Function.update I v l) J z := by
  simp only [entA, gInf_infP_inv_mul]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
  have hv : ent (M v) (k v (((Pi.mulSingle v (Unitary.toUnits u) : InfinitePlace E → G n) v)⁻¹ * gInf v z).val) (I v) (J v) =
      ∑ l, ent (M v) ((M v).ρ u⁻¹) (I v) l * ent (M v) (k v (gInf v z).val) l (J v) := by
    rw [Pi.mulSingle_eq_same]
    have h2 := mult_equivariant_val (hk v) (gInf v z) u⁻¹ 1
    simp only [OneMemClass.coe_one, map_one, mul_one] at h2
    have e : ((Unitary.toUnits u)⁻¹ * gInf v z).val = (u⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 * (gInf v z).val := by
      rw [Units.val_mul]
      rfl
    rw [e, h2, PMul.ent_mul]
  have hw : ∀ w : {w // w ≠ v}, ent (M w) (k w (((Pi.mulSingle v (Unitary.toUnits u) : InfinitePlace E → G n) w)⁻¹ * gInf w z).val) (I w) (J w) =
      ent (M w) (k w (gInf w z).val) (I w) (J w) := by
    intro w
    rw [Pi.mulSingle_eq_of_ne w.2, inv_one, one_mul]
  rw [hv, Finset.prod_congr rfl fun w _ => hw w, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v, Function.update_self]
  have hw' : ∀ w : {w // w ≠ v}, ent (M w) (k w (gInf w z).val) (Function.update I v l w) (J w) =
      ent (M w) (k w (gInf w z).val) (I w) (J w) := fun w => by
    rw [Function.update_of_ne w.2]
  rw [Finset.prod_congr rfl fun w _ => hw' w]
  ring

end ActEq

open prime_not_mem_section_base_place ActEq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem equiv_a (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ] {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hR : Repr D ka kb ψ f) (v : InfinitePlace E) (u : Matrix.unitaryGroup (Fin a) ℂ) (I : Io Ma Mb κ)
    (x : H E a b) :
    f I (x * (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1)) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x := by
  obtain ⟨hfc, c, hc, hconv⟩ := hR
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hRx : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  set p : H E a b := (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1) with hp
  have hΦ : ∀ j y, tens ka kb ψ I j (p⁻¹ * y) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y := by
    intro j y
    have hF : hFin (p⁻¹ * y) = hFin y :=
      Prod.ext (gFin_infP_inv_mul _ y.1) (by show gFin (1⁻¹ * y.2) = gFin y.2; rw [inv_one, one_mul])
    show entA ka I.1.1 j.1.1 ((infP a (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * y.1) *
        entA kb I.1.2 j.1.2 (1⁻¹ * y.2) * ψ I.2 j.2 (hFin (p⁻¹ * y)) = _
    rw [hF, inv_one, one_mul, entA_place hka, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [tens]
    ring
  apply mul_left_cancel₀ hc
  rw [f_mul D _ f hconv I x p]
  calc ∑ j, ∫ y, tens ka kb ψ I j (p⁻¹ * y) * f j (x * y) ∂D.μ
      = ∑ j, ∫ y, ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l *
          (tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y * f j (x * y)) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hΦ, Finset.sum_mul, mul_assoc]
    _ = ∑ j, ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l *
          ∫ y, tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y * f j (x * y) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => (hint _ j x).const_mul _]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ = ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * (c * f ((Function.update I.1.1 v l, I.1.2), I.2) x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hRx, Finset.mul_sum]
    _ = c * ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem equiv_b (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ] {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hR : Repr D ka kb ψ f) (v : InfinitePlace E) (u : Matrix.unitaryGroup (Fin b) ℂ) (I : Io Ma Mb κ)
    (x : H E a b) :
    f I (x * (1, infP b (Pi.mulSingle v (Unitary.toUnits u)))) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x := by
  obtain ⟨hfc, c, hc, hconv⟩ := hR
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hRx : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  set p : H E a b := (1, infP b (Pi.mulSingle v (Unitary.toUnits u))) with hp
  have hΦ : ∀ j y, tens ka kb ψ I j (p⁻¹ * y) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y := by
    intro j y
    have hF : hFin (p⁻¹ * y) = hFin y :=
      Prod.ext (by show gFin (1⁻¹ * y.1) = gFin y.1; rw [inv_one, one_mul]) (gFin_infP_inv_mul _ y.2)
    show entA ka I.1.1 j.1.1 (1⁻¹ * y.1) *
        entA kb I.1.2 j.1.2 ((infP b (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * y.2) * ψ I.2 j.2 (hFin (p⁻¹ * y)) = _
    rw [hF, inv_one, one_mul, entA_place hkb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [tens]
    ring
  apply mul_left_cancel₀ hc
  rw [f_mul D _ f hconv I x p]
  calc ∑ j, ∫ y, tens ka kb ψ I j (p⁻¹ * y) * f j (x * y) ∂D.μ
      = ∑ j, ∫ y, ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l *
          (tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y * f j (x * y)) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hΦ, Finset.sum_mul, mul_assoc]
    _ = ∑ j, ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l *
          ∫ y, tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y * f j (x * y) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => (hint _ j x).const_mul _]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ = ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * (c * f ((I.1.1, Function.update I.1.2 v l), I.2) x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hRx, Finset.mul_sum]
    _ = c * ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActPi
noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.BcB.CG

section Split

variable {ι : Type} [DecidableEq ι] {X : Type}

def splitY (w : ι) (t : X) (z : {v // v ≠ w} → X) : ι → X := fun v => if h : v = w then t else z ⟨v, h⟩

theorem splitY_self (w : ι) (t : X) (z : {v // v ≠ w} → X) : splitY w t z w = t := dif_pos rfl

theorem splitY_ne (w : ι) (t : X) (z : {v // v ≠ w} → X) (v : {v // v ≠ w}) : splitY w t z v = z v := by
  simp [splitY, v.2]

theorem update_splitY_self (w : ι) (t t' : X) (z : {v // v ≠ w} → X) :
    Function.update (splitY w t z) w t' = splitY w t' z := by
  funext v
  simp only [Function.update_apply, splitY]
  by_cases h : v = w
  · rw [if_pos h, dif_pos h]
  · rw [if_neg h]; simp [h]

theorem update_splitY_ne (w : ι) (t : X) (z : {v // v ≠ w} → X) (v : {v // v ≠ w}) (s : X) :
    Function.update (splitY w t z) v s = splitY w t (Function.update z v s) := by
  funext x
  simp only [Function.update_apply, splitY]
  by_cases h : x = w
  · have h' : x ≠ (v : ι) := fun e => v.2 (e ▸ h)
    rw [if_neg h', dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    by_cases h' : x = v
    · have : (⟨x, h⟩ : {v // v ≠ w}) = v := Subtype.ext h'
      rw [if_pos h', if_pos this]
    · have : (⟨x, h⟩ : {v // v ≠ w}) ≠ v := fun e => h' (congrArg Subtype.val e)
      rw [if_neg h', if_neg this]

theorem splitY_one [One X] (w : ι) : splitY w (1 : X) (1 : {v // v ≠ w} → X) = 1 := by
  funext v
  by_cases h : v = w <;> simp [splitY, h]

theorem continuous_splitY_left [TopologicalSpace X] (w : ι) (z : {v // v ≠ w} → X) :
    Continuous fun t : X => splitY w t z :=
  continuous_pi fun v => by
    by_cases h : v = w
    · simp only [splitY, dif_pos h]; exact continuous_id
    · simp only [splitY, dif_neg h]; exact continuous_const

theorem continuous_splitY_right [TopologicalSpace X] (w : ι) (t : X) :
    Continuous fun z : {v // v ≠ w} → X => splitY w t z :=
  continuous_pi fun v => by
    by_cases h : v = w
    · simp only [splitY, dif_pos h]; exact continuous_const
    · simp only [splitY, dif_neg h]; exact continuous_apply _

variable {Idx : ι → Type}

theorem psa_apply (w : ι) (J : ∀ v, Idx v) : Equiv.piSplitAt w Idx J = (J w, fun v : {v // v ≠ w} => J v) := rfl

theorem psa_symm_self (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    (Equiv.piSplitAt w Idx).symm (j, J') w = j :=
  congrArg Prod.fst ((Equiv.piSplitAt w Idx).apply_symm_apply (j, J'))

theorem psa_symm_ne (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) :
    (Equiv.piSplitAt w Idx).symm (j, J') v = J' v :=
  congrFun (congrArg Prod.snd ((Equiv.piSplitAt w Idx).apply_symm_apply (j, J'))) v

theorem psa_symm_apply_self (w : ι) (J : ∀ v, Idx v) : (Equiv.piSplitAt w Idx).symm (J w, fun v : {v // v ≠ w} => J v) = J :=
  (Equiv.piSplitAt w Idx).symm_apply_apply J

theorem update_psa_self (w : ι) (j j' : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) w j' = (Equiv.piSplitAt w Idx).symm (j', J') := by
  apply (Equiv.piSplitAt w Idx).injective
  rw [Equiv.apply_symm_apply, psa_apply]
  refine Prod.ext ?_ ?_
  · exact Function.update_self _ _ _
  · funext v
    show Function.update _ w j' (v : ι) = J' v
    rw [Function.update_of_ne v.2, psa_symm_ne]

theorem update_psa_ne (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) (x : Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) (v : ι) x =
      (Equiv.piSplitAt w Idx).symm (j, Function.update J' v x) := by
  apply (Equiv.piSplitAt w Idx).injective
  rw [Equiv.apply_symm_apply, psa_apply]
  refine Prod.ext ?_ ?_
  · show Function.update _ (v : ι) x w = j
    rw [Function.update_of_ne (Ne.symm v.2), psa_symm_self]
  · funext v'
    show Function.update _ (v : ι) x (v' : ι) = Function.update J' v x v'
    by_cases h : v' = v
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun e => h (Subtype.ext e)), Function.update_of_ne h, psa_symm_ne]

def splitM [MeasurableSpace X] (w : ι) : (ι → X) ≃ᵐ X × ({v // v ≠ w} → X) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (· = w)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique fun _ : {v // v = w} => X) (MeasurableEquiv.refl _))

theorem splitM_apply [MeasurableSpace X] (w : ι) (y : ι → X) : splitM w y = (y w, fun v : {v // v ≠ w} => y v) := rfl

theorem splitM_symm [MeasurableSpace X] (w : ι) (t : X) (z : {v // v ≠ w} → X) :
    (splitM w).symm (t, z) = splitY w t z := by
  rw [MeasurableEquiv.symm_apply_eq, splitM_apply]
  refine Prod.ext (splitY_self w t z).symm ?_
  funext v
  exact (splitY_ne w t z v).symm

theorem splitM_mp [MeasurableSpace X] [Fintype ι] (μ : Measure X) [SigmaFinite μ] (w : ι) :
    MeasurePreserving (splitM w) (Measure.pi fun _ : ι => μ) (μ.prod (Measure.pi fun _ : {v // v ≠ w} => μ)) :=
  ((@measurePreserving_piUnique {v // v = w} (Subtype.fintype _) (fun _ => X) _ _ (fun _ => μ)).prod (MeasurePreserving.id _)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (· = w))

end Split

section Iter

variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem pi_cont_supp {ι : Type} [Fintype ι] [DecidableEq ι] {Idx : ι → Type} [∀ v, Fintype (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J)) :
    Continuous (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ∧
      HasCompactSupport (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) := by
  refine ⟨continuous_finsetSum _ fun J _ => Continuous.mul ?_ (hu J), ?_⟩
  · exact continuous_finsetProd (f := fun v (y : ι → X) => e v (y v) (I v) (J v)) _
      fun v _ => (he v (I v) (J v)).1.comp (continuous_apply v)
  let K : ι → Set X := fun v => ⋃ a, ⋃ b, tsupport (fun t => e v t a b)
  have hK : ∀ v, IsCompact (K v) := fun v => isCompact_iUnion fun a => isCompact_iUnion fun b => (he v a b).2
  refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
  rw [Set.mem_univ_pi] at hy
  push_neg at hy
  obtain ⟨v, hv⟩ := hy
  refine Finset.sum_eq_zero fun J _ => ?_
  have h0 : e v (y v) (I v) (J v) = 0 := image_eq_zero_of_notMem_tsupport (f := fun t => e v t (I v) (J v)) fun h =>
    hv (Set.mem_iUnion.2 ⟨I v, Set.mem_iUnion.2 ⟨J v, h⟩⟩)
  rw [Finset.prod_eq_zero (Finset.mem_univ v) h0, zero_mul]

theorem pi_integrable (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Idx : ι → Type} [∀ v, Fintype (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J)) :
    Integrable (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) (Measure.pi fun _ => μ) :=
  (pi_cont_supp e u I he hu).1.integrable_of_hasCompactSupport (pi_cont_supp e u I he hu).2

variable [One X]

theorem pi_iterated_integral_continuous (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Idx : ι → Type) [∀ v, Fintype (Idx v)] [∀ v, DecidableEq (Idx v)]
      (e : ∀ v, X → Idx v → Idx v → ℂ) (val : ι → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v),
      Fintype.card ι = n →
      (∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b)) → (∀ J, Continuous (u J)) →
      (∀ v J y, ∑ j, ∫ t, e v t (J v) j * u (Function.update J v j) (Function.update y v t) ∂μ =
        val v * u J (Function.update y v 1)) →
      ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ) = (∏ v, val v) * u I 1 := by
  induction n with
  | zero =>
    intro ι _ _ Idx _ _ e val u I hn he hu hloc
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    rw [Measure.pi_of_empty (fun _ : ι => μ) (1 : ι → X), integral_dirac, Fintype.sum_unique,
      Subsingleton.elim (default : ∀ v, Idx v) I]
    simp
  | succ n ih =>
    intro ι _ _ Idx _ _ e val u I hn he hu hloc
    obtain ⟨w⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hn' : Fintype.card {v // v ≠ w} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
    have hmp := splitM_mp μ w
    have hF := pi_integrable μ e u I he hu

    have hsplit : ∀ (t : X) (z : {v // v ≠ w} → X),
        (∑ J, (∏ v, e v (splitY w t z v) (I v) (J v)) * u J (splitY w t z)) =
          ∑ j, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            (e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) := by
      intro t z
      rw [← Fintype.sum_equiv (Equiv.piSplitAt w Idx).symm
        (fun p => (∏ v, e v (splitY w t z v) (I v) ((Equiv.piSplitAt w Idx).symm p v)) *
          u ((Equiv.piSplitAt w Idx).symm p) (splitY w t z)) _ (fun _ => rfl), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J' _ => ?_
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ w, splitY_self, psa_symm_self]
      simp only [splitY_ne, psa_symm_ne]
      ring
    have hint : ∀ (z : {v // v ≠ w} → X) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v),
        Integrable (fun t => e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) μ :=
      fun z j J' => ((he w (I w) j).1.mul ((hu _).comp (continuous_splitY_left w z))).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_right (he w (I w) j).2)
    let u' : (∀ v : {v // v ≠ w}, Idx v) → ({v // v ≠ w} → X) → ℂ :=
      fun J' z => val w * u ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
    have hinner : ∀ z : {v // v ≠ w} → X,
        ∫ t, (∑ J, (∏ v, e v ((splitM w).symm (t, z) v) (I v) (J v)) * u J ((splitM w).symm (t, z))) ∂μ =
          ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) * u' J' z := by
      intro z
      simp only [splitM_symm, hsplit]
      rw [MeasureTheory.integral_finsetSum _ fun j _ => MeasureTheory.integrable_finsetSum _ fun J' _ => (hint z j J').const_mul _]
      have hj : ∀ j : Idx w, ∫ t, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            (e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) ∂μ =
          ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            ∫ t, e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z) ∂μ := fun j => by
        rw [MeasureTheory.integral_finsetSum _ fun J' _ => (hint z j J').const_mul _]
        simp only [integral_const_mul]
      rw [Finset.sum_congr rfl fun j _ => hj j]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J' _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      have h1 := hloc w ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
      rw [psa_symm_self] at h1
      simp only [update_psa_self, update_splitY_self] at h1
      exact h1
    have he' : ∀ (v : {v // v ≠ w}) a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b) :=
      fun v => he v
    have hu' : ∀ J', Continuous (u' J') :=
      fun J' => continuous_const.mul ((hu _).comp (continuous_splitY_right w 1))
    have hloc' : ∀ (v : {v // v ≠ w}) (J' : ∀ v : {v // v ≠ w}, Idx v) (z : {v // v ≠ w} → X),
        ∑ j, ∫ t, e v t (J' v) j * u' (Function.update J' v j) (Function.update z v t) ∂μ =
          val v * u' J' (Function.update z v 1) := by
      intro v J' z
      have h1 := hloc v ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
      rw [psa_symm_ne] at h1
      simp only [update_psa_ne, update_splitY_ne] at h1
      simp only [u']
      calc _ = val w * ∑ j, ∫ t, e v t (J' v) j *
              u ((Equiv.piSplitAt w Idx).symm (I w, Function.update J' v j)) (splitY w 1 (Function.update z v t)) ∂μ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← integral_const_mul]
            congr 1
            funext t
            ring
        _ = _ := by rw [h1]; ring
    have hIH := ih {v // v ≠ w} (fun v => Idx v) (fun v => e v) (fun v => val v) u' (fun v => I v) hn' he' hu' hloc'
    calc ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ)
        = ∫ q, (fun y => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ((splitM w).symm q)
            ∂(μ.prod (Measure.pi fun _ : {v // v ≠ w} => μ)) :=
          ((MeasurePreserving.symm _ hmp).integral_comp' _).symm
      _ = ∫ z, ∫ t, (fun y => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ((splitM w).symm (t, z)) ∂μ
            ∂(Measure.pi fun _ : {v // v ≠ w} => μ) :=
          integral_prod_symm _ (((MeasurePreserving.symm _ hmp).integrable_comp_emb
            (splitM w).symm.measurableEmbedding).2 hF)
      _ = ∫ z, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) * u' J' z
            ∂(Measure.pi fun _ : {v // v ≠ w} => μ) :=
          integral_congr_ae (ae_of_all _ hinner)
      _ = (∏ v : {v // v ≠ w}, val v) * u' (fun v => I v) 1 := hIH
      _ = (∏ v, val v) * u I 1 := by
          simp only [u', psa_symm_apply_self, splitY_one]
          rw [Fintype.prod_eq_mul_prod_subtype_ne _ w]
          ring

theorem pi_iter (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Idx : ι → Type) [∀ v, Fintype (Idx v)] [∀ v, DecidableEq (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (val : ι → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J))
    (hloc : ∀ v J y, ∑ j, ∫ t, e v t (J v) j * u (Function.update J v j) (Function.update y v t) ∂μ =
      val v * u J (Function.update y v 1)) :
    ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ) = (∏ v, val v) * u I 1 :=
  pi_iterated_integral_continuous μ _ ι Idx e val u I rfl he hu hloc

end Iter

end PositivityTheory.Rg.BcB.CG

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open PositivityTheory.RgBcC.Bridge (along)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

section Side
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
  [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
  {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ]

theorem actSide_b (hMA : MultAlg) (μb : Measure (G b)) [μb.IsHaarMeasure] (f : Io Ma Mb κ → H E a b → ℂ)
    (kb' : Kers Mb) vb' (T' : ℝ) (hkb' : IsMults μb kb' vb' T') (χb : InfinitePlace E → Inf b)
    (hf : ∀ i, Continuous (f i)) (hsm : ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x))
    (heq : ∀ v (u : Matrix.unitaryGroup (Fin b) ℂ) I x, f I (x * (1, infP b (Pi.mulSingle v (Unitary.toUnits u)))) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x)
    (heig : ∀ i v g m₁, IsEig (χb v) (along v g fun x => f i (m₁, x)))
    (j₁ : IxA Ma) (i₂ : IxA Mb) (z : κ) (x : H E a b) :
    ∫ yb, ∑ J, (∏ v, ent (Mb v) (kb' v (yb v).val) (i₂ v) (J v)) * f ((j₁, J), z) (x * (1, infP b yb))
      ∂(Measure.pi fun _ => μb) = valA vb' χb * f ((j₁, i₂), z) x := by
  have h1 : infP (E := E) b 1 = 1 := by simp [infP]
  have key := pi_iter μb (fun v => Ix (Mb v)) (fun v t p q => ent (Mb v) (kb' v t.val) p q) (fun v => vb' v (χb v))
    (fun J yb => f ((j₁, J), z) (x * (1, infP b yb))) i₂ (fun v p q => mult_ent (hkb' v) p q)
    (fun J => (hf _).comp (continuous_const.mul (continuous_const.prodMk (continuous_infP b)))) ?_
  · simp only [h1, Prod.mk_one_one, mul_one] at key
    exact key
  intro v J y
  set m₁ := (x * (1, infP b (Function.update y v 1))).1
  set g₀ := (x * (1, infP b (Function.update y v 1))).2
  have hsplit : ∀ t : G b, x * (1, infP b (Function.update y v t)) = (m₁, g₀ * infP b (Pi.mulSingle v t)) := by
    intro t
    have e : Function.update y v t = Function.update y v 1 * Pi.mulSingle v t := by
      funext w
      by_cases h : w = v
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    rw [e, infinitePart_mul]
    exact Prod.ext (by simp [m₁]) (by simp [g₀, mul_assoc])
  simp only [hsplit, Pi.mulSingle_one, h1, mul_one]
  have := loc_act hMA μb (Mb v) (kb' v) (vb' v) T' (hkb' v) (χb v) v
    (fun j g => f ((j₁, Function.update J v j), z) (m₁, g)) ?_ ?_ ?_ g₀ (J v)
  · simpa only [Function.update_eq_self] using this
  · intro j
    obtain ⟨φ, hφ⟩ := hsm ((j₁, Function.update J v j), z) m₁
    rw [← hφ]; exact φ.2
  · intro h u l
    have := heq v u ((j₁, Function.update J v l), z) (m₁, h)
    simpa only [Prod.mk_mul_mk, mul_one, Function.update_self, Function.update_idem] using this
  · intro j g
    exact heig ((j₁, Function.update J v j), z) v g m₁

end Side

section SideA
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}
  [MeasurableSpace (G a)] [BorelSpace (G a)]
  {Ma : Mods E a} {Mb : Mods E b} {κ : Type}

theorem actSide_a (hMA : MultAlg) (μa : Measure (G a)) [μa.IsHaarMeasure] (f : Io Ma Mb κ → H E a b → ℂ)
    (ka' : Kers Ma) va' (T' : ℝ) (hka' : IsMults μa ka' va' T') (χa : InfinitePlace E → Inf a)
    (hf : ∀ i, Continuous (f i)) (hsm : ∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂))
    (heq : ∀ v (u : Matrix.unitaryGroup (Fin a) ℂ) I x, f I (x * (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1)) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x)
    (heig : ∀ i v g m₂, IsEig (χa v) (along v g fun x => f i (x, m₂)))
    (i₁ : IxA Ma) (i₂ : IxA Mb) (z : κ) (x : H E a b) :
    ∫ ya, ∑ J, (∏ v, ent (Ma v) (ka' v (ya v).val) (i₁ v) (J v)) * f ((J, i₂), z) (x * (infP a ya, 1))
      ∂(Measure.pi fun _ => μa) = valA va' χa * f ((i₁, i₂), z) x := by
  have h1 : infP (E := E) a 1 = 1 := by simp [infP]
  have key := pi_iter μa (fun v => Ix (Ma v)) (fun v t p q => ent (Ma v) (ka' v t.val) p q) (fun v => va' v (χa v))
    (fun J ya => f ((J, i₂), z) (x * (infP a ya, 1))) i₁ (fun v p q => mult_ent (hka' v) p q)
    (fun J => (hf _).comp (continuous_const.mul ((continuous_infP a).prodMk continuous_const))) ?_
  · simp only [h1, Prod.mk_one_one, mul_one] at key
    exact key
  intro v J y
  set g₀ := (x * (infP a (Function.update y v 1), 1)).1
  set m₂ := (x * (infP a (Function.update y v 1), 1)).2
  have hsplit : ∀ t : G a, x * (infP a (Function.update y v t), 1) = (g₀ * infP a (Pi.mulSingle v t), m₂) := by
    intro t
    have e : Function.update y v t = Function.update y v 1 * Pi.mulSingle v t := by
      funext w
      by_cases h : w = v
      · subst h; simp
      · simp [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    rw [e, infinitePart_mul]
    exact Prod.ext (by simp [g₀, mul_assoc]) (by simp [m₂])
  simp only [hsplit, Pi.mulSingle_one, h1, mul_one]
  have := loc_act hMA μa (Ma v) (ka' v) (va' v) T' (hka' v) (χa v) v
    (fun j g => f ((Function.update J v j, i₂), z) (g, m₂)) ?_ ?_ ?_ g₀ (J v)
  · simpa only [Function.update_eq_self] using this
  · intro j
    obtain ⟨φ, hφ⟩ := hsm ((Function.update J v j, i₂), z) m₂
    rw [← hφ]; exact φ.2
  · intro h u l
    have := heq v u ((Function.update J v l, i₂), z) (h, m₂)
    simpa only [Prod.mk_mul_mk, mul_one, Function.update_self, Function.update_idem] using this
  · intro j g
    exact heig ((Function.update J v j, i₂), z) v g m₂

end SideA

section Lin

theorem actLin2 {Y Z J : Type} [Fintype Z] [Fintype J] [MeasurableSpace Y] (μ : Measure Y) (c : Z → ℂ) (d : J → ℂ)
    (g : Z → J → Y → ℂ) (hg : ∀ z j, Integrable (g z j) μ) :
    ∫ y, ∑ z, c z * ∑ j, d j * g z j y ∂μ = ∑ z, c z * ∑ j, d j * ∫ y, g z j y ∂μ := by
  rw [integral_finsetSum _ fun z _ => (integrable_finsetSum _ fun j _ => (hg z j).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hg z j).const_mul _]
  congr 1
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem actHcsSlice {P Q : Type} [TopologicalSpace P] [T2Space P] [TopologicalSpace Q] {F : P × Q → ℂ}
    (hF : HasCompactSupport F) (q : Q) : HasCompactSupport fun p => F (p, q) := by
  refine HasCompactSupport.intro (hF.image continuous_fst) fun p hp => ?_
  by_contra h
  exact hp ⟨(p, q), subset_tsupport _ h, rfl⟩

end Lin

section Main

theorem actVal (hMA : MultAlg) (hCF : CompatFub) (hTT : TensTest) : ActVal := by
  intro E _ _ _ a b D _ _ _ _ _ _ μa _ μb _ ν _ Ma Mb κ _ ka ka' kb kb' va va' vb vb' T T' ψ ψ' f χa χb hC hka hkb hψ
    hR hsm hEig hka' hkb' hψ'
  haveI : BorelSpace (H E a b) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  haveI : IsFiniteMeasureOnCompacts D.μ := isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hf : ∀ i, Continuous (f i) := hR.1
  have hTm := (hTT E a b μa μb Ma Mb κ ka' kb' va' vb' T' ψ' hka' hkb' hψ').1
  have heqa := fun v u I x => equiv_a D hka hkb hψ hR v u I x
  have heqb := fun v u I x => equiv_b D hka hkb hψ hR v u I x
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, convF, Pi.smul_apply, smul_eq_mul]
  set F : H E a b → ℂ := fun g => ∑ j, tens ka' kb' ψ' i j g * f j (x * g) with hFdef
  have hterm : ∀ j, Continuous (fun g => tens ka' kb' ψ' i j g * f j (x * g)) ∧
      HasCompactSupport (fun g => tens ka' kb' ψ' i j g * f j (x * g)) := fun j =>
    ⟨(hTm i j).1.mul ((hf j).comp (continuous_const.mul continuous_id)), (hTm i j).2.mul_right⟩
  have hFc : Continuous F := continuous_finsetSum _ fun j _ => (hterm j).1
  have hFs : HasCompactSupport F := by
    have e : F = ∑ j, fun g => tens ka' kb' ψ' i j g * f j (x * g) := by
      funext g; simp [hFdef, Finset.sum_apply]
    rw [e]
    exact Finset.sum_induction _ HasCompactSupport (fun _ _ h h' => h.add h') HasCompactSupport.zero
      fun j _ => (hterm j).2
  rw [← integral_finsetSum _ fun j _ => (hterm j).1.integrable_of_hasCompactSupport (hterm j).2]
  change ∫ g, F g ∂D.μ = _
  rw [hCF E a b D μa μb ν hC F hFc hFs]
  change ∫ ya, ∫ yb, ∫ h, F (splitH a b (ya, yb, h)) ∂ν ∂_ ∂_ = _

  set K : Set (Hf E a b) := ⋃ p, ⋃ q, tsupport (ψ' p q) with hKdef
  have hK : IsCompact K := isCompact_iUnion fun p => isCompact_iUnion fun q => (hψ' p q).2
  have hψK : ∀ p q h, h ∉ K → ψ' p q h = 0 := fun p q h hh =>
    image_eq_zero_of_notMem_tsupport fun hm => hh (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨q, hm⟩⟩)
  have hQK : ∀ ya yb h, h ∉ K → F (splitH a b (ya, yb, h)) = 0 := by
    intro ya yb h hh
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [tens, hFin_splitH, hψK _ _ _ hh, mul_zero, zero_mul]
  set ν' := ν.restrict K
  haveI : IsFiniteMeasure ν' := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hres : ∀ ya yb, ∫ h, F (splitH a b (ya, yb, h)) ∂ν = ∫ h, F (splitH a b (ya, yb, h)) ∂ν' :=
    fun ya yb => (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => hQK ya yb h hh).symm
  simp_rw [hres]
  let A := Measure.pi fun _ : InfinitePlace E => μa
  let B := Measure.pi fun _ : InfinitePlace E => μb
  haveI : SigmaFinite A := inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => μa))
  haveI : SigmaFinite B := inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => μb))
  haveI : IsFiniteMeasureOnCompacts A :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μa))
  haveI : IsFiniteMeasureOnCompacts B :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi fun _ : InfinitePlace E => μb))
  set Q : ((InfinitePlace E → G a) × (InfinitePlace E → G b)) × Hf E a b → ℂ :=
    fun q => F (splitH a b (q.1.1, q.1.2, q.2)) with hQdef
  have hQc : Continuous Q := hFc.comp ((splitH a b).continuous.comp (by fun_prop))
  have hQs : HasCompactSupport Q :=
    hFs.comp_homeomorph ((Homeomorph.prodAssoc _ _ _).trans (splitH a b).toHomeomorph)
  have hQi : Integrable Q ((A.prod B).prod ν') := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact hQc.integrable_of_hasCompactSupport hQs
  have hQh : ∀ h, Integrable (fun p => Q (p, h)) (A.prod B) := fun h =>
    (hQc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (actHcsSlice hQs h)
  have step1 : ∫ ya, ∫ yb, ∫ h, F (splitH a b (ya, yb, h)) ∂ν' ∂B ∂A =
      ∫ h, ∫ ya, ∫ yb, Q ((ya, yb), h) ∂B ∂A ∂ν' := by
    set_option synthInstance.maxHeartbeats 200000 in
      rw [← integral_prod (fun p => ∫ h, Q (p, h) ∂ν') hQi.integral_prod_left,
        integral_integral_swap (f := fun p h => Q (p, h)) hQi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_prod _ (hQh h))
  rw [step1]
  have hpt : ∀ (h : Hf E a b) ya yb, x * splitH a b (ya, yb, h) = x * finH h * (infP a ya, 1) * (1, infP b yb) := by
    intro h ya yb
    have hc : ∀ (n : ℕ) (y : InfinitePlace E → G n) (k : GL (Fin n) (Af E)), infP n y * finGL E n k = finGL E n k * infP n y :=
      fun n y k => infGL_comm _ _
    rw [splitH_apply]
    exact Prod.ext (by simp [finH, hc, mul_assoc]) (by simp [finH, hc, mul_assoc])
  have hX : ∀ (X₀ : H E a b) z (j₁ : IxA Ma), ∀ J, Continuous fun yb : InfinitePlace E → G b => f ((j₁, J), z) (X₀ * (1, infP b yb)) :=
    fun X₀ z j₁ J => (hf _).comp (continuous_const.mul (continuous_const.prodMk (continuous_infP b)))
  have hXa : ∀ (X₀ : H E a b) z (j₂ : IxA Mb), ∀ J, Continuous fun ya : InfinitePlace E → G a => f ((J, j₂), z) (X₀ * (infP a ya, 1)) :=
    fun X₀ z j₂ J => (hf _).comp (continuous_const.mul ((continuous_infP a).prodMk continuous_const))
  have per_h : ∀ h, ∫ ya, ∫ yb, Q ((ya, yb), h) ∂B ∂A =
      (valA va' χa * valA vb' χb) * ∑ z, ψ' i.2 z h * f (i.1, z) (x * finH h) := by
    intro h
    have hQexp : ∀ ya yb, Q ((ya, yb), h) = ∑ z, ψ' i.2 z h * ∑ j₁,
        (∏ v, ent (Ma v) (ka' v (ya v).val) (i.1.1 v) (j₁ v)) * ∑ j₂,
          (∏ v, ent (Mb v) (kb' v (yb v).val) (i.1.2 v) (j₂ v)) *
            f ((j₁, j₂), z) (x * finH h * (infP a ya, 1) * (1, infP b yb)) := by
      intro ya yb
      simp only [hQdef, hFdef, tens, entA, gInf_splitH₁, gInf_splitH₂, hFin_splitH, hpt, Fintype.sum_prod_type,
        Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun j₂ _ => by ring
    have inner : ∀ ya, ∫ yb, Q ((ya, yb), h) ∂B = ∑ z, ψ' i.2 z h * (valA vb' χb * ∑ j₁,
        (∏ v, ent (Ma v) (ka' v (ya v).val) (i.1.1 v) (j₁ v)) * f ((j₁, i.1.2), z) (x * finH h * (infP a ya, 1))) := by
      intro ya
      rw [integral_congr_ae (Filter.Eventually.of_forall (hQexp ya))]
      refine (actLin2 B (fun z => ψ' i.2 z h) (fun j₁ => ∏ v, ent (Ma v) (ka' v (ya v).val) (i.1.1 v) (j₁ v))
        (fun z j₁ yb => ∑ j₂, (∏ v, ent (Mb v) (kb' v (yb v).val) (i.1.2 v) (j₂ v)) *
            f ((j₁, j₂), z) (x * finH h * (infP a ya, 1) * (1, infP b yb)))
        (fun z j₁ => pi_integrable μb (fun v t p q => ent (Mb v) (kb' v t.val) p q)
          (fun J yb => f ((j₁, J), z) (x * finH h * (infP a ya, 1) * (1, infP b yb))) i.1.2
          (fun v p q => mult_ent (hkb' v) p q) (hX _ z j₁))).trans ?_
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [actSide_b hMA μb f kb' vb' T' hkb' χb hf hsm.2 heqb hEig.2 j₁ i.1.2 z (x * finH h * (infP a ya, 1))]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall inner),
      integral_finsetSum _ fun z _ => ((pi_integrable μa (fun v t p q => ent (Ma v) (ka' v t.val) p q)
        (fun J ya => f ((J, i.1.2), z) (x * finH h * (infP a ya, 1))) i.1.1
        (fun v p q => mult_ent (hka' v) p q) (hXa _ z i.1.2)).const_mul _).const_mul _]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_const_mul, integral_const_mul,
      actSide_a hMA μa f ka' va' T' hka' χa hf hsm.1 heqa hEig.1 i.1.1 i.1.2 z (x * finH h)]
    simp only [Prod.mk.eta]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall per_h), integral_const_mul]
  have hcf : Continuous fun h : Hf E a b => finH h :=
    ((continuous_finGL' a).comp continuous_fst).prodMk ((continuous_finGL' b).comp continuous_snd)
  have hzi : ∀ z, Continuous (fun h => ψ' i.2 z h * f (i.1, z) (x * finH h)) ∧
      HasCompactSupport (fun h => ψ' i.2 z h * f (i.1, z) (x * finH h)) := fun z =>
    ⟨(hψ' _ _).1.mul ((hf _).comp (continuous_const.mul hcf)), (hψ' _ _).2.mul_right⟩
  rw [integral_finsetSum _ fun z _ => (hzi z).1.integrable_of_hasCompactSupport (hzi z).2]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by simp [hψK _ _ _ hh]

end Main

end PositivityTheory.Rg.BcB.CG
