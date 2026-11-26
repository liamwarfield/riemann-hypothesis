module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.PhiRootVal

def RootOrZero {K : Type} [Field K] (z : K) : Prop := z = 0 ∨ ∃ n : ℕ, 0 < n ∧ z ^ n = 1

variable {K : Type} [Field K]

theorem RootOrZero.zero : RootOrZero (0 : K) := Or.inl rfl

theorem RootOrZero.one : RootOrZero (1 : K) := Or.inr ⟨1, one_pos, one_pow 1⟩

theorem RootOrZero.mul {z w : K} (hz : RootOrZero z) (hw : RootOrZero w) : RootOrZero (z * w) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl (zero_mul w)
  rcases hw with rfl | ⟨m, hm, hw⟩
  · exact Or.inl (mul_zero z)
  refine Or.inr ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_pow, pow_mul, hz, one_pow, one_mul, mul_comm n m, pow_mul, hw, one_pow]

theorem RootOrZero.inv {z : K} (hz : RootOrZero z) : RootOrZero z⁻¹ := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl inv_zero
  exact Or.inr ⟨n, hn, by rw [inv_pow, hz, inv_one]⟩

theorem RootOrZero.prod {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, RootOrZero (f i)) :
    RootOrZero (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (RootOrZero.one : RootOrZero (1 : K))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem RootOrZero.intOff {z : K} (hz : RootOrZero z) (σ : K →+* ℂ) (S : Finset ℕ) : IntOff S (σ z) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · rw [map_zero]; exact IntOff.zero
  exact IntOff.of_pow hn (by rw [← map_pow, hz, map_one])

theorem addChar_root {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A K) (a : A) : RootOrZero (ψ a) := by
  refine Or.inr ⟨Nat.card A, Nat.card_pos, ?_⟩
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem hom_root {G : Type} [Group G] [Finite G] (χ : G →* Kˣ) (g : G) : RootOrZero ((χ g : Kˣ) : K) := by
  refine Or.inr ⟨Nat.card G, Nat.card_pos, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

section Loc
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_root (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : RootOrZero (LocE.unitV χ a) := by
  unfold LocE.unitV
  split_ifs with h
  · exact hom_root χ _
  · exact RootOrZero.zero

end Loc
end GlobalTheory.PhiRootVal

namespace GlobalTheory.PhiRootVal
variable {K : Type} [Field K]
section Loc2
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem phiQ_root (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    RootOrZero (LocE.PhiQ q ξ k₀ r c' n' c n x) := by
  unfold LocE.PhiQ
  split_ifs
  · exact unitV_root ξ _
  · exact RootOrZero.zero

theorem lamGv_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGv ψ₀ χ r t j M) := by
  unfold LocE.lamGv
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem lamGvS_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGvS ψ₀ χ k₀ r t j M) := by
  unfold LocE.lamGvS
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem phiG_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool)
    (k₀ r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiG q ψ₀ χ sharp k₀ r t j c' n' c n x) := by
  unfold LocE.PhiG
  dsimp only
  split_ifs
  · exact (lamGv_root ψ₀ χ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

theorem phiGS_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x) := by
  unfold LocE.PhiGS
  dsimp only
  split_ifs
  · exact (lamGvS_root ψ₀ χ _ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

end Loc2

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem phiAt_root (sharp : Bool) (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiAt (R := R) Ch mu sharp i P x) := by
  unfold PhiAt
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem phiTop_root (sharp : Bool) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTop (R := R) Ch mu sharp m2 P x) := by
  unfold PhiTop
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

end Chain

theorem phi_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (P : HeightOneSpectrum (𝓞 t.X.E)), (∀ (i : ℕ) x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiAt (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp i P x))) ∧ ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ P
  exact ⟨fun i x => (phiAt_root _ _ _ _ _ x).intOff _ _, fun x => (phiTop_root _ _ _ _ _ x).intOff _ _⟩

end GlobalTheory.PhiRootVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_local_data_integral_off_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (P : HeightOneSpectrum (𝓞 t.X.E)), (∀ (i : ℕ) x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiAt (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp i P x))) ∧ ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x)) := by
  first | exact @GlobalTheory.PhiRootVal.phi_intOff | exact GlobalTheory.PhiRootVal.phi_intOff | (intros; apply GlobalTheory.PhiRootVal.phi_intOff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.Meet

theorem sum_char_conj_mul {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {χ : G → K}
    (h : IsAbsIrrChar χ) (y s : G) :
    (∑ g : G, χ (g * y * g⁻¹ * s)) * χ 1 = (Fintype.card G : K) * χ y * χ s := by
  classical
  have hconj := h.conj
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let j := algebraMap K (AlgebraicClosure K)
  have hj : Function.Injective j := j.injective
  set T : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) := ∑ g : G, ρ (g * y * g⁻¹) with hTdef
  have hT : ∀ a v, T (ρ a v) = ρ a (T v) := by
    intro a v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hTdef, LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft a)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := schur_scalar ρ T hT
  have h1 : ∀ u : G, ∑ g : G, ρ.character (g * y * g⁻¹ * u) = c * ρ.character u := by
    intro u
    have : LinearMap.trace _ _ (T * ρ u) = c * ρ.character u := by
      rw [hc]; simp [Representation.character, Module.End.mul_eq_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.character, map_mul]
  have h2 : j ((Fintype.card G : K) * χ y) = c * j (χ 1) := by
    have := h1 1
    simp only [mul_one, hρ, hconj] at this
    rw [← this]
    simp [j]
  have h3 : j (∑ g : G, χ (g * y * g⁻¹ * s)) = c * j (χ s) := by
    have := h1 s
    simp only [hρ] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, this]
  apply hj
  rw [map_mul, h3, map_mul _ _ (χ s), h2]
  ring

section Op

variable {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
  (σ : K →+* ℂ) (ρ : Representation ℂ G W)

theorem class_sum_apply {χ : G → K} (h : IsAbsIrrChar χ) (h1 : χ 1 ≠ 0) (y : G) (u : W) :
    ∑ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      σ ((Fintype.card G : K) * χ y / χ 1) • ∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e1 : ∀ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      ∑ s : G, σ ((chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s)) • ρ s u := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (g * y * g⁻¹)⁻¹)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  simp only [e1]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_smul, ← map_sum, smul_smul, ← map_mul]
  congr 2
  have e2 : ∀ g : G, (chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s) =
      χ 1 / (Fintype.card G : K) * χ (g * y * g⁻¹ * s⁻¹) := by
    intro g
    rw [coeff_chiIdem]
    congr 1
    have := h.conj s (s⁻¹ * (g * y * g⁻¹))
    rw [_root_.mul_inv_rev, inv_inv, ← this]
    congr 1
    group
  simp only [e2]
  rw [← Finset.mul_sum, coeff_chiIdem]
  have := sum_char_conj_mul h y s⁻¹
  field_simp
  linear_combination this

end Op

def lvlCoef {K G : Type} [Field K] [Group G] (P : Subgroup G) (ψ : P →* Kˣ) (h : P) : K :=
  (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)


open Classical in
theorem coeff_chiIdem_mul_lvlIdem {K G : Type} [Field K] [Group G] [Fintype G] (χ : G → K) (P : Subgroup G)
    (ψ : P →* Kˣ) (t : G) :
    (chiIdem χ * lvlIdem P ψ).coeff t =
      χ 1 / (Fintype.card G : K) * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) := by
  classical
  unfold lvlIdem
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.coeff_mul_single_apply, coeff_chiIdem]
  simp only [lvlCoef, _root_.mul_inv_rev, inv_inv]
  ring

end GlobalTheory.Hk3.Meet

namespace GlobalTheory.Hk3


open GlobalTheory.Hk3.Meet in
theorem exists_level_vector : ∀ {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : K →+* ℂ) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (ρ : Representation ℂ G W)
    (U : Submodule ℂ W), (∀ χ ∈ X, IsAbsIrrChar χ) → (∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0) → (∀ g, U.map (ρ g) ≤ U) →
    U ≠ ⊥ → (∀ u ∈ U, ∑ g, σ ((idemOf X).coeff g) • ρ g u = u) →
    ∃ u ∈ U, u ≠ 0 ∧ ∀ p : P, ρ p u = σ (ψ p : K) • u := by
  intro K G W _ _ _ _ _ _ _ σ X P ψ ρ U hX hne hst hbot hid
  classical
  have hmem : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => hst g (Submodule.mem_map_of_mem hu)

  obtain ⟨u₀, hu₀, hu₀ne⟩ := (Submodule.ne_bot_iff U).1 hbot
  have hsplit : ∑ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ = u₀ := by
    refine Eq.trans ?_ (hid u₀ hu₀)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : (idemOf X).coeff g = ∑ φ ∈ X, (chiIdem φ).coeff g := by
      unfold idemOf
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, e]
  obtain ⟨χ, hχ, hw⟩ : ∃ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu₀ne (by rw [← hsplit]; exact Finset.sum_eq_zero hcon)
  set w₀ := ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ with hw₀
  have hw₀U : w₀ ∈ U := Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hmem g _ hu₀)

  obtain ⟨t, ht⟩ : ∃ t, (chiIdem χ * lvlIdem P ψ).coeff t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne χ hχ (by
      apply MonoidAlgebra.ext
      ext t
      simpa using hcon t)
  rw [coeff_chiIdem_mul_lvlIdem] at ht
  have h1 : χ 1 ≠ 0 := fun e => ht (by simp [e])
  have hc : ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) ≠ 0 := right_ne_zero_of_mul ht
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  set L : W → W := fun w => ∑ h : P, σ (lvlCoef P ψ h) • ρ (h : G) w with hL
  have hLU : ∀ w ∈ U, L w ∈ U := fun w hw => Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (hmem _ _ hw)
  have hLe : ∀ (p : P) w, ρ p (L w) = σ (ψ p : K) • L w := by
    intro p w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hL, map_sum, map_smul, Finset.smul_sum]
    refine (Equiv.sum_comp (Equiv.mulLeft p⁻¹) _).symm.trans (Finset.sum_congr rfl fun h _ => ?_)
    simp only [Equiv.coe_mulLeft]
    have e1 : lvlCoef P ψ (p⁻¹ * h) = (ψ p : K) * lvlCoef P ψ h := by
      simp only [lvlCoef, _root_.mul_inv_rev, inv_inv, map_mul, Units.val_mul]
      ring
    have e2 : ρ (p : G) (ρ ((p⁻¹ * h : P) : G) w) = ρ (h : G) w := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [e1, e2, map_mul, mul_smul]
  by_contra hno
  push_neg at hno
  have hL0 : ∀ w ∈ U, L w = 0 := by
    intro w hw
    by_contra hLw
    obtain ⟨p, hp⟩ := hno _ (hLU w hw) hLw
    exact hp (hLe p w)
  have hz : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) = 0 :=
    Finset.sum_eq_zero fun g _ => by rw [hL0 _ (hmem _ _ hw₀U), map_zero]
  have hz2 : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
      σ ((Fintype.card G : K) / χ 1 * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹)) • w₀ := by
    have e : ∀ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
        ∑ h : P, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ := by
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hL, map_sum, map_smul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Module.End.mul_apply (ρ (h : G)), ← map_mul, ← Module.End.mul_apply (ρ g), ← map_mul]
      simp [mul_assoc]
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ h : P, ∑ g : G, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ =
        σ (lvlCoef P ψ h * ((Fintype.card G : K) * χ ((h : G) * t⁻¹) / χ 1)) • w₀ := by
      intro h
      rw [← Finset.smul_sum, map_mul, mul_smul]
      congr 1
      exact class_sum_apply σ ρ (hX χ hχ) h1 _ u₀
    simp only [e2]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hz2] at hz
  rcases smul_eq_zero.1 hz with h0 | h0
  · exact (mul_ne_zero (div_ne_zero hN h1) hc) ((map_eq_zero σ).1 h0)
  · exact hw h0

end GlobalTheory.Hk3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_vector_goodType_stable_subspace : ∀ {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : K →+* ℂ) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (ρ : Representation ℂ G W) (U : Submodule ℂ W), (∀ χ ∈ X, IsAbsIrrChar χ) → (∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0) → (∀ g, U.map (ρ g) ≤ U) → U ≠ ⊥ → (∀ u ∈ U, ∑ g, σ ((idemOf X).coeff g) • ρ g u = u) → ∃ u ∈ U, u ≠ 0 ∧ ∀ p : P, ρ p u = σ (ψ p : K) • u := by
  first | exact @GlobalTheory.Hk3.exists_level_vector | exact GlobalTheory.Hk3.exists_level_vector | (intros; apply GlobalTheory.Hk3.exists_level_vector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
open Formalism.L2.Col

namespace GlobalTheory.ScalarExtEig

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
  {σ : K →+* ℂ} (j : V →ₛₗ[σ] W)

theorem span_image_span (S : Set V) :
    Submodule.span ℂ (j '' (Submodule.span K S : Set V)) = Submodule.span ℂ (j '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem span_image_mono {U U' : Submodule K V} (h : U ≤ U') :
    Submodule.span ℂ (j '' (U : Set V)) ≤ Submodule.span ℂ (j '' (U' : Set V)) :=
  Submodule.span_mono (Set.image_mono h)

theorem span_image_iSup {κ : Sort*} (U : κ → Submodule K V) :
    Submodule.span ℂ (j '' ((⨆ i, U i : Submodule K V) : Set V))
      = ⨆ i, Submodule.span ℂ (j '' (U i : Set V)) := by
  rw [Submodule.iSup_eq_span, span_image_span, Set.image_iUnion, Submodule.span_iUnion]

theorem span_image_bot : Submodule.span ℂ (j '' ((⊥ : Submodule K V) : Set V)) = ⊥ := by
  simp

theorem span_image_sup (U U' : Submodule K V) :
    Submodule.span ℂ (j '' ((U ⊔ U' : Submodule K V) : Set V))
      = Submodule.span ℂ (j '' (U : Set V)) ⊔ Submodule.span ℂ (j '' (U' : Set V)) := by
  rw [← Submodule.span_eq U, ← Submodule.span_eq U', ← Submodule.span_union, span_image_span,
    Set.image_union, Submodule.span_union, span_image_span, span_image_span]

variable {ι : Type} [Finite ι] (b : Module.Basis ι K V)

include b in
theorem finiteDimensional_of_basis : FiniteDimensional K V := Module.Finite.of_basis b

theorem span_image_top (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) :
    Submodule.span ℂ (j '' ((⊤ : Submodule K V) : Set V)) = ⊤ := by
  rw [eq_top_iff, ← hsp]
  exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨b k, Submodule.mem_top, rfl⟩)

theorem finiteDimensional_W (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) : FiniteDimensional ℂ W :=
  Module.Finite.of_basis (Module.Basis.mk hli hsp.ge)

theorem finrank_W (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) :
    Module.finrank ℂ W = Module.finrank K V := by
  haveI := Fintype.ofFinite ι
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge), Module.finrank_eq_card_basis b]

theorem linearIndependent_comp (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤)
    {κ : Type} {u : κ → V} (hu : LinearIndependent K u) :
    LinearIndependent ℂ (fun k => j (u k)) := by
  haveI := finiteDimensional_of_basis b
  have hs : LinearIndepOn K id (Set.range u) := hu.linearIndepOn_id
  let B := Module.Basis.extend hs
  haveI : Fintype (hs.extend (Set.subset_univ _)) := Fintype.ofFinite _
  have hB : LinearIndependent ℂ (fun l => j (B l)) := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
    · rw [← hsp]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      have h1 : j (b k) ∈ Submodule.span ℂ (j '' (Submodule.span K (Set.range B) : Set V)) := by
        rw [B.span_eq]; exact Submodule.subset_span ⟨b k, Submodule.mem_top, rfl⟩
      rw [span_image_span, ← Set.range_comp] at h1
      exact h1
    · rw [finrank_W j b hli hsp, Module.finrank_eq_card_basis B]
  let f : κ → hs.extend (Set.subset_univ _) := fun k => ⟨u k, Module.Basis.subset_extend hs ⟨k, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hu.injective (congrArg Subtype.val h)
  have := hB.comp f hf
  convert this using 1
  funext k
  simp [B, f, Module.Basis.coe_extend]

theorem finrank_span_image (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (U : Submodule K V) :
    Module.finrank ℂ (Submodule.span ℂ (j '' (U : Set V))) = Module.finrank K U := by
  haveI := finiteDimensional_of_basis b
  let bU := Module.finBasis K U
  have hu : LinearIndependent K (fun i => (bU i : V)) :=
    bU.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hspan : Submodule.span K (Set.range fun i => (bU i : V)) = U := by
    have : (Set.range fun i => (bU i : V)) = U.subtype '' Set.range bU := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bU.span_eq, Submodule.map_subtype_top]
  have h2 : Submodule.span ℂ (j '' (U : Set V))
      = Submodule.span ℂ (Set.range fun i => j (bU i : V)) := by
    conv_lhs => rw [← hspan]
    rw [span_image_span, ← Set.range_comp]; rfl
  rw [h2, finrank_span_eq_card (linearIndependent_comp j b hli hsp hu), Fintype.card_fin]

theorem span_image_inf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (U U' : Submodule K V) :
    Submodule.span ℂ (j '' ((U ⊓ U' : Submodule K V) : Set V))
      = Submodule.span ℂ (j '' (U : Set V)) ⊓ Submodule.span ℂ (j '' (U' : Set V)) := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  refine Submodule.eq_of_le_of_finrank_eq
    (le_inf (span_image_mono j inf_le_left) (span_image_mono j inf_le_right)) ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U U'
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℂ (j '' (U : Set V)))
    (Submodule.span ℂ (j '' (U' : Set V)))
  rw [← span_image_sup] at h2
  simp only [finrank_span_image j b hli hsp] at h2 ⊢
  omega

theorem span_image_finset_inf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) {I : Type} (U : I → Submodule K V)
    (F : Finset I) :
    Submodule.span ℂ (j '' ((F.inf U : Submodule K V) : Set V))
      = F.inf (fun i => Submodule.span ℂ (j '' (U i : Set V))) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp only [Finset.inf_empty]; exact span_image_top j b hsp
  | insert i F hi ih => rw [Finset.inf_insert, Finset.inf_insert, span_image_inf j b hli hsp, ih]

theorem exists_finset_inf_eq_iInf {I : Type} [FiniteDimensional K V] (U : I → Submodule K V) :
    ∃ F : Finset I, F.inf U = ⨅ i, U i := by
  classical
  have hex : ∃ n, ∃ F : Finset I, Module.finrank K ((F.inf U : Submodule K V)) = n := ⟨_, ∅, rfl⟩
  obtain ⟨F, hF⟩ := Nat.find_spec hex
  refine ⟨F, le_antisymm (le_iInf fun i => ?_) (Finset.le_inf fun i _ => iInf_le U i)⟩
  have hle : (insert i F).inf U ≤ F.inf U := Finset.inf_mono (Finset.subset_insert i F)
  have hmin : Nat.find hex ≤ Module.finrank K (((insert i F).inf U : Submodule K V)) := Nat.find_min' hex ⟨_, rfl⟩
  have heq : (insert i F).inf U = F.inf U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact Finset.inf_le (Finset.mem_insert_self i F)

theorem span_image_iInf (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) {I : Type} (U : I → Submodule K V) :
    Submodule.span ℂ (j '' ((⨅ i, U i : Submodule K V) : Set V))
      = ⨅ i, Submodule.span ℂ (j '' (U i : Set V)) := by
  haveI := finiteDimensional_of_basis b
  obtain ⟨F, hF⟩ := exists_finset_inf_eq_iInf U
  refine le_antisymm (le_iInf fun i => span_image_mono j (iInf_le U i)) ?_
  rw [← hF, span_image_finset_inf j b hli hsp]
  exact Finset.le_inf fun i _ => iInf_le _ i

theorem span_image_ker (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (f : Module.End K V)
    (fC : Module.End ℂ W) (hf : ∀ v, j (f v) = fC (j v)) :
    Submodule.span ℂ (j '' (LinearMap.ker f : Set V)) = LinearMap.ker fC := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  have hle : Submodule.span ℂ (j '' (LinearMap.ker f : Set V)) ≤ LinearMap.ker fC := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hv ⊢
    rw [← hf, hv, map_zero]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hr : LinearMap.range fC = Submodule.span ℂ (j '' (LinearMap.range f : Set V)) := by
    rw [LinearMap.range_eq_map, ← span_image_top j b hsp, Submodule.map_span, LinearMap.range_eq_map,
      Submodule.map_coe, Set.image_image, Set.image_image]
    simp_rw [hf]
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker fC
  rw [hr, finrank_span_image j b hli hsp, finrank_W j b hli hsp] at h2
  rw [finrank_span_image j b hli hsp]
  omega

theorem span_image_maxGenEigenspace (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤) (f : Module.End K V)
    (fC : Module.End ℂ W) (hf : ∀ v, j (f v) = fC (j v)) (a : K) :
    Submodule.span ℂ (j '' (f.maxGenEigenspace a : Set V)) = fC.maxGenEigenspace (σ a) := by
  haveI := finiteDimensional_of_basis b
  haveI := finiteDimensional_W j b hli hsp
  have key : ∀ (k : ℕ) (v : V),
      ((fC - σ a • (1 : Module.End ℂ W)) ^ k) (j v) = j (((f - a • (1 : Module.End K V)) ^ k) v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smulₛₗ, hf]
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat,
    Module.End.genEigenspace_nat, finrank_W j b hli hsp]
  exact span_image_ker j b hli hsp _ _ (fun v => (key _ v).symm)

end GlobalTheory.ScalarExtEig

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


open GlobalTheory.ScalarExtEig in
theorem span_image_eigAt_of_basis : ∀ {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V) (opC : I → Module.End ℂ W), LinearIndependent ℂ (fun k => j (b k)) → Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ → (∀ i x, j (op i x) = opC i (j x)) → (∀ s : I → K, Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) = Formalism.L2.Col.eigAt opC (fun i => σ (s i))) ∧ (∀ Q : (I → K) → Prop, Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op Q : Set V)) = Formalism.L2.Col.eigSum opC (fun x => ∃ s, Q s ∧ x = fun i => σ (s i))) ∧ (Formalism.L2.Col.PairComm op → Formalism.L2.Col.SplitOver op → ∀ x, Formalism.L2.Col.Occurs opC x → ∃ s, Formalism.L2.Col.Occurs op s ∧ x = fun i => σ (s i)) := by
  intro K V W I ι _ _ _ _ _ _ σ j b op opC hli hsp hop
  have h1 : ∀ s : I → K, Submodule.span ℂ (j '' (eigAt op s : Set V))
      = eigAt opC (fun i => σ (s i)) := by
    intro s
    rw [eigAt, span_image_iInf j b hli hsp, eigAt]
    exact iInf_congr fun i => span_image_maxGenEigenspace j b hli hsp (op i) (opC i) (hop i) (s i)
  refine ⟨h1, fun Q => ?_, fun hc hs x hx => ?_⟩
  · unfold eigSum
    simp_rw [span_image_iSup, h1]
    apply le_antisymm
    · exact iSup₂_le fun s hs => le_iSup₂_of_le (f := fun (y : I → ℂ) (_ : ∃ s, Q s ∧ y = fun i => σ (s i)) => eigAt opC y) _ ⟨s, hs, rfl⟩ le_rfl
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨s, hs, rfl⟩ := hy
      exact le_iSup₂_of_le (f := fun (s : I → K) (_ : Q s) => eigAt opC (fun i => σ (s i))) s hs le_rfl
  · by_contra hno
    push_neg at hno
    have hcC : PairComm opC := by
      intro i k
      show opC i * opC k = opC k * opC i
      refine LinearMap.ext_on_range hsp fun m => ?_
      have := congrArg (fun g => j (g (b m))) (hc i k).eq
      simpa [Module.End.mul_apply, hop] using this
    haveI := finiteDimensional_of_basis b
    have htop : (⊤ : Submodule ℂ W) ≤ ⨆ (y : I → ℂ) (_ : y ≠ x), eigAt opC y := by
      rw [← span_image_top j b hsp, ← iSup_eigAt_eq_top hc hs, span_image_iSup]
      refine iSup_le fun s => ?_
      by_cases hs0 : Occurs op s
      · rw [h1]
        exact le_iSup₂_of_le (f := fun (y : I → ℂ) (_ : y ≠ x) => eigAt opC y) _ (hno s hs0).symm le_rfl
      · rw [Occurs, not_not] at hs0
        rw [hs0, span_image_bot]
        exact bot_le
    exact hx (disjoint_top.1 (((iSupIndep_eigAt hcC) x).mono_right htop))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjoint
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweSwap

variable {L : Type} [Field L]

theorem cT_cT {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {a b : Type} (A : Matrix a b L) :
    Formalism.UG.cT σ (Formalism.UG.cT σ A) = A := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cT_add (σ : L →+* L) {a b : Type} (A B : Matrix a b L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_zero (σ : L →+* L) {a b : Type} : Formalism.UG.cT σ (0 : Matrix a b L) = 0 := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_herm {σ : L →+* L} {a : ℕ} {J : Matrix (Fin a) (Fin a) L} (h : ∀ i j, σ (J i j) = J j i) :
    Formalism.UG.cT σ J = J := by
  ext i j; simp [Formalism.UG.cT, h]

theorem inv_mul_cl {a : ℕ} {β : Type} (J : GL (Fin a) L) (Z : Matrix (Fin a) β L) :
    ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((J : Matrix (Fin a) (Fin a) L) * Z) = Z := by
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem mul_inv_cl {a : ℕ} {β : Type} (J : GL (Fin a) L) (Z : Matrix (Fin a) β L) :
    (J : Matrix (Fin a) (Fin a) L) * (((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * Z) = Z := by
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem cT_inv_herm {σ : L →+* L} {a : ℕ} (J : GL (Fin a) L) (h : Formalism.UG.cT σ (J : Matrix (Fin a) (Fin a) L) = J) :
    Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) = (J⁻¹ : GL (Fin a) L) := by
  have h1 : Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (J : Matrix (Fin a) (Fin a) L) = 1 := by
    conv_lhs => rw [← h]
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc _ = Formalism.UG.cT σ ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((J : Matrix (Fin a) (Fin a) L) *
        ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) := by rw [Units.mul_inv, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem trace_cT (σ : L →+* L) {a : ℕ} (A : Matrix (Fin a) (Fin a) L) :
    σ (Matrix.trace A) = Matrix.trace (Formalism.UG.cT σ A) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.UG.cT, Matrix.trace, map_sum]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (X : Matrix (Fin n) (Fin n') L) :
    Matrix (Fin n') (Fin n) L :=
  ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ X * (JS : Matrix (Fin n) (Fin n) L)

theorem adj_add (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (X Y : Matrix (Fin n) (Fin n') L) :
    adj σ JS JT (X + Y) = adj σ JS JT X + adj σ JS JT Y := by
  simp [adj, cT_add, Matrix.mul_add, Matrix.add_mul]

theorem adj_zero (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) :
    adj σ JS JT (0 : Matrix (Fin n) (Fin n') L) = 0 := by
  simp [adj, cT_zero]

theorem adj_pre {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L)
    (x : Matrix (Fin n') (Fin n) L) :
    adj σ JS JT (Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))) = x := by
  simp only [adj, cT_cT hσ, Matrix.mul_assoc, inv_mul_cl, Units.inv_mul, Matrix.mul_one]

theorem locH_adj {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {δ : L} (hδ : σ δ = -δ) {n n' : ℕ} (JS : GL (Fin n) L)
    (JT : GL (Fin n') L) (hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS)
    (hTi : Formalism.UG.cT σ ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = (JT⁻¹ : GL (Fin n') L))
    (X Y : Matrix (Fin n) (Fin n') L) :
    σ (locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y)) = locH σ (-δ) JT JS X Y := by
  have hc : ∀ {a b : Type} (Z : Matrix a b L), (Z.map σ)ᵀ = Formalism.UG.cT σ Z := fun _ => rfl
  simp only [locH, hc, adj, Formalism.UG.cT_mul, cT_cT hσ, hS, hTi, Matrix.mul_assoc, inv_mul_cl, map_mul, hδ, trace_cT]
  congr 1
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.Hk3.HoweSwap

namespace GlobalTheory.Hk3.HoweSwap

variable {L : Type} [Field L]

theorem adj_norm (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (h : GL (Fin n) L) (g : GL (Fin n') L)
    (hh : Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (h : Matrix (Fin n) (Fin n) L) = JS)
    (hg : Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (JT : Matrix (Fin n') (Fin n') L) *
      ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) = JT)
    (X : Matrix (Fin n) (Fin n') L) :
    adj σ JS JT ((h : Matrix (Fin n) (Fin n) L) * X * ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) =
      (g : Matrix (Fin n') (Fin n') L) * adj σ JS JT X * ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  have e2 : Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) =
      (JS : Matrix (Fin n) (Fin n) L) * ((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    conv_rhs => rw [← hh]
    rw [Matrix.mul_assoc _ (h : Matrix (Fin n) (Fin n) L), Units.mul_inv, Matrix.mul_one]
  have e1 : ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) =
      (g : Matrix (Fin n') (Fin n') L) * ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) := by
    have e3 : Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (JT : Matrix (Fin n') (Fin n') L) =
        (JT : Matrix (Fin n') (Fin n') L) * (g : Matrix (Fin n') (Fin n') L) := by
      conv_rhs => rw [← hg]
      rw [Matrix.mul_assoc _ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L), Units.inv_mul, Matrix.mul_one]
    calc _ = ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * (Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
          ((JT : Matrix (Fin n') (Fin n') L) * ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L))) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc (Formalism.UG.cT σ _), e3, Matrix.mul_assoc, inv_mul_cl]
  unfold adj
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Formalism.UG.cT σ ((g⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L)) *
        Formalism.UG.cT σ X * (Formalism.UG.cT σ (h : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e1, e2]; simp only [Matrix.mul_assoc]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem intMat_mul {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : A ∈ HoweDuality.intMat L a b) (hB : B ∈ HoweDuality.intMat L b c) : A * B ∈ HoweDuality.intMat L a c := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem intMat_cT {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : A ∈ HoweDuality.intMat L a b) : Formalism.UG.cT σ A ∈ HoweDuality.intMat L b a := fun i j => by
  have h := hA j i
  simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at h ⊢
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hv]
  exact h

theorem glint_int {a : ℕ} {J : GL (Fin a) L} (h : J ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L)) :
    (J : Matrix (Fin a) (Fin a) L) ∈ HoweDuality.intMat L a a ∧
      ((J⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) ∈ HoweDuality.intMat L a a := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp [Formalism.UG.bc]
  · rw [← map_inv]; simp [Formalism.UG.bc]

end GlobalTheory.Hk3.HoweSwap

namespace GlobalTheory.Hk3.HoweSwap

theorem locPair_swap : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω →
    GlobalTheory.Hk3.LocPair ϖ σ q (-δ) JT JS ψ
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)))
      (ω.comp (MulEquiv.prodComm : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) × Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) ≃* _).toMonoidHom) ∧
    (∀ s : M, GlobalTheory.Hk3.LocVac ρ s → GlobalTheory.Hk3.LocVac
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L))) s) ∧
    ∀ s : M, Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n') L =>
      ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)) s) = ⊤ := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have hσ : ∀ x, σ (σ x) = x := hp.unr.1
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hp.unr.2.1
  have hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := cT_herm hp.hermS
  have hT : Formalism.UG.cT σ (JT : Matrix (Fin n') (Fin n') L) = JT := cT_herm hp.hermT
  have hTi := cT_inv_herm JT hT
  obtain ⟨hS1, hS2⟩ := glint_int hp.intS
  obtain ⟨hT1, hT2⟩ := glint_int hp.intT
  have hai : ∀ X : Matrix (Fin n) (Fin n') L, X ∈ HoweDuality.intMat L n n' → adj σ JS JT X ∈ HoweDuality.intMat L n' n :=
    fun X hX => intMat_mul (intMat_mul hT2 (intMat_cT hv hX)) hS1
  have hprei : ∀ x : Matrix (Fin n') (Fin n) L, x ∈ HoweDuality.intMat L n' n →
      Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∈ HoweDuality.intMat L n n' :=
    fun x hx => intMat_cT hv (intMat_mul (intMat_mul hT1 hx) hS2)
  have hvac : ∀ s, LocVac ρ s → LocVac (fun X => ρ (adj σ JS JT X)) s := fun s hs u hu => hs _ (hai u hu)
  have hvac' : ∀ s, LocVac (fun X => ρ (adj σ JS JT X)) s → LocVac ρ s := fun s hs u hu => by
    have h1 := hs _ (hprei u hu)
    simp only [adj_pre hσ] at h1
    exact h1
  have hrange : ∀ s : M, Set.range (fun x => ρ x s) ⊆ Set.range (fun X => ρ (adj σ JS JT X) s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨(Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))), by simp only [adj_pre hσ]⟩
  refine ⟨?_, hvac, fun s hs => ?_⟩
  · refine ⟨hp.unr, hp.odd, hp.intT, hp.intS, hp.hermT, hp.hermS,
      ⟨by rw [Valuation.map_neg]; exact hp.delta.1, by rw [map_neg, hp.delta.2]⟩, hp.psi_int, hp.psi_ne, ?_, ?_, ?_, ?_, ?_⟩
    · show ρ (adj σ JS JT 0) = 1
      rw [adj_zero]; exact hp.rho_zero
    · intro X Y
      show ρ (adj σ JS JT X) * ρ (adj σ JS JT Y) = _ • ρ (adj σ JS JT (X + Y))
      have hb := locH_adj hσ hp.delta.2 JS JT hS hTi X Y
      have ha : locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y) = σ (locH σ (-δ) JT JS X Y) := by rw [← hb, hσ]
      have key : locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y) + σ (locH σ δ JS JT (adj σ JS JT X) (adj σ JS JT Y)) =
          locH σ (-δ) JT JS X Y + σ (locH σ (-δ) JT JS X Y) := by
        rw [hb]; linear_combination ha
      rw [hp.rho_mul, adj_add, key]
    · rw [eq_top_iff, ← hp.span]
      apply Submodule.span_mono
      rintro w ⟨x, s, hs, rfl⟩
      refine ⟨(Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))), s, hvac s hs, ?_⟩
      show ρ x s = ρ (adj σ JS JT (Formalism.UG.cT σ ((JT : Matrix (Fin n') (Fin n') L) * x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) s
      rw [adj_pre hσ]
    · intro g h x
      show ω (h, g) * ρ (adj σ JS JT _) = ρ (adj σ JS JT _) * ω (h, g)
      rw [hp.norm h g, adj_norm σ JS JT (h : GL (Fin n) L) (g : GL (Fin n') L) h.2 ((Formalism.UG.UJ σ _).inv_mem g.2)]
    · intro g h hg hh s hs
      exact hp.fix h g hh hg s (hvac' s hs)
  · rw [eq_top_iff, ← hs]
    exact Submodule.span_mono (hrange s)

end GlobalTheory.Hk3.HoweSwap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalDualPairSwapHermitianAdjointStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedLocalDualPair_swap_hermitianAdjoint : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω →
    GlobalTheory.Hk3.LocPair ϖ σ q (-δ) JT JS ψ
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)))
      (ω.comp (MulEquiv.prodComm : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) × Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) ≃* _).toMonoidHom) ∧
    (∀ s : M, GlobalTheory.Hk3.LocVac ρ s → GlobalTheory.Hk3.LocVac
      (fun X : Matrix (Fin n) (Fin n') L => ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L))) s) ∧
    ∀ s : M, Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → Submodule.span ℂ (Set.range fun X : Matrix (Fin n) (Fin n') L =>
      ρ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * Matrix.transpose (X.map σ) * (JS : Matrix (Fin n) (Fin n) L)) s) = ⊤ := by
  first | exact @GlobalTheory.Hk3.HoweSwap.locPair_swap | exact GlobalTheory.Hk3.HoweSwap.locPair_swap | (intros; apply GlobalTheory.Hk3.HoweSwap.locPair_swap <;> assumption)
end
end
