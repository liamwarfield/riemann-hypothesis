module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqProductDatumThetaConjugateHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeIffFrameAdjointIsIntegralMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeIffFrameAdjointIsIntegralMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.HalfLatFrames

theorem halfLat_iff_isIntM : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x →
  (x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx
  have hR : GlobalTheory.Hk3.Core R F := hL.1
  have hPT : PrimeToHost R t := hL.2.1
  obtain ⟨cV, hcV⟩ := hR.lev.βV i
  obtain ⟨cW, hcW⟩ := hR.lev.βW i
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have hP : ∀ PP ∈ R.Pg ∪ R.Q t,
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hmem
    refine hPT PP (Finset.mem_union.1 hPP) ?_
    have : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) * (D.host.d : 𝓞 D.host.E) := by
      push_cast; ring
    rw [this]
    exact PP.asIdeal.mul_mem_right _ hmem
  constructor
  · intro hmem
    exact GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) sV sW hcV.1 hcW.1
      (R.Pg ∪ R.Q t) e he hP x hmem hx
  · intro hint
    exact GlobalTheory.T.idempotent_sum_self_dual_frames_bound D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) sV sW hcV.1 hcW.1
      (R.Pg ∪ R.Q t) e he hP x hx hint

end GlobalTheory.HalfLatFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeIffFrameAdjointIsIntegralMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfLattice_iff_frameAdjoint_isIntegralMatrix : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → ∀ x : WO (Vc D i) (Wc D i), IsHalf (cA D e) x →
  (x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) := by
  first | exact @GlobalTheory.HalfLatFrames.halfLat_iff_isIntM | exact GlobalTheory.HalfLatFrames.halfLat_iff_isIntM | (intros; apply GlobalTheory.HalfLatFrames.halfLat_iff_isIntM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwiner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory

theorem finite_plancherel_schrodinger_intertwiner :
∀ {X Aψ G : Type} [AddCommGroup X] [AddCommGroup Aψ] [AddCommGroup G] [Fintype G]
  (ψ : AddChar Aψ ℂ) (B : X → X → Aψ) (Λc : AddSubgroup X) (red : Λc →+ G)
  (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hs : X → (X → ℂ) → (X → ℂ)) (SB : (X → ℂ) → Prop) (Hd : X → Prop)
  (Th : (X → ℂ) → Prop) (ip : (X → ℂ) → (X → ℂ) → ℂ) (f₀ : X → ℂ) (Gd : G → ℂ),
  Function.Surjective red →
  (∀ t k y, B (t + k) y = B t y + B k y) →
  (∀ Ψ : X → ℂ, (∀ t, Ψ t ≠ 0 → t ∈ Λc) → (∀ t, ∀ u ∈ Λc, Ψ (t + Fintype.card G • u) = Ψ t) → SB Ψ) →
  (∀ Φ, SB Φ → ∀ x ∈ Λc, T (fun t => Φ (t + x)) = hs x (T Φ)) →
  (∀ Φ, SB Φ → ∀ y, Hd y → T (fun t => ψ (B t y) * Φ t) = hs y (T Φ)) →
  T (fun t => if t ∈ Λc then 1 else 0) = f₀ →
  (∀ x : Λc, red x ≠ 0 → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ ψ (B x y) ≠ 1) →
  (∀ w (a : ℂ) (f₁ f₂ : X → ℂ), hs w (a • f₁ + f₂) = a • hs w f₁ + hs w f₂) →
  (∀ (a : ℂ) f₁ f₂, Th f₁ → Th f₂ → Th (a • f₁ + f₂)) →
  (∀ w f, Th f → Th (hs w f)) →
  (∀ (a : ℂ) f₁ f₂ g, Th f₁ → Th f₂ → Th g → ip (a • f₁ + f₂) g = a * ip f₁ g + ip f₂ g) →
  (∀ f g, Th f → Th g → ip g f = starRingEnd ℂ (ip f g)) →
  (∀ w f₁ f₂, Th f₁ → Th f₂ → ip (hs w f₁) (hs w f₂) = ip f₁ f₂) →
  Th f₀ → ip f₀ f₀ = 1 →
  ip (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) =
    ((∑ g, ‖Gd g‖ ^ 2 : ℝ) : ℂ) / (Fintype.card G : ℂ) := by
  intro X Aψ G _ _ _ _ ψ B Λc red T hs SB Hd Th ip f₀ Gd hsurj hB hSB htr hmod hf₀ hwit hslin hThlin
    hThhs hiplin hipconj hiphs hThf₀ hip₀
  obtain ⟨rep, hrep⟩ : ∃ rep : G → Λc, ∀ c, red (rep c) = c :=
    ⟨Function.surjInv hsurj, Function.surjInv_eq hsurj⟩
  obtain ⟨ind, hind⟩ : ∃ ind : G → X → ℂ, ∀ c t, ind c t =
      if h : t ∈ Λc then (if red ⟨t, h⟩ = c then (1:ℂ) else 0) else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : G → X → ℂ, ∀ c, g c = T (ind c) := ⟨_, fun _ => rfl⟩
  obtain ⟨χ, hχd⟩ : ∃ χ : X → G → ℂ, ∀ y c, χ y c = ψ (B (rep c) y) := ⟨_, fun _ _ => rfl⟩
  have hB0 : ∀ y, B 0 y = 0 := fun y => by simpa using hB 0 0 y
  have hBn : ∀ (m : ℕ) t y, B (m • t) y = m • B t y := by
    intro m t y
    induction m with
    | zero => simp [hB0]
    | succ m ih => rw [succ_nsmul, hB, ih, succ_nsmul]
  have hχ : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ t : Λc, ψ (B t y) = χ y (red t) := by
    intro y hy t
    have hk : red (t - rep (red t)) = 0 := by rw [map_sub, hrep, sub_self]
    have ht : (t : X) = ((t - rep (red t) : Λc) : X) + (rep (red t) : X) := by simp
    rw [ht, hB, AddChar.map_add_eq_mul, hy _ hk, one_mul, hχd]
  have hχpow : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, χ y c ^ Fintype.card G = 1 := by
    intro y hy c
    rw [hχd, ← AddChar.map_nsmul_eq_pow, ← hBn]
    have := hy (Fintype.card G • rep c) (by rw [map_nsmul, card_nsmul_eq_zero])
    simpa using this
  have hχnorm : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c, ‖χ y c‖ = 1 :=
    fun y hy c => Complex.norm_eq_one_of_pow_eq_one (hχpow y hy c) Fintype.card_ne_zero
  have hχconj : ∀ y, (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c,
      starRingEnd ℂ (χ y c) * χ y c = 1 := by
    intro y hy c
    rw [Complex.conj_mul', hχnorm y hy c]; simp
  have hsep : ∀ c d, c ≠ d → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ χ y c ≠ χ y d := by
    intro c d hcd
    obtain ⟨y, hHd, hy, hne⟩ := hwit (rep (c - d)) (by rw [hrep]; exact sub_ne_zero.mpr hcd)
    refine ⟨y, hHd, hy, fun heq => hne ?_⟩
    have h1 := hχ y hy (rep (c - d) + rep d)
    have hr : red (rep (c - d) + rep d) = c := by rw [map_add (f := _), hrep, hrep, sub_add_cancel]
    rw [hr, AddSubgroup.coe_add, hB, AddChar.map_add_eq_mul, ← hχd y d, heq] at h1
    have h0 : χ y d ≠ 0 := fun h => by simpa [h] using hχnorm y hy d
    exact mul_right_cancel₀ h0 (h1.trans (one_mul _).symm)
  have hSBind : ∀ c, SB (ind c) := by
    intro c
    apply hSB
    · intro t ht
      by_contra hmem
      exact ht (by rw [hind, dite_eq_right hmem])
    · intro t u hu
      have hnu : Fintype.card G • u ∈ Λc := Λc.nsmul_mem hu _
      by_cases ht : t ∈ Λc
      · have ht' : t + Fintype.card G • u ∈ Λc := Λc.add_mem ht hnu
        have he : red ⟨t + Fintype.card G • u, ht'⟩ = red ⟨t, ht⟩ := by
          have : (⟨t + Fintype.card G • u, ht'⟩ : Λc) = ⟨t, ht⟩ + Fintype.card G • ⟨u, hu⟩ :=
            Subtype.ext (by simp)
          rw [this, map_add (f := _), map_nsmul, card_nsmul_eq_zero, add_zero]
        rw [hind, hind, dite_eq_left ht, dite_eq_left ht', he]
      · have ht' : t + Fintype.card G • u ∉ Λc := fun h => ht (by simpa using Λc.sub_mem h hnu)
        rw [hind, hind, dite_eq_right ht, dite_eq_right ht']
  have hmodg : ∀ y, Hd y → (∀ k : Λc, red k = 0 → ψ (B k y) = 1) → ∀ c,
      hs y (g c) = χ y c • g c := by
    intro y hHd hy c
    rw [hg, ← hmod (ind c) (hSBind c) y hHd, ← map_smul]
    congr 1
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, hind]
    by_cases ht : t ∈ Λc
    · rw [dite_eq_left ht]
      by_cases hr : red ⟨t, ht⟩ = c
      · rw [ite_eq_left hr, mul_one, mul_one, ← hr]; exact hχ y hy ⟨t, ht⟩
      · rw [ite_eq_right hr]; simp
    · rw [dite_eq_right ht]; simp
  have htrg : ∀ c, hs (rep c) (g c) = g 0 := by
    intro c
    rw [hg, hg, ← htr (ind c) (hSBind c) (rep c) (rep c).2]
    congr 1
    funext t
    rw [hind, hind]
    by_cases ht : t ∈ Λc
    · have ht' : t + (rep c : X) ∈ Λc := Λc.add_mem ht (rep c).2
      have he : red ⟨t + rep c, ht'⟩ = red ⟨t, ht⟩ + c := by
        have : (⟨t + rep c, ht'⟩ : Λc) = ⟨t, ht⟩ + rep c := Subtype.ext (by simp)
        rw [this, map_add (f := _), hrep]
      rw [dite_eq_left ht, dite_eq_left ht', he]
      simp
    · have ht' : t + (rep c : X) ∉ Λc := fun h => ht (by simpa using Λc.sub_mem h (rep c).2)
      rw [dite_eq_right ht, dite_eq_right ht']
  have hTh0 : Th 0 := by simpa using hThlin (-1) f₀ f₀ hThf₀ hThf₀
  have hThsmul : ∀ a f, Th f → Th (a • f) := fun a f hf => by simpa using hThlin a f 0 hf hTh0
  have hhs0 : ∀ w, hs w 0 = 0 := fun w => by simpa using hslin w 1 0 0
  have hThsum : ∀ (a : G → ℂ) (s : Finset G), (∀ c ∈ s, Th (g c)) → Th (∑ c ∈ s, a c • g c) := by
    intro a s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using hTh0
    | @insert d s hds ih =>
      intro h
      rw [Finset.sum_insert hds]
      exact hThlin _ _ _ (h d (Finset.mem_insert_self _ _))
        (ih fun c hc => h c (Finset.mem_insert_of_mem hc))
  have hsSum : ∀ w (a : G → ℂ) (s : Finset G),
      hs w (∑ c ∈ s, a c • g c) = ∑ c ∈ s, a c • hs w (g c) := by
    intro w a s
    induction s using Finset.induction_on with
    | empty => simpa using hhs0 w
    | @insert d s hds ih => rw [Finset.sum_insert hds, Finset.sum_insert hds, hslin, ih]
  have hf0sum : f₀ = ∑ c, g c := by
    rw [← hf₀]
    simp only [hg]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    congr 1
    funext t
    rw [Finset.sum_apply]
    simp only [hind]
    by_cases ht : t ∈ Λc
    · simp [ht]
    · simp [ht]
  have hΦsum : (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) = ∑ c, Gd c • g c := by
    simp only [hg, ← map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    congr 1
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hind]
    by_cases ht : t ∈ Λc
    · simp [ht]
    · simp [ht]
  have hThg : ∀ c, Th (g c) := by
    intro c
    have key : ∀ S : Finset G, c ∉ S →
        ∃ a : G → ℂ, a c = 1 ∧ (∀ e ∈ S, a e = 0) ∧ Th (∑ e, a e • g e) := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; exact ⟨fun _ => 1, rfl, by simp, by simpa [hf0sum] using hThf₀⟩
      | @insert d S hdS ih =>
        intro hc
        have hcS : c ∉ S := fun h => hc (Finset.mem_insert_of_mem h)
        have hcd : c ≠ d := fun h => hc (h ▸ Finset.mem_insert_self d S)
        obtain ⟨a, ha1, ha0, hTh⟩ := ih hcS
        obtain ⟨y, hHd, hy, hne⟩ := hsep c d hcd
        have hk : χ y c - χ y d ≠ 0 := sub_ne_zero.mpr hne
        refine ⟨fun e => a e * ((χ y e - χ y d) / (χ y c - χ y d)), ?_, ?_, ?_⟩
        · show a c * ((χ y c - χ y d) / (χ y c - χ y d)) = 1
          rw [ha1, one_mul, div_self hk]
        · intro e he
          rcases Finset.mem_insert.mp he with rfl | he
          · simp
          · simp [ha0 e he]
        · have hrw : ∑ e, (a e * ((χ y e - χ y d) / (χ y c - χ y d))) • g e =
              (χ y c - χ y d)⁻¹ • hs y (∑ e, a e • g e) +
                (-(χ y d) / (χ y c - χ y d)) • ∑ e, a e • g e := by
            rw [hsSum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [hmodg y hHd hy e, smul_smul, smul_smul, smul_smul, ← add_smul]
            congr 1
            field_simp
            ring
          rw [hrw]
          exact hThlin _ _ _ (hThhs y _ hTh) (hThsmul _ _ hTh)
    obtain ⟨a, ha1, ha0, hTh⟩ := key (Finset.univ.erase c) (by simp)
    have : ∑ e, a e • g e = g c := by
      rw [Finset.sum_eq_single c]
      · rw [ha1, one_smul]
      · intro e _ he; rw [ha0 e (by simp [he]), zero_smul]
      · simp
    rwa [this] at hTh
  have hip0 : ∀ h, Th h → ip 0 h = 0 := fun h hh => by simpa using hiplin 1 0 0 h hTh0 hTh0 hh
  have hipsL : ∀ a f h, Th f → Th h → ip (a • f) h = a * ip f h := fun a f h hf hh => by
    simpa [hip0 h hh] using hiplin a f 0 h hf hTh0 hh
  have hipsR : ∀ a f h, Th f → Th h → ip f (a • h) = starRingEnd ℂ a * ip f h :=
    fun a f h hf hh => by
      rw [hipconj (a • h) f (hThsmul a h hh) hf, hipsL a h f hh hf, map_mul, ← hipconj h f hh hf]
  have hipsumL : ∀ h, Th h → ∀ (a : G → ℂ) (s : Finset G),
      ip (∑ c ∈ s, a c • g c) h = ∑ c ∈ s, a c * ip (g c) h := by
    intro h hh a s
    induction s using Finset.induction_on with
    | empty => simpa using hip0 h hh
    | @insert d s hds ih =>
      rw [Finset.sum_insert hds, Finset.sum_insert hds,
        hiplin _ _ _ _ (hThg d) (hThsum a s fun c _ => hThg c) hh, ih]
  have horth : ∀ c d, c ≠ d → ip (g c) (g d) = 0 := by
    intro c d hcd
    obtain ⟨y, hHd, hy, hne⟩ := hsep c d hcd
    have h1 := hiphs y (g c) (g d) (hThg c) (hThg d)
    rw [hmodg y hHd hy c, hmodg y hHd hy d, hipsL _ _ _ (hThg c) (hThsmul _ _ (hThg d)),
      hipsR _ _ _ (hThg c) (hThg d)] at h1
    have hk : χ y c * starRingEnd ℂ (χ y d) ≠ 1 := by
      intro h
      apply hne
      have := congrArg (· * χ y d) h
      simp only [mul_assoc, hχconj y hy d, mul_one, one_mul] at this
      exact this
    have : (1 - χ y c * starRingEnd ℂ (χ y d)) * ip (g c) (g d) = 0 := by
      linear_combination (-1 : ℂ) * h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hk
    · exact h
  have hdiag : ∀ c, ip (g c) (g c) = ip (g 0) (g 0) := by
    intro c
    rw [← htrg c, hiphs _ _ _ (hThg c) (hThg c)]
  have hgram : ∀ a b : G → ℂ, ip (∑ e, a e • g e) (∑ e, b e • g e) =
      (∑ e, a e * starRingEnd ℂ (b e)) * ip (g 0) (g 0) := by
    intro a b
    have hS : Th (∑ e, b e • g e) := hThsum b _ fun c _ => hThg c
    rw [hipsumL _ hS a Finset.univ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hipconj _ _ hS (hThg e), hipsumL _ (hThg e) b Finset.univ,
      Finset.sum_eq_single e (fun d _ hde => by rw [horth d e hde, mul_zero]) (by simp),
      map_mul, hdiag e, ← hipconj _ _ (hThg 0) (hThg 0)]
    ring
  have hD : ip (g 0) (g 0) = 1 / (Fintype.card G : ℂ) := by
    have h1 := hgram (fun _ => 1) (fun _ => 1)
    simp only [one_smul, map_one, mul_one, Finset.sum_const, Finset.card_univ] at h1
    rw [← hf0sum, hip₀] at h1
    have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [eq_div_iff hc]
    rw [h1]; simp [mul_comm]
  rw [hΦsum, hgram, hD]
  have hn : ∀ z : ℂ, z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hn, Complex.ofReal_sum]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlancherelSchrodingerIntertwinerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_plancherel_schrodinger_intertwiner_alt : ∀ {X Aψ G : Type} [AddCommGroup X] [AddCommGroup Aψ] [AddCommGroup G] [Fintype G]
  (ψ : AddChar Aψ ℂ) (B : X → X → Aψ) (Λc : AddSubgroup X) (red : Λc →+ G)
  (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hs : X → (X → ℂ) → (X → ℂ)) (SB : (X → ℂ) → Prop) (Hd : X → Prop)
  (Th : (X → ℂ) → Prop) (ip : (X → ℂ) → (X → ℂ) → ℂ) (f₀ : X → ℂ) (Gd : G → ℂ),
  Function.Surjective red →
  (∀ t k y, B (t + k) y = B t y + B k y) →
  (∀ Ψ : X → ℂ, (∀ t, Ψ t ≠ 0 → t ∈ Λc) → (∀ t, ∀ u ∈ Λc, Ψ (t + Fintype.card G • u) = Ψ t) → SB Ψ) →
  (∀ Φ, SB Φ → ∀ x ∈ Λc, T (fun t => Φ (t + x)) = hs x (T Φ)) →
  (∀ Φ, SB Φ → ∀ y, Hd y → T (fun t => ψ (B t y) * Φ t) = hs y (T Φ)) →
  T (fun t => if t ∈ Λc then 1 else 0) = f₀ →
  (∀ x : Λc, red x ≠ 0 → ∃ y, Hd y ∧ (∀ k : Λc, red k = 0 → ψ (B k y) = 1) ∧ ψ (B x y) ≠ 1) →
  (∀ w (a : ℂ) (f₁ f₂ : X → ℂ), hs w (a • f₁ + f₂) = a • hs w f₁ + hs w f₂) →
  (∀ (a : ℂ) f₁ f₂, Th f₁ → Th f₂ → Th (a • f₁ + f₂)) →
  (∀ w f, Th f → Th (hs w f)) →
  (∀ (a : ℂ) f₁ f₂ g, Th f₁ → Th f₂ → Th g → ip (a • f₁ + f₂) g = a * ip f₁ g + ip f₂ g) →
  (∀ f g, Th f → Th g → ip g f = starRingEnd ℂ (ip f g)) →
  (∀ w f₁ f₂, Th f₁ → Th f₂ → ip (hs w f₁) (hs w f₂) = ip f₁ f₂) →
  Th f₀ → ip f₀ f₀ = 1 →
  ip (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) (T fun t => if h : t ∈ Λc then Gd (red ⟨t, h⟩) else 0) =
    ((∑ g, ‖Gd g‖ ^ 2 : ℝ) : ℂ) / (Fintype.card G : ℂ) := by
  first | exact @GlobalTheory.finite_plancherel_schrodinger_intertwiner | exact GlobalTheory.finite_plancherel_schrodinger_intertwiner | (intros; apply GlobalTheory.finite_plancherel_schrodinger_intertwiner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqProductDatumThetaConjugateHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.PlancherelHalf

theorem symplO_add_left {D : D7} (S T : HSp D) (t k y : WO S T) :
    symplO S T (t + k) y = symplO S T t y + symplO S T k y := by
  simp only [symplO, hO, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem heisO_lin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (a : ℂ) (f₁ f₂ : WO S T → ℂ) :
    heisO ψ S T w (a • f₁ + f₂) = a • heisO ψ S T w f₁ + heisO ψ S T w f₂ := by
  funext x; simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem ipO_self {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f f = ((nrm2 μ 𝓕 f : ℝ) : ℂ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO nrm2
  rw [← integral_complex_ofReal]
  congr 1; funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem ipO_conj {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f g : Mx D m n → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 g f = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f g) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← integral_conj]
  congr 1; funext w; simp [mul_comm]

theorem ipO_lin {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a : ℂ) (f₁ f₂ g : Mx D m n → ℂ)
    (h₁ : IntegrableOn (fun w => f₁ w * (starRingEnd ℂ) (g w)) 𝓕 μ)
    (h₂ : IntegrableOn (fun w => f₂ w * (starRingEnd ℂ) (g w)) 𝓕 μ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 (a • f₁ + f₂) g = a * GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f₁ g + GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓕 f₂ g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← integral_const_mul, ← integral_add (h₁.const_mul a) h₂]
  congr 1; funext w; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem norm_sq_product_extension_matrix_family_sum {ι : Type} (S : Finset ι) (κ : ι → Type) [∀ i, Fintype (κ i)] (a b : ℕ)
    (ext : (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)) → ∀ i, Matrix (Fin a) (Fin b) (κ i))
    (hext : ∀ z (i : ↥S), ext z i.1 = z i)
    (Gd : (∀ i, Matrix (Fin a) (Fin b) (κ i)) → ℂ) (h : ∀ i, Matrix (Fin a) (Fin b) (κ i) → ℝ)
    (hGd : ∀ y, ‖Gd y‖ = ∏ i ∈ S, h i (y i)) :
    (∑ z : (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)), ‖Gd (ext z)‖ ^ 2) /
        (Fintype.card (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)) : ℝ) =
      ∏ i ∈ S, (∑ᶠ z, h i z ^ 2) / (Nat.card (κ i) : ℝ) ^ (a * b) := by
  have h1 : ∀ z : (∀ i : ↥S, Matrix (Fin a) (Fin b) (κ i.1)), ‖Gd (ext z)‖ ^ 2 = ∏ i : ↥S, h i.1 (z i) ^ 2 := by
    intro z
    rw [hGd, ← Finset.prod_pow, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun i _ => by rw [hext]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (i : ↥S) (m : Matrix (Fin a) (Fin b) (κ i.1)) => h i.1 m ^ 2), Fintype.card_pi, ← Finset.prod_coe_sort S, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  congr 1
  rw [show Fintype.card (Matrix (Fin a) (Fin b) (κ i.1)) = Fintype.card (Fin a → Fin b → κ i.1) from rfl, Fintype.card_fun, Fintype.card_fun]
  simp [← pow_mul, mul_comm]

theorem normSq_thetaAt_halfProd : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
  ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) →
  ∀ (Gd : (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ)
    (h : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP) → ℝ),
    (∀ y, ‖Gd y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, h PP (y PP)) →
  ∀ f' : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        Gd (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) f' →
  ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    nrm2 μ 𝓧 f' = ∏ PP ∈ R.Pg ∪ R.Q t, (∑ᶠ z, h PP z ^ 2) / (Nat.card (kP PP) : ℝ) ^ ((Vc D i).rank * (Wc D i).rank) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he Gd h hGd f' hθ μ 𝓧 hcov

  have hW := hL.2.2.2.2.2.1
  have hLV := hL.2.2.2.2.2.2.2.1
  have hvac := hLV.1.2
  have hU := (hPM.1 R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW).2 (μ, 𝓧) hcov
  have hf₀n : nrm2 μ 𝓧 f₀ = 1 := hvac.norm.2 (μ, 𝓧) hcov
  set S := R.Pg ∪ R.Q t with hS
  set Λ := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) with hΛ
  let FM := frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)
  have hlat := GlobalTheory.T.halfLattice_iff_frameAdjoint_isIntegralMatrix R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he
  let Λc : AddSubgroup (WO (Vc D i) (Wc D i)) :=
    { carrier := {x | x ∈ Λ ∧ IsHalf (cA D e) x}
      add_mem' := fun {a b} ha hb => ⟨Λ.add_mem ha.1 hb.1, fun p q => by
        simp only [Matrix.add_apply, mul_add, ha.2 p q, hb.2 p q]⟩
      zero_mem' := ⟨Λ.zero_mem, fun p q => by simp⟩
      neg_mem' := fun {a} ha => ⟨Λ.neg_mem ha.1, fun p q => by
        simp only [Matrix.neg_apply, mul_neg, ha.2 p q]⟩ }
  have hmem : ∀ x, x ∈ Λc ↔ IsHalf (cA D e) x ∧ IsIntM (FM x) := fun x =>
    ⟨fun hx => ⟨hx.2, (hlat x hx.2).1 hx.1⟩, fun hx => ⟨(hlat x hx.1).2 hx.2, hx.1⟩⟩
  haveI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP =>
    @Fintype.ofFinite _ (Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot)
  let Gt := ∀ PP : ↥S, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP.1)
  let red : Λc →+ Gt := AddMonoidHom.mk' (fun x PP => redM PP.1 (FM x.1)) (fun x y => by
    funext PP
    exact (GlobalTheory.T.adjointFrameMatrix_add_integral_reduction (Vc D i) (Wc D i) (R.βV i) (R.βW i) x.1 y.1 ((hmem _).1 x.2).2 ((hmem _).1 y.2).2).2 PP.1)
  let ext : Gt → ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP) :=
    fun z PP => if hP : PP ∈ S then z ⟨PP, hP⟩ else 0
  obtain ⟨Tm, hTm⟩ := hθ.1
  have hf' := hθ.2 Tm hTm

  have hΦ : (fun x => if IsHalf (cA D e) x ∧ IsIntM (FM x) then Gd (fun PP => redM PP (FM x)) else 0) =
      fun x => if hx : x ∈ Λc then Gd (ext (red ⟨x, hx⟩)) else 0 := by
    funext x
    by_cases hx : IsHalf (cA D e) x ∧ IsIntM (FM x)
    · have hx' : x ∈ Λc := (hmem x).2 hx
      rw [if_pos hx, dif_pos hx']
      congr 1; funext PP
      by_cases hP : PP ∈ S
      · simp only [ext, dif_pos hP]; rfl
      · simp only [ext, dif_neg hP]
        exact GlobalTheory.T.adjointFrameMatrix_reduction_eq_zero_off_places R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he x hx.1 hx.2 PP hP
    · have hx' : x ∉ Λc := fun h' => hx ((hmem x).1 h')
      rw [if_neg hx, dif_neg hx']
  have key := GlobalTheory.T.finite_plancherel_schrodinger_intertwiner_alt R.ψ (symplO (Vc D i) (Wc D i)) Λc red Tm (heisO R.ψ (Vc D i) (Wc D i))
    (IsSBHalf (cA D e) Λ) (IsHalf (cA D (cA D e))) (IsThetaFunO R.ψ (Vc D i) (Wc D i))
    (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO μ 𝓧) f₀ (fun z => Gd (ext z))
    (by
      intro z
      obtain ⟨x, hx1, hx2, hx3⟩ := GlobalTheory.T.exists_halfLattice_adjointFrame_reductions_eq R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he (ext z)
      refine ⟨⟨x, (hmem x).2 ⟨hx1, hx2⟩⟩, ?_⟩
      funext PP
      show redM PP.1 (FM x) = z PP
      rw [hx3 PP.1 PP.2]; simp only [ext, dif_pos PP.2])
    (symplO_add_left _ _)
    (by
      intro Ψ hsupp hinv
      refine ⟨fun t ht => (hsupp t ht).2, Fintype.card Gt, Fintype.card_pos, fun u hu hh t => hinv t u ⟨hu, hh⟩,
        fun t ht => ?_⟩
      exact Λ.nsmul_mem (hsupp t ht).1 _)
    (fun Φ hΦ x hx => hTm.trans Φ hΦ x hx.2)
    (fun Φ hΦ y hy => hTm.modul Φ hΦ y hy)
    (by
      have := hTm.vac
      rw [one_smul] at this
      rw [← this]
      congr 1
      funext x
      unfold halfInd
      by_cases hx : x ∈ Λ ∧ IsHalf (cA D e) x
      · rw [if_pos (show x ∈ Λc from hx), if_pos hx]
      · rw [if_neg (show x ∉ Λc from hx), if_neg hx])
    (by
      intro x hx
      have hx2 := (hmem _).1 x.2
      obtain ⟨PP, hPP⟩ : ∃ PP : ↥S, redM PP.1 (FM x.1) ≠ 0 := by
        by_contra hc; push_neg at hc; exact hx (funext hc)
      obtain ⟨y, hy1, hy2, hy3⟩ := GlobalTheory.T.exists_dual_half_lattice_detecting_character R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL e he x.1 hx2.1 hx2.2
        ⟨PP.1, PP.2, hPP⟩
      refine ⟨y, hy1, fun k hk => ?_, hy3⟩
      have hk2 := (hmem _).1 k.2
      exact hy2 k.1 hk2.1 hk2.2 fun PP hP => congrFun hk ⟨PP, hP⟩)
    (heisO_lin R.ψ (Vc D i) (Wc D i))
    (fun a f₁ f₂ h₁ h₂ => (hU f₁ f₂ h₁ h₂).1 a)
    (fun w f hf => ((hU f f hf hf).2.2.2.2.1 w).1)
    (fun a f₁ f₂ g h₁ h₂ hg => ipO_lin μ 𝓧 a f₁ f₂ g (hU f₁ g h₁ hg).2.1 (hU f₂ g h₂ hg).2.1)
    (fun f g _ _ => ipO_conj μ 𝓧 f g)
    (fun w f₁ f₂ h₁ h₂ => ((hU f₁ f₂ h₁ h₂).2.2.2.2.1 w).2)
    hvac.theta
    (by rw [ipO_self, hf₀n]; simp)
  rw [← hΦ, ← hf'] at key
  have hn : nrm2 μ 𝓧 f' = (∑ z : Gt, ‖Gd (ext z)‖ ^ 2) / (Fintype.card Gt : ℝ) := by
    have := congrArg Complex.re key
    rw [ipO_self, Complex.ofReal_re] at this
    rw [this]
    have h2 : ((∑ z : Gt, ‖Gd (ext z)‖ ^ 2 : ℝ) : ℂ) / (Fintype.card Gt : ℂ) =
        (((∑ z : Gt, ‖Gd (ext z)‖ ^ 2) / (Fintype.card Gt : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.ofReal_re]
  rw [hn]
  exact norm_sq_product_extension_matrix_family_sum S (fun PP => kP PP) _ _ ext (fun z PP => by simp only [ext, dif_pos PP.2]) Gd h hGd

end GlobalTheory.PlancherelHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqProductDatumThetaConjugateHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_productDatumTheta_conjugateHalf : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
  ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) →
  ∀ (Gd : (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ)
    (h : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP) → ℝ),
    (∀ y, ‖Gd y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, h PP (y PP)) →
  ∀ f' : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
      (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        Gd (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) f' →
  ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    nrm2 μ 𝓧 f' = ∏ PP ∈ R.Pg ∪ R.Q t, (∑ᶠ z, h PP z ^ 2) / (Nat.card (kP PP) : ℝ) ^ ((Vc D i).rank * (Wc D i).rank) := by
  first | exact @GlobalTheory.PlancherelHalf.normSq_thetaAt_halfProd | exact GlobalTheory.PlancherelHalf.normSq_thetaAt_halfProd | (intros; apply GlobalTheory.PlancherelHalf.normSq_thetaAt_halfProd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormFiniteThetaDatumEqIndicatorProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormFiniteThetaDatumEqIndicatorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.LevelVecNorm.NormFac

variable {E : Type} [Field E] [NumberField E]

instance finKP (PP : Pl E) : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot

theorem norm_char_fin {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : ‖((f g : ℂˣ) : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem mem_blockTri_blkOf {κ : Type} [CommRing κ] {r t : ℕ} (g : GL (Fin r) κ) : g ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro i j h
  simp [blkOf, i.2, j.2] at h

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {r : ℕ} (hr : r ≤ r) (g : GL (Fin r) κ) : upperLeftBlock hr g = g := by
  have hm : g ∈ blockTri (blk2 r) := by
    rw [mem_blockTri]
    intro i j h
    simp [blk2, i.2, j.2] at h
  ext i j
  rw [upper_block_val_submatrix hr hm]
  rfl

theorem exists_GL_iff {κ : Type} [CommRing κ] {r : ℕ} (M : Matrix (Fin r) (Fin r) κ) :
    (∃ g : GL (Fin r) κ, (g : Matrix (Fin r) (Fin r) κ) = M) ↔ IsUnit M.det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, hg⟩⟩

theorem locH_of_mem (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∈ Pg) : locH Pg Hl PP = Hl ⟨PP, h⟩ := dif_pos h

theorem locH_of_not (Pg : Finset (Pl E)) {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) {PP : Pl E}
    (h : PP ∉ Pg) : locH Pg Hl PP = ⊤ := dif_neg h

theorem norm_omegaQ {D : D7} {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaQ Q r ξ k y‖ = if ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then 1 else 0 := by
  unfold omegaQ
  split
  · rename_i h
    simp only [norm_prod, norm_zpow, norm_char_fin, _root_.one_zpow, Finset.prod_const_one]
  · rename_i h
    rw [norm_zero]

theorem norm_omegaG {D : D7} {b r t : ℕ} (hr : r ≤ r) (Pg : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)) :
    ‖omegaG (Lev.datY r r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) χ ξ Lev.Frm.B) m y‖ =
      if ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
          ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP) then 1 else 0 := by
  by_cases hc : ∀ PP (h : PP ∈ Pg), LowZero r (y PP) ∧
      ∃ g ∈ Hl ⟨PP, h⟩, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc]
    unfold omegaG
    split
    · simp only [norm_mul, norm_prod, norm_inv, norm_char_fin, Finset.prod_const_one, inv_one, mul_one]
    · rename_i h
      exfalso
      apply h
      refine ⟨fun PP hP => (hc PP hP).1, fun PP => (hc PP.1 PP.2).2.choose,
        fun PP => (hc PP.1 PP.2).2.choose_spec.2, fun PP => mem_blockTri_blkOf _, ?_⟩
      show (fun PP : ↥Pg => upperLeftBlock hr ((hc PP.1 PP.2).2.choose)) ∈ Subgroup.pi Set.univ Hl
      intro PP _
      simp only [restrictedBlock_self_apply]
      exact (hc PP.1 PP.2).2.choose_spec.1
  · rw [if_neg hc]
    unfold omegaG
    split
    · rename_i h
      exfalso
      obtain ⟨hlow, g, hg1, -, hg3⟩ := h
      apply hc
      intro PP hP
      have h3 : (fun PP : ↥Pg => upperLeftBlock hr (g PP)) ∈ Subgroup.pi Set.univ Hl := hg3
      have h4 := h3 ⟨PP, hP⟩ (Set.mem_univ _)
      simp only [restrictedBlock_self_apply] at h4
      exact ⟨hlow PP hP, g ⟨PP, hP⟩, h4, hg1 ⟨PP, hP⟩⟩
    · rw [norm_zero]

theorem norm_omegaG_mul_omegaQ {D : D7} {b a r t : ℕ} (hr : r ≤ a) (har : a = r) (Pg Q : Finset (Pl D.host.E))
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) (cl : ∀ PP : ↥Pg, Hl PP →* ℂˣ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    ‖omegaG (Lev.datY a r t 0 hr Pg ∅ (LevelP.ofLocal Hl cl) (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) m y *
        omegaQ Q a m (-1) y‖ = ∏ PP ∈ Pg ∪ Q, suppInd r (locH Pg Hl PP) (y PP) := by
  subst a
  rw [norm_mul, norm_omegaG, norm_omegaQ, ite_zero_mul_ite_zero, mul_one]
  unfold suppInd
  rw [Finset.prod_ite_zero, Finset.prod_const_one]
  by_cases hc : ∀ PP ∈ Pg ∪ Q, LowZero r (y PP) ∧
      ∃ g ∈ locH Pg Hl PP, ((g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) = topL r (y PP)
  · rw [if_pos hc, if_pos]
    refine ⟨fun PP hP => ?_, fun PP hP => ?_⟩
    · have h1 := hc PP (Finset.mem_union_left _ hP)
      rwa [locH_of_mem Pg Hl hP] at h1
    · have h1 := hc PP (Finset.mem_union_right _ hP)
      refine ⟨h1.1, ?_⟩
      obtain ⟨g, -, hg⟩ := h1.2
      exact (exists_GL_iff _).1 ⟨g, hg⟩
  · rw [if_neg hc, if_neg]
    rintro ⟨hA, hB⟩
    apply hc
    intro PP hP
    by_cases hg : PP ∈ Pg
    · rw [locH_of_mem Pg Hl hg]
      exact hA PP hg
    · rw [locH_of_not Pg Hl hg]
      have hq : PP ∈ Q := (Finset.mem_union.1 hP).resolve_left hg
      obtain ⟨g, hg'⟩ := (exists_GL_iff _).2 (hB PP hq).2
      exact ⟨(hB PP hq).1, g, Subgroup.mem_top _, hg'⟩

end GlobalTheory.LevelVecNorm.NormFac

namespace GlobalTheory.LevelVecNorm

theorem normFac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)),
  ‖omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) (y PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t Hl cl m y
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  exact NormFac.norm_omegaG_mul_omegaQ (le_of_eq hW.symm) hW R.Pg (R.Q t) Hl cl m y

end GlobalTheory.LevelVecNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormFiniteThetaDatumEqIndicatorProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_finiteThetaDatum_eq_indicator_product : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)),
  ‖omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y‖ = ∏ PP ∈ R.Pg ∪ R.Q t, GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) (y PP) := by
  first | exact @GlobalTheory.LevelVecNorm.normFac | exact GlobalTheory.LevelVecNorm.normFac | (intros; apply GlobalTheory.LevelVecNorm.normFac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCard
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCard
open Classical

namespace GlobalTheory.LevelVecNorm

theorem finsum_indicator_one_eq_ncard' {α : Type} (s : Set α) :
    (∑ᶠ x, s.indicator (fun _ => (1:ℝ)) x) = (s.ncard : ℝ) := by
  by_cases hs : s.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]
    simp
  · have hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]
    simp

theorem suppInd_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
    ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  intro k _ b a r t hb ha H
  subst hb; subst a
  let f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k := fun g i j =>
    if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0
  have htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k) := by
    intro g; ext i j
    simp [Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]
  have hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g) := by
    intro g i j hi _
    simp [f, show ¬ i.val < r by omega]
  have hinj : Function.Injective f := by
    intro g g' h
    apply Units.ext
    rw [← htop g, ← htop g', h]
  let S : Set (Matrix (Fin (r + t)) (Fin r) k) :=
    {z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}
  have hS : S = f '' (H : Set (GL (Fin r) k)) := by
    ext z
    constructor
    · rintro ⟨hz, g, hg, hgz⟩
      refine ⟨g, hg, ?_⟩
      ext i j
      by_cases hi : i.val < r
      · have := congrFun (congrFun hgz ⟨i.val, hi⟩) j
        simp only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this
        simpa [f, hi] using this
      · simp [f, hi, hz i j (by omega) j.isLt]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hlow g, g, hg, (htop g).symm⟩
  have hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    unfold GlobalTheory.LevelVecNorm.suppInd
    by_cases hz : z ∈ S
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_pos hz', Set.indicator_of_mem hz]; norm_num
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_neg hz', Set.indicator_of_notMem hz]; norm_num
  simp_rw [hfun]
  rw [finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  rfl

end GlobalTheory.LevelVecNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerZeroUpperBlockIndicatorSqSumEqCardStatement
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerZeroUpperBlockIndicator_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
  ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  first | exact @GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | exact GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card | (intros; apply GlobalTheory.LevelVecNorm.suppInd_sq_sum_eq_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.LevelVecNorm

theorem levelVector_squareNorm_eq_prod_localVolumes_alt : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), P = LevelP.ofLocal Hl cl → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → nrm2 μ 𝓧 f = (∏ PP ∈ R.Pg.attach, (Nat.card (Hl PP) : ℝ) * ((Nat.card (kP PP.1) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
  intro hLIS D G _ _ Pl0 T A Ks _ _ _ R F hPM i t σ s P cμ cη m ω BW f₀ f c io hL Hl cl hP μ 𝓧 hμ
  have hL' := hL
  obtain ⟨hcore, -, -, -, -, -, -, hlev, -⟩ := hL'
  obtain ⟨-, e, he, hth⟩ := hlev
  subst hP
  have h1 := GlobalTheory.T.normSq_productDatumTheta_conjugateHalf R F hPM i t σ s (LevelP.ofLocal Hl cl) cμ cη m ω BW f₀ f c io hL e he
    (fun y => omegaG (R.datWp i (LevelP.ofLocal Hl cl)) m y * omegaQ (R.Q t) (Wc D i).rank m (-1) y)
    (fun PP z => GlobalTheory.LevelVecNorm.suppInd D.R.r (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP) z)
    (GlobalTheory.T.norm_finiteThetaDatum_eq_indicator_product R i t Hl cl m) f hth μ 𝓧 hμ
  rw [h1]
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hexp : (Vc D i).rank * (Wc D i).rank = D.R.r ^ 2 + D.R.r * D.R.t := by rw [hV, hW]; ring
  simp_rw [fun PP => GlobalTheory.T.lowerZeroUpperBlockIndicator_sq_sum_eq_card (k := kP PP) D.R.r D.R.t hV hW (GlobalTheory.LevelVecNorm.locH R.Pg Hl PP), hexp]
  rw [Finset.prod_union (GlobalTheory.T.disjoint_Pg_Q_of_core R F hcore t)]
  congr 1
  · rw [← Finset.prod_attach R.Pg]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [div_eq_mul_inv]
    congr 3
    simp [GlobalTheory.LevelVecNorm.locH, PP.2]
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    have hn : PP ∉ R.Pg := fun h => Finset.disjoint_left.1 (GlobalTheory.T.disjoint_Pg_Q_of_core R F hcore t) h hPP
    rw [div_eq_mul_inv]
    congr 2
    simp only [GlobalTheory.LevelVecNorm.locH, dif_neg hn]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv

end GlobalTheory.LevelVecNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelVectorSquareNormEqProdLocalVolumesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelVector_squareNorm_eq_prod_localVolumes : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, GlobalTheory.LiftRows.IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), P = LevelP.ofLocal Hl cl → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → nrm2 μ 𝓧 f = (∏ PP ∈ R.Pg.attach, (Nat.card (Hl PP) : ℝ) * ((Nat.card (kP PP.1) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * ((Nat.card (kP PP) : ℝ) ^ (D.R.r ^ 2 + D.R.r * D.R.t))⁻¹ := by
  first | exact @GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | exact GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt | (intros; apply GlobalTheory.LevelVecNorm.levelVector_squareNorm_eq_prod_localVolumes_alt <;> assumption)
end
