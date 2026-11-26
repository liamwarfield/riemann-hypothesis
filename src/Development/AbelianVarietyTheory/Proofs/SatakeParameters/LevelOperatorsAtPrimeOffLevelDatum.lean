module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemMult
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeKeep

variable {D : D7} {V : HSp D}

theorem suppF_iff (f : Formalism.L2.Theta.AE D) (g : GA D V) :
    SuppF V f g ↔ f • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem mt_mul (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := rfl

theorem mt_one : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem fix_mul {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : f • (b - 1) = b - 1) : f • (a * b - 1) = a * b - 1 := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by rw [sub_mul, one_mul]; abel
  rw [e, smul_add, hb, ← smul_mul_assoc, ha]

theorem fix_inv {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : a * b = 1) : f • (b - 1) = b - 1 := by
  have e : b - 1 = -((a - 1) * b) := by rw [sub_mul, one_mul, hb, neg_sub]
  rw [e, smul_neg, ← smul_mul_assoc, ha]

theorem suppF_mul {f : Formalism.L2.Theta.AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  rw [suppF_iff] at ha hb ⊢
  rw [mt_mul]
  exact fix_mul ha hb

theorem suppF_inv {f : Formalism.L2.Theta.AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  rw [suppF_iff] at ha ⊢
  exact fix_inv ha (by rw [← mt_mul, mul_inv_cancel, mt_one])

theorem suppF_one (f : Formalism.L2.Theta.AE D) : SuppF V f 1 := by
  rw [suppF_iff, mt_one, sub_self, smul_zero]

theorem exists_loc (V : HSp D) (f : Formalism.L2.Theta.AE D) : ∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g :=
  ⟨{ carrier := {g | SuppF V f g}, mul_mem' := suppF_mul, one_mem' := suppF_one f, inv_mem' := suppF_inv },
    fun _ => Iff.rfl⟩

end GlobalTheory.HeckeKeep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOp

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem mem_hyp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {k : GA D V} :
    k ∈ hyp V P ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := by
  refine ⟨fun ⟨h, e', f', h', hs⟩ => ⟨h, ?_⟩, fun h => ⟨h.1, e, f, hP, h.2⟩⟩
  obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' h'
  exact hs

theorem comm_of_supp {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {a b : GA D V} (ha : SuppF V f a)
    (hb : SuppF V (1 - f) b) : Commute a b :=
  have h1 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1.1 h1.2.1).2.2 (1 - f) a b (by rw [mul_sub, mul_one, h1.1, sub_self]) ha hb

theorem full_iff {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Set (GA D V)} {χ : GA D V → ℂ}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (d : List ℤ) (B : Finset (GA D V)) :
    Hecke₂ V J χ SF P d B ↔ OffS D SF P ∧ SphOp V P d B := by
  have hK : {k | k ∈ J ∧ SuppF V f k} = {k | k ∈ KsphC V ∅ ∧ SuppF V f k} :=
    Set.ext fun k => and_congr_left fun hk => hJ k hk
  constructor
  · rintro ⟨e', f', ϖ, α, hS, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨hS, _, _, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, h1, h2, hd, fun _ _ => Iff.rfl,
      fun _ _ _ => rfl, hα, hD, hR, hK ▸ hc⟩
  · rintro ⟨hS, e', f', ϖ, α, -, hP', h1, h2, hd, -, -, hα, hD, hR, hc⟩
    obtain ⟨rfl, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact ⟨_, _, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ, hα, hD, hR, hK ▸ hc⟩

theorem offS_empty : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)

theorem rep_cases (d : List ℤ) : GlobalTheory.Hk3.rep V P d = ∅ ∨ SphOp V P d (GlobalTheory.Hk3.rep V P d) := by
  unfold GlobalTheory.Hk3.rep
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

theorem heckeLin_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V P d R)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    heckeLin V R F (h * (k₁ * k₂)) = heckeLin V R (fun x => F (x * (k₁ * k₂))) h := by
  obtain ⟨L, hL⟩ := GlobalTheory.HeckeKeep.exists_loc V f
  have hJ' : ∀ g, SuppF V f g → (g ∈ ((J ⊓ L : Subgroup (GA D V)) : Set (GA D V)) ↔ g ∈ KsphC V ∅) := fun g hg =>
    ⟨fun h => (hJ g hg).1 h.1, fun h => ⟨(hJ g hg).2 h, (hL g).2 hg⟩⟩
  have hop := (full_iff hP (χ := fun _ => 1) hJ' (fun _ _ _ => rfl) ∅ d R).2 ⟨offS_empty, hR⟩
  have hsupp : ∀ γ ∈ R, SuppF V f γ := by
    obtain ⟨e', f', ϖ, α, -, hP', -, -, -, -, -, -, -, hR, -⟩ := hR
    obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
    exact hR
  have key := GlobalTheory.SphericalOps.level_heckeLin (J := J ⊓ L) (F := fun x => F (x * k₂)) (fun _ _ _ _ => (one_mul _).symm)
    (fun e' f' _ hP' k hk => by
      obtain ⟨-, rfl⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP).2.2.2.1 e' f' hP'
      exact ⟨k, hk, 1, one_mem _, (hL k).1 hk.2, GlobalTheory.HeckeKeep.suppF_one _, (mul_one k).symm⟩) hop
    (fun k hk g => by
      have s := (hL k).1 hk.2
      show F (g * k * k₂) = 1 * F (g * k₂)
      rw [one_mul, mul_assoc, (comm_of_supp hP s s₂).eq, ← mul_assoc,
        hF k ((mem_hyp hP).2 ⟨(hJ k s).1 hk.1, s⟩)]) k₁ ⟨hk₁, (hL _).2 s₁⟩ h
  rw [one_mul, heckeLin_apply, heckeLin_apply] at key
  rw [heckeLin_apply, heckeLin_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) (key.trans (Finset.sum_congr rfl fun a _ => ?_))
  · rw [← mul_assoc, mul_assoc _ k₂, ← (comm_of_supp hP (hsupp a ha) s₂).eq, ← mul_assoc]
  · show _ = F (h * a * (k₁ * k₂))
    rw [(comm_of_supp hP s₁ s₂).eq, ← mul_assoc, hF k₁ ((mem_hyp hP).2 ⟨(hJ _ s₁).1 hk₁, s₁⟩)]

theorem hk_apply (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (h : GA D V) :
    hk V P c F h = ∑ d ∈ c.support, c d * heckeLin V (GlobalTheory.Hk3.rep V P d) F h := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem hk_translate {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ)
    {F : GA D V → ℂ} (hF : ∀ k ∈ hyp V P, ∀ h, F (h * k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (h : GA D V) :
    hk V P c F (h * (k₁ * k₂)) = hk V P c (fun x => F (x * (k₁ * k₂))) h := by
  rw [hk_apply, hk_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rcases rep_cases (V := V) (P := P) d with h0 | h0
  · rw [h0, heckeLin_apply, heckeLin_apply, Finset.sum_empty, Finset.sum_empty]
  · exact heckeLin_translate hP hJ h0 hF hk₁ s₁ s₂ h

theorem postOn_hk {S : D.what₂.Tau → SPar} (M : DSModel V S) (c : List ℤ →₀ ℂ) (U : MMap M) :
    postOn M (hk V P c) U = ∑ d ∈ c.support, c d • heckeOn M (GlobalTheory.Hk3.rep V P d) U := by
  ext v g
  rw [postOn_apply, hk_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem level_operators : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1) ∧ (∀ SF d B, Hecke₂ V (levS V β L) (levChi V β L) SF P d B ↔ OffS D SF P ∧ SphOp V P d B) ∧ (∀ c Φ, HasType V β L Φ → HasType V β L (hk V P c Φ)) ∧ (∀ c (g0 : G0 L.Pg L.r) Φ, (∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h) → actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) ∧ ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) c, IsInfFam θ → ∀ U ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  intro D V β Λ N L hB P hN hPP
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  obtain ⟨hJ, hχ, hs⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hP hN hPP
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  have h1 : ∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1 := fun k hk => by
    obtain ⟨a, b⟩ := (mem_hyp hP).1 hk
    exact ⟨(hJ k b).2 a, hχ k ((hJ k b).2 a) b⟩
  have hinv : ∀ Φ, HasType V β L Φ → ∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h := fun Φ hΦ k hk h => by
    rw [hΦ k (h1 k hk).1, (h1 k hk).2, one_mul]
  refine ⟨h1, full_iff hP hJ hχ, fun c Φ hΦ κ hκ h => ?_, fun c g0 Φ hΦ => ?_, fun S θ M c hθ U hU => ?_⟩
  · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
    have e1 : (fun x => Φ (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • Φ := funext fun x => hΦ _ hκ x
    rw [hk_translate hP hJ c (hinv Φ hΦ) hk₁ s₁ s₂, e1, LinearMap.map_smul]
    rfl
  · unfold actG0
    split_ifs with hex
    · have hl := hex.choose_spec
      generalize hex.choose = κ at hl ⊢
      have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
      obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
      have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
        (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
      rw [e1, LinearMap.map_smul]
      funext h
      rw [hk_translate hP hJ' c hΦ hk₁ s₁ s₂]
      rfl
    · rw [LinearMap.map_zero]
  · rw [postOn_hk]
    refine sum_mem fun d _ => Submodule.smul_mem _ _ ?_
    rcases rep_cases (V := V) (P := P) d with h0 | h0
    · have : heckeOn M (GlobalTheory.Hk3.rep V P d) U = 0 := by
        ext v g
        rw [h0, heckeOn, postOn_apply, heckeLin_apply, Finset.sum_empty]
        rfl
      rw [this]
      exact zero_mem _
    · have hop := (full_iff hP (J := levS V β L) hJ hχ ∅ d _).2 ⟨offS_empty, h0⟩
      rw [GlobalTheory.MultMem.mem_mult_iff] at hU ⊢
      refine GlobalTheory.SphericalOps.isMultMap_heckeOn hU (fun k hk => ?_) fun v κ hκ h => ?_
      · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := hop
        exact (hc.1 k hk).1
      · obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
        have e1 : (fun x => U v (x * (k₁ * k₂))) = levChi V β L (k₁ * k₂) • U v := funext fun x => hU.lev v _ hκ x
        rw [heckeLin_translate hP hJ h0 (hinv _ (hU.lev v)) hk₁ s₁ s₂, e1, LinearMap.map_smul]
        rfl

end GlobalTheory.LevOp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_operators_at_prime_off_level_datum : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1) ∧ (∀ SF d B, Hecke₂ V (levS V β L) (levChi V β L) SF P d B ↔ OffS D SF P ∧ SphOp V P d B) ∧ (∀ c Φ, HasType V β L Φ → HasType V β L (hk V P c Φ)) ∧ (∀ c (g0 : G0 L.Pg L.r) Φ, (∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h) → actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) ∧ ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) c, IsInfFam θ → ∀ U ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  first | exact @GlobalTheory.LevOp.level_operators | exact GlobalTheory.LevOp.level_operators | (intros; apply GlobalTheory.LevOp.level_operators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
namespace GlobalTheory.Hk3

theorem locVac_span_classes_indep : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    iSupIndep (fun c : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = c ∧ w = ρ x s}) := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]
  set Λ := HoweDuality.intMat L n' n with hΛdef

  have hle : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ) = c ∧ w = ρ x s}) ≤
      fun c => Submodule.span ℂ {ρ c.out s} := by
    intro c
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, hx, rfl⟩
    have hm : -c.out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq', hx])
    have := hshift s hvac c.out _ hm
    rw [add_neg_cancel_left] at this
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine iSupIndep.mono ?_ hle
  by_cases hs : s = 0
  · have hb : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ => Submodule.span ℂ {ρ c.out s}) = fun _ => ⊥ := by
      funext c; rw [hs, map_zero, Submodule.span_singleton_eq_bot]
    rw [hb, iSupIndep_def]
    intro i
    exact disjoint_bot_left
  have hnz : ∀ x, ρ x s ≠ 0 := by
    intro x h0
    have := congrArg (fun f => f s) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact hs ((smul_eq_zero.mp this.symm).resolve_left hne)
  refine LinearIndependent.iSupIndep_span_singleton ?_
  rw [linearIndependent_iff']
  intro I C hC y hy
  have hind := eig_indep (fun u : intMatSub (L := L) n n' => ρ (u : Matrix (Fin n') (Fin n) L))
    (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : intMatSub (L := L) n n') =>
      ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
    (fun y => ρ y.out s) (fun y u => heig s hvac y.out u u.2) I
    (by
      intro y _ y' _ hyy
      by_contra hcon
      push_neg at hcon
      apply hyy
      have hm := hdist y.out y'.out (fun u hu => hcon ⟨u, hu⟩)
      rw [hΛ] at hm
      rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
      exact hm)
    C hC
  exact (smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)

end GlobalTheory.Hk3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependentStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeModel_vacuumTranslate_classes_independent : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    iSupIndep (fun c : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = c ∧ w = ρ x s}) := by
  first | exact @GlobalTheory.Hk3.locVac_span_classes_indep | exact GlobalTheory.Hk3.locVac_span_classes_indep | (intros; apply GlobalTheory.Hk3.locVac_span_classes_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMulAddEqOneOfNotMem
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}



omit [StarRing E] in
theorem exists_coprime_mem (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ Q ∈ S, ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal) : ∃ a : ℕ, a.Coprime p ∧ ∀ Q ∈ S, ((a : ℕ) : 𝓞 E) ∈ Q.asIdeal := by
  classical
  have h1 : ∀ Q : S, ∃ a : ℕ, a.Coprime p ∧ ((a : ℕ) : 𝓞 E) ∈ Q.1.asIdeal := by
    intro Q
    haveI := Q.1.isMaximal
    haveI : Finite (𝓞 E ⧸ Q.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.1.ne_bot
    letI := Ideal.Quotient.field Q.1.asIdeal
    have hp : (ringChar (𝓞 E ⧸ Q.1.asIdeal)).Prime := CharP.prime_ringChar _
    refine ⟨_, (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hS Q.1 Q.2 ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 h
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact (ringChar.spec _ _).2 dvd_rfl
  choose a ha ha' using h1
  refine ⟨∏ Q, a Q, Nat.Coprime.prod_left fun Q _ => ha Q, fun Q hQ => ?_⟩
  exact Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨Q, hQ⟩))) (ha' ⟨Q, hQ⟩)

end Deco

section Coef

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K)

theorem natCast_notMem_of_coprime {a p : ℕ} (h : a.Coprime p) (w : HeightOneSpectrum (𝓞 K))
    (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  obtain ⟨x, y, e⟩ := (Nat.Coprime.cast (R := 𝓞 K) h)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ ha) (w.asIdeal.mul_mem_left _ hw)))

omit [Fintype ι] in
theorem nsmul_mem_tauLat (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    {y : Fin n → K} (hy : y ∈ tauLat emb τ L) : a • y ∈ tauLat emb τ L' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨a • x, h x hx, ?_⟩
    funext i
    simp
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy

omit [Fintype ι] in
theorem localization_dualFr_tauLat_le (τ : ι) {L L' : Submodule (𝓞 E) (Fin n → E)} {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (dualFr (tauLat emb τ L')) ≤ localization₂ w.asIdeal (dualFr (tauLat emb τ L)) := by
  refine GlobalTheory.TransLoc.localization_le_of_smul_mem w ha fun φ hφ x hx => ?_
  have := hφ _ (nsmul_mem_tauLat emb τ h hx)
  rw [dotProduct_smul] at this
  rw [smul_dotProduct, Nat.cast_smul_eq_nsmul]
  exact this

theorem localization_nabK_delK_congr (lam : ι → DomWeight n) {M M' : ι → Submodule (𝓞 K) (Fin n → K)}
    (hM : ∀ τ, Submodule.IsFullLattice K (M τ)) (hM' : ∀ τ, Submodule.IsFullLattice K (M' τ)) (w : HeightOneSpectrum (𝓞 K))
    (h : ∀ τ, localization₂ w.asIdeal (M τ) = localization₂ w.asIdeal (M' τ)) :
    localization₂ w.asIdeal (nabK lam M) = localization₂ w.asIdeal (nabK lam M') ∧
      localization₂ w.asIdeal (delK lam M) = localization₂ w.asIdeal (delK lam M') := by
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have hB' : ∀ τ, IsBasisAt w (M' τ) (B τ) := fun τ => (h τ).symm.trans (hB τ)
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have h2 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M' hM' w B hB'
  have key : ∀ (T : Submodule (𝓞 K) (Pol K ι n)) (x : VV K lam),
      x ∈ localization₂ w.asIdeal (T.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) ↔ x.1 ∈ localization₂ w.asIdeal T := by
    intro T x
    exact Iff.rfl
  constructor
  · ext x
    unfold nabK
    rw [key, key, h1.1, h2.1]
  · ext x
    unfold delK
    rw [key, key, h1.2, h2.2]

theorem localization_nabAtr_delAtr_congr (lam : ι → DomWeight n) {L L' : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.IsFullLattice E L) (hL' : Submodule.IsFullLattice E L') {a : ℕ} (h : ∀ x ∈ L, a • x ∈ L')
    (h' : ∀ x ∈ L', a • x ∈ L) (w : HeightOneSpectrum (𝓞 K)) (ha : ((a : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr emb lam L) = localization₂ w.asIdeal (nabAtr emb lam L') ∧
      localization₂ w.asIdeal (delAtr emb lam L) = localization₂ w.asIdeal (delAtr emb lam L') :=
  localization_nabK_delK_congr lam
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L' hL')) w
    fun τ => le_antisymm (localization_dualFr_tauLat_le emb τ h' w ha) (localization_dualFr_tauLat_le emb τ h w ha)

end Coef

variable {p : ℕ} {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem use₃ (lam : X.Tau → DomWeight n) (hT : ∀ Q ∈ ST, ((p : ℕ) : 𝓞 X.E) ∉ Q.asIdeal)
    (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) :
    localization₂ w.asIdeal (nabAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (nabAtr X.emb lam d.1.N) ∧
      localization₂ w.asIdeal (delAtr X.emb lam d.1.Lsh) = localization₂ w.asIdeal (delAtr X.emb lam d.1.N) := by
  obtain ⟨a, hap, ha⟩ := exists_coprime_mem p ST hT
  letI : Submodule.IsFullLattice X.E d.1.N := Formalism.L2.Ker.full_of_sd ⟨d.2.lat, d.2.uni⟩
  letI := d.2.Lsh_lattice
  have hLsh : Submodule.IsFullLattice X.E d.1.Lsh := Submodule.IsFullLattice.of_le X.E d.2.N_le_Lsh
  refine localization_nabAtr_delAtr_congr X.emb lam hLsh inferInstance (a := a) (fun x hx => ?_)
    (fun x hx => Submodule.smul_of_tower_mem _ a (d.2.N_le_Lsh hx)) w (natCast_notMem_of_coprime hap w hw)
  rw [← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
  exact d.2.smul_Lsh_mem_N (fun P => by rw [map_natCast]; exact ha P.1 P.2) hx

end GlobalTheory.GO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimeProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimeProperties
noncomputable section

namespace GlobalTheory.TwU.Served

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical NumberField

theorem hP_ne_zero (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) (hn : HNeZero D.host p) : hP D p ≠ 0 := by
  obtain ⟨P, hP', hL, σ, hσ⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.exists_frob D.host p hp hc
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP', hL, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have h3 := @HNeZero.ne_one _ _ _ hn P₂ h1 h2 σ₂ hσ₂
  intro h0
  apply h3
  rw [he]
  have h4 := Formalism.HC.Frame.iota_iotaInv D.R.toFrame (Classical.epsilon (fun g => g ∈ frobSet D p)).2
  unfold hP at h0
  rw [h0, Formalism.HC.Frame.iota_zero] at h4
  exact h4.symm

theorem jacobi_eq_neg_one (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  obtain ⟨h2, hq, hd, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcop : (-(D.host.d : ℤ)).gcd (p : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes D.host.hyp.2.1 hp).2 (Ne.symm hd)
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h | h | h
  · exact absurd hcop (jacobiSym.eq_zero_iff_not_coprime.1 h)
  · exact absurd h hjd
  · exact h

theorem coprime_absNorm_ccK (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  obtain ⟨-, -, -, hjd, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host p hc
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
  obtain ⟨P, hpP, hdvd⟩ := GlobalTheory.HalfCompare.exists_place_of_dvd_absNorm hp D.host.ccK h
  obtain ⟨hNP, hj⟩ := D.host.ccK_split P.asIdeal P.isPrime (Ideal.le_of_dvd hdvd)
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.HalfCompare.exists_prime_under P
  have hlp : l = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 ((hlP p).1 hpP)
  have hlN : l = Ideal.absNorm P.asIdeal :=
    (Nat.prime_dvd_prime_iff_eq hl hNP).1 ((hlP _).1 (Ideal.absNorm_mem P.asIdeal))
  rw [← hlN, hlp] at hj
  exact hjd hj

theorem served_facts : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p →
    hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p :=
  fun D p hp hc hn => ⟨hP_ne_zero D p hp hc hn, jacobi_eq_neg_one D p hp hc, coprime_absNorm_ccK D p hp hc⟩

end GlobalTheory.TwU.Served
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimePropertiesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.servedPrime_properties : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p → hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  first | exact @GlobalTheory.TwU.Served.served_facts | exact GlobalTheory.TwU.Served.served_facts | (intros; apply GlobalTheory.TwU.Served.served_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelComm

section Abstract

variable {G : Type} [Group G]

theorem isDC_of_reps {K : Subgroup G} {x : G} {A : Finset G} (h : GlobalTheory.SphLabelOps.Reps K x A) :
    Formalism.IndefR.Bridge.IsDC K x A := by
  refine ⟨fun a ha => ?_, fun g hg => h.2 g ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hg
    exact ⟨k₁, k₁.2, k₂, k₂.2, rfl⟩

theorem sum_comm_of_antiInv (K L : Subgroup G) (hKL : K ≤ L) (θ : G → G)
    (t1 : ∀ g ∈ L, θ g ∈ L) (t2 : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (t3 : ∀ x ∈ L, θ (θ x) = x)
    (t4 : ∀ k ∈ K, θ k ∈ K) (t5 : ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b)
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) {A B A' : Finset G}
    (hA : GlobalTheory.SphLabelOps.Reps K x A) (hB : GlobalTheory.SphLabelOps.Reps K y B) (hA' : GlobalTheory.SphLabelOps.Reps K x⁻¹ A')
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u) :
    ∑ a ∈ A, π a (∑ b ∈ B, π b u) = ∑ b ∈ B, π b (∑ a ∈ A, π a u) := by
  have memL : ∀ {z : G} {R : Finset G}, GlobalTheory.SphLabelOps.Reps K z R → z ∈ L → ∀ a ∈ R, a ∈ L := by
    intro z R hR hz a ha
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR.1 a ha
    exact mul_mem (mul_mem (hKL h₁) hz) (hKL h₂)
  have hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧
      (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K ⊓ L, θ k ∈ K) ∧ ∀ g ∈ L, ∃ a ∈ K ⊓ L, ∃ b ∈ K ⊓ L, θ g = a * g * b := by
    refine ⟨θ, t1, t2, t3, fun k hk => t4 k hk.1, fun g hg => ?_⟩
    obtain ⟨a, ha, b, hb, e⟩ := t5 g hg
    exact ⟨a, ⟨ha, hKL ha⟩, b, ⟨hb, hKL hb⟩, e⟩
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hF : ∀ (k : K) (h : G), (fun g => φ (π g u)) (h * k) = ((1 : K →* ℂˣ) k : ℂ) • (fun g => φ (π g u)) h := by
    intro k h
    simp [map_mul, Module.End.mul_apply, hu k k.2]
  have key := (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (W := ℂ) K L 1 x y A B A' (fun g => φ (π g u))
    (fun k hk => ⟨k, hk, 1, one_mem _, hKL hk, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun k _ => rfl) hθ (memL hA hx) (memL hB hy) (memL hA' (inv_mem hx)) (isDC_of_reps hA) (isDC_of_reps hB)
    (isDC_of_reps hA') hF).1
  have e := congrFun key 1
  simp only [Formalism.IndefR.Bridge.dcOp, one_mul, map_mul, Module.End.mul_apply] at e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, LinearMap.zero_apply]
  rw [sub_eq_zero]
  exact e

theorem comb_comm {ι M : Type} [AddCommGroup M] [Module ℂ M] (S : ι → Module.End ℂ M) (u : M)
    (h : ∀ i j, S i (S j u) = S j (S i u)) (c c' : ι →₀ ℂ) :
    (c.sum fun i z => z • S i) ((c'.sum fun i z => z • S i) u) =
      (c'.sum fun i z => z • S i) ((c.sum fun i z => z • S i) u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [h i j, smul_comm]

end Abstract


open GlobalTheory.IdemSupport in
theorem label_ops_comm : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ c c', ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P c (opOf π P c' u) = opOf π P c' (opOf π P c u) := by
  intro D V P c c' M _ _ π u hu
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨e, f, h⟩ := (supported_group_and_prime_idempotents V).2.1 P
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 P e f h
  obtain ⟨L, hL⟩ := ((supported_group_and_prime_idempotents V).1 f h0.1 h0.2.1).1
  have memK : ∀ k, k ∈ K ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := fun k => by
    rw [← SetLike.mem_coe, ← hK, GlobalTheory.SphLabelOps.hyp_eq h]
    rfl
  have hKL : K ≤ L := fun k hk => (hL k).2 ((memK k).1 hk).2
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ : ∃ θ : GA D V → GA D V, (∀ g ∈ L, θ g ∈ L) ∧
      (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K, θ k ∈ K) ∧
      ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b := by
    rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
    · obtain ⟨θ, s1, s2, s3, s4, s5⟩ := (GlobalTheory.SplitPlace.split_local V P e hs).1
      refine ⟨θ, fun g hg => (hL _).2 (s1 g ((hL g).1 hg)), fun x hx y hy => s2 x y ((hL x).1 hx) ((hL y).1 hy),
        fun x hx => s3 x ((hL x).1 hx), fun k hk => ?_, fun g hg => ?_⟩
      · have hk' := (memK k).1 hk
        exact (memK _).2 ⟨s4 k hk', s1 k hk'.2⟩
      · obtain ⟨a, ha, b, hb, eq⟩ := s5 g ((hL g).1 hg)
        exact ⟨a, (memK a).2 ha, b, (memK b).2 hb, eq⟩
    · refine ⟨fun g => g⁻¹, fun g hg => inv_mem hg, fun x _ y _ => mul_inv_rev x y, fun x _ => inv_inv x,
        fun k hk => inv_mem hk, fun g hg => ?_⟩
      obtain ⟨a, b, ha, ha', hb, hb', eq⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ h
        (GlobalTheory.SphLabelOps.exists_real_unif D P) g ((hL g).1 hg)).1
      exact ⟨a, (memK a).2 ⟨ha, ha'⟩, b, (memK b).2 ⟨hb, hb'⟩, eq⟩
  have reps : ∀ d, IsLab V P d → ∃ x ∈ L, GlobalTheory.SphLabelOps.Reps K x (rep V P d) ∧
      ∃ A', GlobalTheory.SphLabelOps.Reps K x⁻¹ A' := by
    intro d hd
    have hR := GlobalTheory.SphLabelOps.sphOp_rep hd
    obtain ⟨e', f', ϖ, α, -, h', h1, h2, -, -, -, hα, hD, -⟩ := id hR
    obtain ⟨rfl, rfl⟩ := h0.2.2.2.1 e' f' h'
    have hαL : α ∈ L := (hL α).2 hα
    refine ⟨α, hαL, GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 hα hD hR, ?_⟩
    obtain ⟨R', hR', -⟩ := GlobalTheory.SphLabelOps.exists_dual hR
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h').1
    exact ⟨R', GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 ((hL _).1 (inv_mem hαL))
      (GlobalTheory.DivDual.divAt_inv_and_mul V _ _ d α he (GlobalTheory.SphLabelOps.unif_ne_zero h2) hD).1 hR'⟩
  have key : ∀ d d', (∑ γ ∈ rep V P d, π γ) ((∑ δ ∈ rep V P d', π δ) u) =
      (∑ δ ∈ rep V P d', π δ) ((∑ γ ∈ rep V P d, π γ) u) := by
    intro d d'
    by_cases hd : IsLab V P d
    swap
    · simp [Hk3.rep, dif_neg hd]
    by_cases hd' : IsLab V P d'
    swap
    · simp [Hk3.rep, dif_neg hd']
    obtain ⟨x, hx, rA, A', rA'⟩ := reps d hd
    obtain ⟨y, hy, rB, -⟩ := reps d' hd'
    simp only [LinearMap.sum_apply]
    exact sum_comm_of_antiInv K L hKL θ t1 t2 t3 t4 t5 hx hy rA rB rA' π u
      (fun k hk => hu k (by rw [hK]; exact hk))
  exact comb_comm (fun d => ∑ γ ∈ rep V P d, π γ) u key c c'

end GlobalTheory.SphLabelComm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalHeckeCombinations_commute_fixedVectors : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ c c', ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P c (opOf π P c' u) = opOf π P c' (opOf π P c u) := by
  first | exact @GlobalTheory.SphLabelComm.label_ops_comm | exact GlobalTheory.SphLabelComm.label_ops_comm | (intros; apply GlobalTheory.SphLabelComm.label_ops_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorEqLabelOperatorLocalReps
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorEqLabelOperatorLocalReps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HkDict

theorem lift_cosets {H G : Type} [Group H] [Group G] (φ : H →* G) (N J₀ L₀ L₁ : Subgroup H) (J : Subgroup G) (K : Set H)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hi : ∀ g g', g ∈ N → g' ∈ N → φ g = φ g' → g = g')
    (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hLN : ∀ g ∈ L₀, g ∈ N)
    (hc : ∀ g g', g ∈ L₀ → g' ∈ L₁ → Commute g g') (hd : ∀ g, g ∈ L₀ → g ∈ L₁ → g = 1)
    (hK : ∀ g, g ∈ L₀ → (g ∈ J₀ ↔ g ∈ K))
    (hsp : ∀ k ∈ J₀, ∃ k₁ ∈ J₀, ∃ k₂ ∈ J₀, k₁ ∈ L₀ ∧ k₂ ∈ L₁ ∧ k = k₁ * k₂)
    (α : H) (hα : α ∈ L₀) (B : Finset G) (hB : ∀ a ∈ B, ∃ g ∈ L₀, φ g = a) (hDC : Bridge.IsDC J (φ α) B) :
    ∃ R : Finset H, (∀ γ ∈ R, γ ∈ L₀) ∧
      (∀ γ ∈ R, ∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ γ = k₁ * α * k₂) ∧
      (∀ x : H, (∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ x = k₁ * α * k₂) →
        ∃! γ, γ ∈ R ∧ (γ⁻¹ * x ∈ K ∧ γ⁻¹ * x ∈ L₀)) ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), ∑ a ∈ B, F a = ∑ γ ∈ R, F (φ γ) := by
  classical
  choose s hs1 hs2 using hs
  have hsL : ∀ a ∈ B, s a ∈ L₀ := fun a ha => by
    obtain ⟨g, hg, rfl⟩ := hB a ha
    rw [hi _ _ (hs1 _) (hLN g hg) (hs2 _)]
    exact hg
  have hsinj : Function.Injective s := fun a b h => by rw [← hs2 a, ← hs2 b, h]
  have hKJ : ∀ k, k ∈ K ∧ k ∈ L₀ → φ k ∈ J := fun k hk => (hJ k (hLN k hk.2)).2 ((hK k hk.2).2 hk.1)
  refine ⟨B.image s, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact hsL a ha
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, hk⟩ := hDC.1 a ha
    have j₁ : s k₁ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    have j₂ : s k₂ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    obtain ⟨a₁, ha₁, b₁, hb₁, la₁, lb₁, e₁⟩ := hsp _ j₁
    obtain ⟨a₂, ha₂, b₂, hb₂, la₂, lb₂, e₂⟩ := hsp _ j₂
    have e : s a = s k₁ * α * s k₂ := by
      refine hi _ _ (hs1 _) (N.mul_mem (N.mul_mem (hs1 _) (hLN _ hα)) (hs1 _)) ?_
      rw [map_mul, map_mul, hs2, hs2, hs2]
      exact hk
    have e' : s a = (a₁ * α * a₂) * (b₁ * b₂) := by
      rw [e, e₁, e₂]
      have c := (hc _ _ (L₀.mul_mem hα la₂) lb₁).eq
      calc a₁ * b₁ * α * (a₂ * b₂) = a₁ * (b₁ * (α * a₂)) * b₂ := by simp only [mul_assoc]
        _ = _ := by rw [← c]; simp only [mul_assoc]
    have hb : b₁ * b₂ = 1 := by
      refine hd _ ?_ (L₁.mul_mem lb₁ lb₂)
      have : b₁ * b₂ = (a₁ * α * a₂)⁻¹ * s a := by rw [e', inv_mul_cancel_left]
      rw [this]
      exact L₀.mul_mem (L₀.inv_mem (L₀.mul_mem (L₀.mul_mem la₁ hα) la₂)) (hsL a ha)
    exact ⟨a₁, ⟨(hK _ la₁).1 ha₁, la₁⟩, a₂, ⟨(hK _ la₂).1 ha₂, la₂⟩, by rw [e', hb, mul_one]⟩
  · rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have hxL : x ∈ L₀ := hx ▸ L₀.mul_mem (L₀.mul_mem h₁.2 hα) h₂.2
    obtain ⟨a, ⟨ha, haJ⟩, hu⟩ := hDC.2 (φ x) ⟨⟨φ k₁, hKJ _ h₁⟩, ⟨φ k₂, hKJ _ h₂⟩, by rw [hx, map_mul, map_mul]⟩
    have hL : (s a)⁻¹ * x ∈ L₀ := L₀.mul_mem (L₀.inv_mem (hsL a ha)) hxL
    refine ⟨s a, ⟨Finset.mem_image_of_mem s ha, (hK _ hL).1 ((hJ _ (hLN _ hL)).1 ?_), hL⟩, ?_⟩
    · rwa [map_mul, map_inv, hs2]
    · rintro γ ⟨hγ, hγK⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
      have := hKJ _ hγK
      rw [map_mul, map_inv, hs2] at this
      rw [hu b ⟨hb, this⟩]
  · intro W _ F
    rw [Finset.sum_image fun a _ b _ h => hsinj h]
    simp only [hs2]

def rightTr {H G : Type} [Group H] [Group G] (φ : H →* G) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (G → W) where
  toFun g := { toFun := fun F h => F (h * φ g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F h; simp
  map_mul' g g' := by ext F h; simp [mul_assoc]

theorem supp_both {D : D7} (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) (h : SuppF V f g) (h' : SuppF V (1 - f) g) :
    g = 1 := by
  apply Subtype.ext
  apply Units.ext
  have : Formalism.L2.Theta.mt V g - 1 = 0 := by
    ext i j
    have a := h i j
    have b := h' i j
    rw [sub_mul, one_mul, a, sub_self] at b
    exact b.symm
  exact sub_eq_zero.1 this


set_option maxHeartbeats 1000000 in
open GlobalTheory.SplitHeckeAdj in
theorem dcOp_eq_label : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)), d.Pairwise (fun a b => b ≤ a) → IsLabElt V P d x → (∀ a ∈ B, IsLocElt V P a) → Bridge.IsDC (levEnv V β L).J x B → IsLab V P d ∧ ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Φ : Bridge.Gf V → W), (∀ h (k : (levEnv V β L).J), IsLocElt V P k → Φ (h * k) = Φ h) → Bridge.dcOp B Φ = hkF V P (Finsupp.single d 1) Φ := by
  intro D V β Λ N L hβ P hN hoff d x B hd hx hB hDC
  obtain ⟨e, f, ϖ, α, hP, hϖ, hϖ', -, hxα, hα, hdiv⟩ := hx
  have hG := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have h01 := hG.2.2.1 P e f hP
  have hff := h01.1
  have hcf := h01.2.1
  have hff' : (1 - f) * (1 - f) = 1 - f := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero]
  have hcf' : cA D (1 - f) = 1 - f := by rw [map_sub, map_one, hcf]
  obtain ⟨L₀, hL₀⟩ := (hG.1 f hff hcf).1
  obtain ⟨L₁, hL₁⟩ := (hG.1 _ hff' hcf').1
  have h03 := (GlobalTheory.LevSplit.lev_split V β Λ N (flag1L L) hβ).2 P e f hP hN hoff
  have hK := h03.1
  have hsp := h03.2.2
  have hx' : x = fin V α := Subtype.ext hxα
  subst hx'
  have hB' : ∀ a ∈ B, ∃ g ∈ L₀, fin V g = a := fun a ha => by
    obtain ⟨e', f', g, hP', -, h1, h2⟩ := hB a ha
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at h2
    exact ⟨g, (hL₀ g).2 h2, Subtype.ext h1.symm⟩
  have main := lift_cosets (fin V) (GfC V) (levG V β (flag1L L)) L₀ L₁ (levEnv V β L).J (KsphC V ∅)
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L)
    (fun g hg => h01.2.2.1 g ((hL₀ g).1 hg))
    (fun g g' h h' => commute_compl V _ hff hcf ((hL₀ g).1 h) ((hL₁ g').1 h'))
    (fun g h h' => supp_both V f g ((hL₀ g).1 h) ((hL₁ g).1 h'))
    (fun g h => hK g ((hL₀ g).1 h))
    (fun k hk => by
      obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, h⟩ := hsp k hk
      exact ⟨k₁, h₁, k₂, h₂, (hL₀ _).2 s₁, (hL₁ _).2 s₂, h⟩)
    α ((hL₀ α).2 hα) B hB' hDC
  obtain ⟨R, r1, r2, r3, r4⟩ := main
  simp only [hL₀] at r1 r2 r3
  have hR : SphOp V P d R :=
    ⟨e, f, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, hϖ, hϖ', hd, fun _ _ => Iff.rfl, fun _ _ _ => rfl,
      hα, hdiv, r1, fun γ hγ => ⟨h01.2.2.1 γ (r1 γ hγ), r2 γ hγ⟩, r3⟩
  refine ⟨⟨R, hR⟩, fun W _ _ Φ hΦ => ?_⟩
  have hfix : ∀ k ∈ hyp V P, rightTr (fin V) W k Φ = Φ := by
    rintro k ⟨hk, e', f', hP', hs⟩
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at hs
    have hkf := h01.2.2.1 k hs
    funext h
    exact hΦ h ⟨fin V k, (mem_J V β L hkf).2 ((hK k hs).2 hk)⟩ ⟨e, f, k, hP, hkf, rfl, hs⟩
  have h := ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 d R hR).2 _ (rightTr (fin V) W) Φ hfix
  funext g
  have h1 := congrFun h g
  have h2 : Bridge.dcOp B Φ g = ∑ γ ∈ R, Φ (g * fin V γ) := r4 W fun a => Φ (g * a)
  rw [h2]
  simp only [opOf, hkF, zero_smul, Finsupp.sum_single_index, one_smul, Finset.sum_apply, LinearMap.sum_apply] at h1 ⊢
  exact h1

end GlobalTheory.HkDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorEqLabelOperatorLocalRepsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)), d.Pairwise (fun a b => b ≤ a) → IsLabElt V P d x → (∀ a ∈ B, IsLocElt V P a) → Bridge.IsDC (levEnv V β L).J x B → IsLab V P d ∧ ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Φ : Bridge.Gf V → W), (∀ h (k : (levEnv V β L).J), IsLocElt V P k → Φ (h * k) = Φ h) → Bridge.dcOp B Φ = hkF V P (Finsupp.single d 1) Φ := by
  first | exact @GlobalTheory.HkDict.dcOp_eq_label | exact GlobalTheory.HkDict.dcOp_eq_label | (intros; apply GlobalTheory.HkDict.dcOp_eq_label <;> assumption)
end
end
