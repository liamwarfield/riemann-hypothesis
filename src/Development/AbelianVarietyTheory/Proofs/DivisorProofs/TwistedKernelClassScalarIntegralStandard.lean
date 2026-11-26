module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitModulusConstantsEquivariantDictionary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NotMemOfCoprime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortUnits

open GlobalTheory.LatticeIndex GlobalTheory.TrivLattice

section Val
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem valuation_nat {k : ℕ} (hk : (k : 𝓞 K) ∉ la.asIdeal) : la.valuation K (k : K) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 K) K)]
  exact la.valuation_eq_one_iff_notMem.2 hk

theorem not_mem_of_coprime' {a b : ℕ} (h : Nat.Coprime a b) (ha : (a : 𝓞 K) ∈ la.asIdeal) :
    (b : 𝓞 K) ∉ la.asIdeal := fun hb => by
  obtain ⟨u, v, e⟩ : IsCoprime (a : 𝓞 K) (b : 𝓞 K) := h.cast
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ ha) (la.asIdeal.mul_mem_left _ hb)))

end Val

theorem vLa_beta {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (la : HeightOneSpectrum (𝓞 c.F)) (hA : PullbackSections.AdaptAt Λ la) (β : c.F)
    (hβ : BetaIs (Dw := Dw) c Λ β) : vLa la β = 0 := by
  obtain ⟨k, hk, hk1, hk2⟩ := hA
  have h1 : ∀ v ∈ Λ.La, k • v ∈ stdLat E n := fun v hv => nsmul_mem_of_le hk1 hv
  have h2 : ∀ v ∈ stdLat E n, k • v ∈ Λ.La := fun v hv => nsmul_mem_of_le hk2 hv
  let w := la.valuation c.F
  have hw : ∀ r : 𝓞 c.F, w (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r => la.valuation_le_one r
  have hwτ : ∀ τ, ∀ r : 𝓞 E, w.comap (embF c τ) (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    hw ⟨_, map_isIntegral_int (embF c τ) r.isIntegral_coe⟩
  have hnat : ∀ τ, w.comap (embF c τ) (k : E) = 1 := fun τ => by
    simp only [w, Valuation.comap_apply, map_natCast]
    exact valuation_nat la hk
  have hm : ∀ (A : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ A, k • v ∈ stdLat E n) → (∀ v ∈ stdLat E n, k • v ∈ A) →
      HasMax w (∏ τ : E →+* ℂ, idealAt c A τ ^ Dw.mult τ) 1 := fun A a1 a2 => by
    have := hasMax_prod hw Finset.univ (fun τ => idealAt c A τ ^ Dw.mult τ) (fun _ => 1) fun τ => by
      obtain ⟨a, y, hy, b⟩ := detSet_max _ (hwτ τ) A (hnat τ) a1 a2
      have h : HasMax w (idealAt c A τ) 1 := by
        refine hasMax_span hw ?_ ⟨_, ⟨_, hy, rfl⟩, b⟩
        rintro _ ⟨y, hy, rfl⟩
        exact a y hy
      simpa using h.pow hw (Dw.mult τ)
    simpa using this
  have hb : HasMax w (Submodule.span (𝓞 c.F) {β}) (w β) := hasMax_span hw (by simp) (by simp)
  have f1 := hb.mul (hm Λ.La h1 h2)
  rw [hβ] at f1
  have f := f1.unique (hm Λ.Ln (fun v hv => h1 v hv.1)
    (fun v hv => ⟨h2 v hv, (stdLat E n).toAddSubgroup.nsmul_mem hv k⟩))
  rw [_root_.mul_one] at f
  have f' : la.valuation c.F β = 1 := f
  simp [vLa, f']

theorem vLa_betaH {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) {n : ℕ} (Λ : GenLat D.host.E n)
    (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D)) (hA : PullbackSections.AdaptAt Λ la) :
    vLa la (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 0 := by
  have h := hF.sh.beta j hj n (hF.p.kPsi j hj) Λ hU hT
  refine vLa_beta (Dw := T.Q.Dw j) T.Q.c Λ la hA _ ?_
  unfold betaH
  rw [dite_eq_left h]
  exact h.choose_spec.2.1

end GlobalTheory.ShortUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramified
namespace GlobalTheory.TwistedKernelChar

section General

open NumberField IsDedekindDomain Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem inf_triv [_root_.NumberField.IsTotallyComplex L] (χ : HChar L) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hpow : ∀ x, χ.1 x ^ n = 1 := fun x => by
    have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
    simpa using h1
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz0 : e.symm z ≠ 0 := by
    intro h0
    have h1 : z = 0 := by simpa using congrArg e h0
    rw [h1, zero_pow hn.ne'] at hz
    exact (atInf w k).ne_zero (e.injective (by rw [← hz, map_zero]))
  have hk : atInf w k = Units.mk0 _ hz0 ^ n := Units.ext (e.injective (by
    rw [← hz, Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, RingEquiv.apply_symm_apply]))
  rw [MonoidHom.comp_apply, hk, map_pow, map_pow, hpow]

theorem hasInf_mul_inv {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n m : I → ℤ} {α β γ : HChar L}
    (ha : α.HasInf φ n) (hb : ∀ k, β.inf k = 1) (hc : γ.HasInf φ m) : (α * β * γ⁻¹).HasInf φ (fun i => n i - m i) := by
  intro k
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, hb, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, ha k, hc k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have h1 : φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero h0 (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 h0))
  rw [zpow_sub₀ h1, div_eq_mul_inv (_ ^ _)]

end General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem frame_char (D : D7) (C : Formalism.L2.Host.CharFrame D) (i : Fin D.R.m) (l : ℕ) :
    ∃ (b : ℕ) (n : D.R.Psi → ℤ), b ≠ 0 ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∈ Q.asIdeal → ((badN D : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → (C.mu0 i * C.delAt l * C.eta⁻¹).UnrAt Q) ∧
      (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q →
        ∀ k : D.host.Fˣ, (C.mu0 i * C.delAt l * C.eta⁻¹).resFin (Q.under (𝓞 D.host.F)) k = 1) ∧
      (∀ Q, (C.mu0 i * C.delAt l * C.eta⁻¹).TameAt Q) ∧
      (C.mu0 i * C.delAt l * C.eta⁻¹).HasInf (Formalism.L2.Host.embPsi D.host) n := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨p, hp, hpl, hδ⟩ : ∃ p : ℕ, p.Prime ∧ p ∈ D.host.levelPrimes ∧ Formalism.L2.Host.IsDelta (H := D.host) p (C.delAt l) := by
    unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    · exact ⟨_, D.host.pde'_prime, D.host.pde_level.2, C.isDel'⟩
    · exact ⟨_, D.host.pde_prime, D.host.pde_level.1, C.isDel⟩
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ∀ a b : ℕ, a ∣ b → (a : 𝓞 D.host.E) ∈ Q.asIdeal →
      (b : 𝓞 D.host.E) ∈ Q.asIdeal := by
    rintro Q a b ⟨u, rfl⟩ h
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h
  have lev : ∀ a ∈ D.host.levelPrimes, a ∣ badN D := fun a ha =>
    Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p => p) ha) _
  obtain ⟨n, -, hn⟩ := (C.isMu0 i).inf
  obtain ⟨o, ho, hod⟩ := hδ.fin
  refine ⟨D.host.g 0 * D.host.g 1 * p, fun τ => n τ - 1,
    mul_ne_zero (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero) hp.ne_zero, fun Q hQ => ?_,
    fun Q hQ x hx => ?_, fun Q hQ x => ?_, fun Q x hx hx' => ?_,
    hasInf_mul_inv hn (inf_triv _ ho hod) C.isEta.inf⟩
  · rw [Nat.cast_mul, Nat.cast_mul] at hQ
    rcases Q.isPrime.mem_or_mem hQ with h | h
    · rcases Q.isPrime.mem_or_mem h with h | h
      · exact key Q _ _ (lev _ (D.host.g_level 0)) h
      · exact key Q _ _ (lev _ (D.host.g_level 1)) h
    · exact key Q _ _ (lev _ hpl) h
  · have a1 : (C.mu0 i).UnrAt Q := (C.isMu0 i).unr Q fun j hj => hQ (key Q _ _ (by
      refine Dvd.dvd.mul_right ?_ p
      rw [← Fin.prod_univ_two D.host.g]
      exact Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)) hj)
    have a2 : (C.delAt l).UnrAt Q := hδ.unr Q fun hj => hQ (key Q _ _ (Dvd.intro_left _ rfl) hj)
    change (C.mu0 i).loc Q x * (C.delAt l).loc Q x * ((C.eta.loc Q x)⁻¹) = 1
    rw [a1 x hx, a2 x hx,
      C.isEta.unr Q x hx, inv_one, one_mul, one_mul]
  · rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
      (C.isMu0 i).triv.1, hδ.triv.1, C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
      Finset.card_pair hQ.symm, ite_eq_right (by norm_num), inv_one, one_mul, one_mul]
  · change (C.mu0 i).loc Q x * (C.delAt l).loc Q x * ((C.eta.loc Q x)⁻¹) = 1
    rw [(C.isMu0 i).tame Q x hx hx',
      hδ.tame Q x hx hx', C.isEta.unr Q x hx, inv_one, one_mul, one_mul]


set_option maxHeartbeats 800000 in
theorem twisted_kernel_char : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i _ v _ _ _ _ _ _ _ _ ℓ _ _ χ ξR ω φ hK Λ h N _ _ _ _ _ e Ps yd _ _ hb
  obtain ⟨b, n, h0, h1, h2, h3, h4, h5⟩ := frame_char D R.C i (Formalism.EigenvalueLevelCeiling.plc v)
  refine ⟨_, b, _, _, _, n, h0, fun Q hQ hm => hb Q hQ ?_,
    GlobalTheory.ClassScalarValue.chrEq_mul_inv (hC.lev.mu0 i) hK.chr hC.lev.eta, h2, h3, h4, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (h1 Q hm)

end GlobalTheory.TwistedKernelChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramifiedStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  first | exact @GlobalTheory.TwistedKernelChar.twisted_kernel_char | exact GlobalTheory.TwistedKernelChar.twisted_kernel_char | (intros; apply GlobalTheory.TwistedKernelChar.twisted_kernel_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.BetaInvIntegral

theorem betaH_inv_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  intro D T hF j hj n Λ σ p hp hU hT hTp
  have hβ : betaH (Dw := T.Q.Dw j) T.Q.c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  obtain ⟨M, hM, hint⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hp
    (betaH (Dw := T.Q.Dw j) T.Q.c Λ)⁻¹ (fun w hw => by
      obtain ⟨k, hk, h1, h2⟩ := hTp
      have hA : ReciprocityTheory.ChartRestriction.G.PullbackSections.AdaptAt Λ w :=
        ⟨k, GlobalTheory.ShortUnits.not_mem_of_coprime' w hk.symm hw, h1, h2⟩
      have hv := GlobalTheory.ShortUnits.vLa_betaH T hF j hj Λ w hU hT hA
      have hne : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) ≠ 0 := by simpa using hβ
      have h1' : w.valuation T.Q.c.F (betaH (Dw := T.Q.Dw j) T.Q.c Λ) = 1 := by
        rw [← WithZero.exp_log hne]
        simp only [vLa, neg_eq_zero] at hv
        rw [hv]; rfl
      rw [map_inv₀, h1', inv_one])
  refine ⟨M, hM, ?_⟩
  have := map_isIntegral_int σ hint
  simpa [map_mul, map_inv₀, map_natCast] using this

end GlobalTheory.BetaInvIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegralStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  first | exact @GlobalTheory.BetaInvIntegral.betaH_inv_integral | exact GlobalTheory.BetaInvIntegral.betaH_inv_integral | (intros; apply GlobalTheory.BetaInvIntegral.betaH_inv_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPoint
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.DetIdealPrime

theorem exists_ideal_coprime : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  intro D V hg hL h e P y he hs hy b hb c ψ hc hu hr Λ hΛ p hp hT
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e P y he hs hy b hb c ψ hc hu hr
  refine ⟨cc, c0, c2, ?_, c4⟩
  refine GlobalTheory.NormCoprime.coprime_absNorm_of_sup p hp c0 ?_
  obtain ⟨k, hk, -, hk2⟩ := hT
  have hdet : ((k : D.host.E) ^ V.rank) ∈ Submodule.span (𝓞 D.host.E) (detSet (Bridge.hLat V (fin V h))) := by
    refine Submodule.subset_span ⟨fun i => (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E), fun i => ?_, ?_⟩
    · have hstd : (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
        rw [Formalism.L2.Pj.stdLat, Submodule.mem_pi]
        intro j _
        by_cases hj : j = i
        · subst hj; simpa using (Submodule.one_le.1 le_rfl : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E))
        · simp [Pi.single_apply, hj]
      have h1 := hk2 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (k : 𝓞 D.host.E)) hstd)
      have h2 : ((k : 𝓞 D.host.E) • (Pi.single i (1 : D.host.E) : Fin V.rank → D.host.E)) =
          (k : D.host.E) • (Pi.single i 1 : Fin V.rank → D.host.E) := by
        rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) k, algebraMap_smul]
      rw [h2] at h1
      have h3 := (hΛ _).1 h1
      convert h3 using 1
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · have : (Matrix.of fun i j => ((k : D.host.E) • (Pi.single j 1 : Fin V.rank → D.host.E)) i) =
          (k : D.host.E) • (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) := by
        ext i j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hcM : cc ≤ M := le_trans le_sup_left hle
  have hpM : ((p : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hkM : ((k : ℕ) : 𝓞 D.host.E) ∉ M := by
    intro hkM
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
    have e1 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at e1
    refine hM.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e1]
    exact M.add_mem (M.mul_mem_left _ hkM) (M.mul_mem_left _ hpM)
  have hkn : ((k : ℕ) : 𝓞 D.host.E) ^ V.rank ∉ M := fun h0 => hkM (hM.isPrime.mem_of_pow_mem _ h0)
  have hc'M : cc.map (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ M := by
    intro x hx
    have hm : (k : D.host.E) ^ V.rank * (x : D.host.E) ∈ idlE cc := by
      rw [← c3]
      exact Submodule.mul_mem_mul hdet ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzeq⟩ := hm
    have hz' : z = ((k : ℕ) : 𝓞 D.host.E) ^ V.rank * x := by
      apply RingOfIntegers.ext
      rw [show (z : D.host.E) = Algebra.linearMap (𝓞 D.host.E) D.host.E z from rfl, hzeq]
      push_cast
      rfl
    rw [hz'] at hz
    exact ((hM.isPrime.mem_or_mem (hcM hz)).resolve_left hkn)
  exact hM.ne_top (top_le_iff.1 (c1 ▸ sup_le hcM hc'M))

end GlobalTheory.DetIdealPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.DetIdealPrime.exists_ideal_coprime | exact GlobalTheory.DetIdealPrime.exists_ideal_coprime | (intros; apply GlobalTheory.DetIdealPrime.exists_ideal_coprime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnId
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.TameHeckeIntegral

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_onId (E : Type) [Field E] [NumberField E] (ψ : HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ)
    (n : I → ℤ) (hinf : ψ.HasInf φs n) (ht : ∀ v, ψ.TameAt v) (b : ℕ) (hb : b ≠ 0)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) (cc : Ideal (𝓞 E)) (hcc : cc ≠ ⊥)
    (hcop : cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤) :
    UnitOff (Ideal.absNorm cc) ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ) := by
  classical
  have hb0 : (b : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hfin : {w | ¬ ψ.UnrAt w}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(b : 𝓞 E)}) (by simpa using hb0)).subset fun w hw => ?_
    have hbw : (b : 𝓞 E) ∈ w.asIdeal := by
      by_contra h
      exact hw (hu w h)
    show w.asIdeal ∣ Ideal.span {(b : 𝓞 E)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hbw
  have hcc0 : cc ≠ 0 := hcc
  unfold HChar.onId
  refine finprod_induction (fun u : ℂˣ => UnitOff (Ideal.absNorm cc) (u : ℂ)) (by simpa using unitOff_one _)
    (fun x y hx hy => by simpa [Units.val_mul] using unitOff_mul hx hy) fun v => ?_
  show UnitOff _ (((ψ.val v ^ FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ)) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]
  by_cases hdv : v.asIdeal ∣ cc
  · have hle : cc ≤ v.asIdeal := Ideal.le_of_dvd hdv
    have hbv : (b : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top (by
      rw [eq_top_iff, ← hcop]
      exact sup_le hle (by rw [Ideal.span_singleton_le_iff_mem]; exact h))
    have hq : ((Ideal.absNorm cc : ℕ) : 𝓞 E) ∈ v.asIdeal := hle (Ideal.absNorm_mem cc)
    exact unitOff_zpow (GlobalTheory.ValUnit.unitOff_val E ψ I φs n v _ hinf hfin ht (hu v hbv) hq) _
  · have h0 : FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0 := by
      rw [FractionalIdeal.count_coe E v hcc0, Nat.cast_eq_zero]
      by_contra h
      exact hdv ((Associates.count_ne_zero_iff_dvd hcc0 (HeightOneSpectrum.prime v).irreducible).1 h)
    rw [h0, zpow_zero]
    exact unitOff_one _

theorem isIntegral_absNorm_pow_mul_onId : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  intro E _ _ ψ I _ φs n hinf ht b hb hu cc hcc hcop
  obtain ⟨_, K, hK, _⟩ := unitOff_onId E ψ I φs n hinf ht b hb hu cc hcc hcop
  exact ⟨K, hK⟩

end GlobalTheory.TameHeckeIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralAbsNormPowMulOnIdStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | exact GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId | (intros; apply GlobalTheory.TameHeckeIntegral.isIntegral_absNorm_pow_mul_onId <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.ClassScalarIntegral


set_option maxHeartbeats 1000000 in
theorem class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM hLN hΛ e Ps yd hh he hPs hs hy hcard a ha lam hTl
  have lemL1 := GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral
  have lemHV := GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime
  have lemCC := GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint
  have lemPSI := GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified
  obtain ⟨ψ, b, I, _, φs, n, hb0, hbP, hc, hu, hr, htame, hinf⟩ :=
    lemPSI D G Pl0 T0 A T R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM
      hLN hΛ e Ps yd hh he hPs
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime lam
  obtain ⟨cc, c0, cb, cl, cv⟩ := lemCC D (Vc D i) hO.2.lift.std.1 hO.2.lift.std.2 h e Ps yd he hs hy b hbP _ ψ hc hu hr Λ hΛ
    (Formalism.EigenvalueLevelCeiling.plc lam) hp hTl
  obtain ⟨K, hK1⟩ := lemHV D.host.E ψ I φs n hinf htame b hb0 hu cc c0 cb
  obtain ⟨m, hm, hm1⟩ := lemL1 D T hT ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ Λ (O i).s0 (Formalism.EigenvalueLevelCeiling.plc lam) hp hU hTb hTl
  refine ⟨((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL), ?_, ?_⟩
  · intro hmem
    have hco : Nat.Coprime (m * Ideal.absNorm cc ^ K) (Formalism.EigenvalueLevelCeiling.plc lam) := Nat.Coprime.mul_left hm (Nat.Coprime.pow_left _ cl)
    have h1 : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem lam
    obtain ⟨u, w, huw⟩ : IsCoprime ((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL) ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) :=
      Nat.Coprime.cast hco
    exact lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huw ▸ lam.asIdeal.add_mem (lam.asIdeal.mul_mem_left _ hmem) (lam.asIdeal.mul_mem_left _ h1)))
  · have hinj : Function.Injective D.what₂.embLL.toIntAlgHom := D.what₂.embLL.injective
    refine (isIntegral_algHom_iff _ hinj).1 ?_
    have e1 : D.what₂.embLL.toIntAlgHom (((((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL)) : D.what₂.LL) * a) =
        ((m : ℂ) * ((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹) *
        (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ)) *
        ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) := by
      rw [RingHom.toIntAlgHom_apply, map_mul, ha, ← cv]
      push_cast
      rw [map_mul, map_pow, map_natCast, map_natCast]
      ring
    rw [e1]
    refine (hm1.mul hK1).mul ?_
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Nat.cast_pow, Complex.ofReal_natCast]
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ D.R.r : ℕ) : ℤ)))

end GlobalTheory.ClassScalarIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_kernel_class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  first | exact @GlobalTheory.ClassScalarIntegral.class_scalar_integral | exact GlobalTheory.ClassScalarIntegral.class_scalar_integral | (intros; apply GlobalTheory.ClassScalarIntegral.class_scalar_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistScalarMemRange
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.TwistScalarField

open NumberField IsDedekindDomain

theorem val_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    (χ₁ * χ₂).val v = χ₁.val v * χ₂.val v :=
  by rfl

theorem onId_mul {L : Type} [Field L] [NumberField L] (χ₁ χ₂ : Formalism.L2.Host.HChar L)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := by
  unfold Formalism.L2.Host.HChar.onId
  have hfin := Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := L) I)
  have hs : ∀ χ : Formalism.L2.Host.HChar L,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v I).Finite :=
    fun χ => hfin.subset fun v hv h0 => hv (by show χ.val v ^ _ = 1; rw [h0, zpow_zero])
  rw [← finprod_mul_distrib (hs χ₁) (hs χ₂)]
  exact finprod_congr fun v => by rw [val_mul, mul_zpow]

theorem onId_mem_range {L C : Type} [Field L] [NumberField L] [Field C] (emb : C →+* ℂ) (ξ : Formalism.L2.Host.HChar L)
    (h : ∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ emb.range) (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :
    ((ξ.onId I : ℂˣ) : ℂ) ∈ emb.range := by
  let S : Subgroup ℂˣ :=
    { carrier := {u | (u : ℂ) ∈ emb.range}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y, hy⟩ := hb
        exact ⟨x * y, by rw [map_mul, hx, hy, Units.val_mul]⟩
      one_mem' := ⟨1, by rw [map_one, Units.val_one]⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨x, hx⟩ := ha
        exact ⟨x⁻¹, by rw [map_inv₀, hx, Units.val_inv_eq_inv_val]⟩ }
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), ξ.val v ∈ S := fun v => h _
  exact finprod_induction (· ∈ S) S.one_mem (fun _ _ => S.mul_mem) (fun v => S.zpow_mem (hv v) _)


set_option maxHeartbeats 1000000 in
theorem twist_scalar_mem_range : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∃ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv htup hQG hF0 hVal hdel hMb hRun ℓ hLev hAct χ ξR ω φ hK Λ h N hU hTb hTl hLevOK hconj e Ps yd hh he hPs hPsO hs hy hcard
  classical
  have hpq : D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q :=
    (hT.p.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.J.toCore.good_σ₀).1
  have hInR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hlev := hT.sh.dLev _ hInR (Vc D i).rank
  obtain ⟨pp, -, hpd⟩ := hT.sh.dPd
  have hpd1 := hRun.2.1
  rw [hpd _ hInR] at hpd1
  have hpd2 : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).pd = ownAt D v := by rw [hpd _ hInR, hpd1]
  have hL := hC.lev
  have hstd := hO.2.lift.std
  have hbadO := hO.2.bad ()
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad () := ⟨_, rfl⟩
  have hbPs : ∀ PP ∈ Ps, ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP hm => by
    rw [hb, Nat.cast_mul (badN D * _)] at hm
    rcases PP.isPrime.mem_or_mem hm with h1 | h1
    · exact hPs PP hP h1
    · exact hPsO PP hP h1
  have h2b : 2 ∣ b := hb ▸ dvd_mul_of_dvd_right hbadO.2.1 _
  have hMb' : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∣ b := hb ▸ dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have g := GlobalTheory.AdTh.SerOne.guard_of_splitOffBad (Vc D i) hstd.1 hstd.2 _ h2b hMb' ⟨hh, e, Ps, he, hbPs, hs⟩
  obtain ⟨gU, ⟨k, hk1, hk2, hk3⟩, gS⟩ := g
  have gT : (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank).TrivAt ((O i).bad ()) :=
    ⟨k, Nat.Coprime.coprime_dvd_right (hb ▸ dvd_mul_left _ _) hk1, hk2, hk3⟩
  have hΛ : Λ = GlobalTheory.ClassScalarCompare.conjLat (Bridge.hLat (Vc D i) (fin (Vc D i) h)) := by
    cases Λ with
    | mk La => congr 1; ext w; exact hconj w
  have memb : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((ownAt D v : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      ((b : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := fun Q hQ => by
    rw [hb, hlev.2.1, hpd2, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hQ))
  have hbar : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal (Vc D i) hstd.1 hstd.2 h e Ps yd he hs hy b hbPs
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 (R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹)
    (GlobalTheory.ClassScalarValue.chrEq_mul_inv (hL.mu0 i) hK.chr hL.eta)
    (fun Q hQ x hx => by
      have a1 : (R.C.mu0 i).UnrAt Q := (R.C.isMu0 i).unr Q fun j hj => hQ (by
        obtain ⟨u, hu⟩ := (Finset.dvd_prod_of_mem D.host.g (Finset.mem_univ j)).trans
          ((Fin.prod_univ_two D.host.g).symm ▸ hbadO.2.2.2.2)
        rw [hb, hu]
        simp only [Nat.cast_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hj))
      have a2 : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).UnrAt Q := by
        by_contra hn
        rcases (hK.ram Q).1 hn with a | ⟨Q', a, a'⟩
        · exact hQ (memb Q (Finset.mem_filter.1 a).2)
        · rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 a', GlobalTheory.IdemSupport.mem_cP, map_natCast] at hQ
          exact hQ (memb Q' (Finset.mem_filter.1 a).2)
      change (R.C.mu0 i).loc Q x * (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).loc Q x * ((R.C.eta).loc Q x)⁻¹ = 1
      rw [a1 x hx, a2 x hx, R.C.isEta.unr Q x hx, inv_one, one_mul, one_mul])
    (fun Q hQ x => by
      rw [Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_mul, Formalism.L2.Host.HChar.resFin_inv,
        (R.C.isMu0 i).triv.1, hK.triv.1, R.C.isEta.res.1, Formalism.L2.Host.etaFin, GlobalTheory.ClassScalarValue.above_eq,
        Finset.card_pair hQ.symm, if_neg (by norm_num), inv_one, one_mul, one_mul])
  rw [← hbar] at c1 c3
  obtain ⟨q, q0, q1, q2⟩ := (hO.2.ep ()).2 _ cc gU gT gS c1 c3
  have c2' : cc ⊔ Ideal.span {(((O i).bad () : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    refine top_le_iff.1 (c2 ▸ sup_le_sup_left (Ideal.span_singleton_le_span_singleton.2 ?_) _)
    rw [hb]; exact Nat.cast_dvd_cast (dvd_mul_left _ _)
  have hB := (hO.2.tuple ()).B cc c0 c2'
  have hxi : R.xiH A.μ0 = 1 := hL.xi_base
  have S1 : ∀ (χ₁ χ₂ : Formalism.L2.Host.HChar D.host.E) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
      (χ₁ * χ₂).onId I = χ₁.onId I * χ₂.onId I := fun χ₁ χ₂ I => onId_mul χ₁ χ₂ I
  have S2 : ∀ (ξ : Formalism.L2.Host.HChar D.host.E), (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) →
      ∀ I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, ((ξ.onId I : ℂˣ) : ℂ) ∈ D.what₂.embLL.range :=
    fun ξ hξ I => onId_mem_range D.what₂.embLL ξ hξ I
  have e1 : R.C.mu0 i * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) * R.C.eta⁻¹ =
      (R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹) * R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) := by
    rw [hxi, mul_one, mul_right_comm]
  rw [e1, S1, Units.val_mul] at c4
  obtain ⟨a3, ha3⟩ := S2 _ hdel (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  have hF := hO.1
  have memF : ∀ x : (O i).c'.F, ∃ a : D.what₂.LL, D.what₂.embLL a = (x : ℂ) := fun x => by
    obtain ⟨a, ha⟩ := AlgHom.mem_fieldRange.1 ((SetLike.ext_iff.1 hF (x : ℂ)).1 x.2)
    exact ⟨a, ha⟩
  obtain ⟨a1, ha1⟩ := memF (incF T.Q.c (O i).c' (O i).hle (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))
  obtain ⟨a2, ha2⟩ := memF ((O i).B () cc)
  have hi : GlobalTheory.ClassScalarCompare.stdIndex Λ =
      GlobalTheory.ClassScalarCompare.stdIndex (⟨Bridge.hLat (Vc D i) (fin (Vc D i) h)⟩ : GenLat D.host.E (Vc D i).rank) := by
    rw [hΛ]; exact GlobalTheory.ClassScalarCompare.stdIndex_conjLat _
  have q1' : (q : ℝ) ^ 2 * ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) := by
    rw [hi, hpq]; exact_mod_cast q1
  have hsq : ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ) =
      ((Real.sqrt (Ideal.absNorm cc : ℝ) : ℝ) : ℂ) * ((q : ℂ))⁻¹ := by
    have hq : (0:ℝ) < q := by exact_mod_cast q0
    have e2 : ((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r = (Ideal.absNorm cc : ℝ) / (q : ℝ) ^ 2 := by
      rw [← q1']; field_simp
    rw [e2, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hq.le, Complex.ofReal_div, div_eq_mul_inv,
      Complex.ofReal_ratCast]
  have h1 : (O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ) = D.what₂.embLL a1 := ha1.symm
  beta_reduce at hB
  have h2 := ha2.trans hB
  refine ⟨a1⁻¹ * a2 * a3 * ((q⁻¹ : ℚ) : D.what₂.LL), ?_⟩
  change _ = _ * _ * ((Real.sqrt (((GlobalTheory.ClassScalarCompare.stdIndex Λ : ℕ) : ℝ) ^ D.R.r) : ℝ) : ℂ)
  rw [h1, c4, hsq, map_mul, map_mul, map_mul, map_inv₀, map_ratCast, h2, ha3]
  push_cast
  ring

end GlobalTheory.TwistScalarField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandard
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.TwistClassScalar

set_option maxHeartbeats 800000

theorem twist_class_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → ∃ c1 : D.what₂.LL, D.what₂.embLL c1 * (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹) = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) ∧ ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c1) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hPb hs hy
  have hz := GlobalTheory.ClassScalarValue.zCard_eq Λ N D.R.r hLev.2.2
  have hm : Λ.mIdx N D.R.r ≠ 0 := GlobalTheory.ClassScalarValue.mIdx_ne_zero Λ D.R.r (fun h0 => by
    obtain ⟨k, hk⟩ := hLev.1
    omega)
  by_cases hK0 : Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0
  · obtain ⟨a, ha⟩ := GlobalTheory.TwistScalarField.twist_scalar_mem_range D G Pl0 T0 A T R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hPb hs hy hK0
    refine ⟨a, ?_, GlobalTheory.T.twisted_kernel_class_scalar_integral D G Pl0 T0 A T R F κ v₀ fw O hT hC i hP v hv htm hQ hF hV hdel hMb hRun ℓ hLv hAc χ ξR ω φ hK Λ h N hU hTb hTM hLev hLa e Ps yd hh he hPs hs hy hK0 a ha⟩
    rw [ha, hz]
    have hc : (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hs2 : ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) ^ 2 = ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℂ) ^ D.R.r) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
      push_cast; rfl
    have hmC : ((Λ.mIdx N D.R.r : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm
    push_cast
    rw [GenLat.Ln] at *
    field_simp
    rw [hs2]
  · refine ⟨0, ?_, fun lam _ => ⟨1, fun h1 => lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using isIntegral_zero⟩⟩
    rw [not_not] at hK0
    rw [hK0]
    simp

end GlobalTheory.TwistClassScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegralStandardStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_kernel_class_scalar_integral_standard : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → ∃ c1 : D.what₂.LL, D.what₂.embLL c1 * (((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ)⁻¹ * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹) = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * ((Λ.mIdx N D.R.r : ℂ))⁻¹ * ((Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) : ℂ))⁻¹ * (Λ.zCard N D.R.r : ℂ)) ∧ ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c1) := by
  first | exact @GlobalTheory.TwistClassScalar.twist_class_scalar | exact GlobalTheory.TwistClassScalar.twist_class_scalar | (intros; apply GlobalTheory.TwistClassScalar.twist_class_scalar <;> assumption)
end
