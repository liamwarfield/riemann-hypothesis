module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.LocTransfer
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThird

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (A : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · exact (map_zero f).symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem regAt_neg {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    RegAt x (mCoordIdeal z) (-s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨d, -g, h, fun m hm k => hg m (by rwa [support_neg] at hm) k, hh, hn, ?_⟩
  rw [map_neg, heq, neg_mul]

def regRing (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {s | RegAt x (mCoordIdeal z) s}
  mul_mem' := ValRing.regAt_mul
  one_mem' := ValRing.regAt_one x z
  add_mem' := ValRing.regAt_add
  zero_mem' := ValRing.regAt_zero x z
  neg_mem' := regAt_neg

def regVal (x : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) : regRing x z →+* ℂ where
  toFun s := valAt x s z
  map_one' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1
  map_zero' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1
  map_mul' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.1
  map_add' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.2

def valMat {N : ℕ} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (A : Matrix (Fin N) (Fin N) Ω) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a b => valAt x (A a b) z

variable {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_sum (hz : z ∈ mcPts (mCoordIdeal x)) {σ : Type} (s : Finset σ) (f : σ → Ω)
    (hf : ∀ i ∈ s, RegAt x (mCoordIdeal z) (f i)) :
    RegAt x (mCoordIdeal z) (∑ i ∈ s, f i) ∧ valAt x (∑ i ∈ s, f i) z = ∑ i ∈ s, valAt x (f i) z := by
  revert hf
  refine Finset.induction_on s ?_ (fun a s ha ih hf => ?_)
  · intro _
    simp only [Finset.sum_empty]
    exact ⟨(ValRing.regAt_valAt_ring K ι Ω x z hz).1, (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1⟩
  · rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨-, hadd, -, hval⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 _ _ hfa h1
    exact ⟨hadd, by rw [hval, h2]⟩

theorem reg_mul (hz : z ∈ mcPts (mCoordIdeal x)) {s t : Ω} (hs : RegAt x (mCoordIdeal z) s)
    (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z := by
  obtain ⟨hm, -, hv, -⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t hs ht
  exact ⟨hm, hv⟩

theorem regMat_mul {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A B : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (hB : ∀ a b, RegAt x (mCoordIdeal z) (B a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b)) ∧ valMat x z (A * B) = valMat x z A * valMat x z B := by
  have key : ∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b) ∧
      valAt x ((A * B) a b) z = ∑ c, valAt x (A a c) z * valAt x (B c b) z := by
    intro a b
    rw [Matrix.mul_apply]
    obtain ⟨h1, h2⟩ := reg_sum hz Finset.univ (fun c => A a c * B c b)
      (fun c _ => (reg_mul hz (hA a c) (hB c b)).1)
    refine ⟨h1, ?_⟩
    rw [h2]
    exact Finset.sum_congr rfl fun c _ => (reg_mul hz (hA a c) (hB c b)).2
  refine ⟨fun a b => (key a b).1, ?_⟩
  ext a b
  simp only [valMat, Matrix.of_apply, Matrix.mul_apply]
  exact (key a b).2

theorem reg_minor {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (I J : Finset (Fin N)) :
    RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (valMat x z A) I J := by
  let A' : Matrix (Fin N) (Fin N) (regRing x z) := fun a b => ⟨A a b, hA a b⟩
  have hmap : A'.map (regRing x z).subtype = A := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : regRing x z) : Ω) := by
    have h := minorIJ_map (regRing x z).subtype A' I J
    rw [hmap] at h
    exact h
  have h2 : valMat x z A = A'.map (regVal x hz) := by
    ext a b
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h2, minorIJ_map, h1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def proj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * starRingEnd ℂ (z ⟨q.1, q.2.2⟩) / ((∑ i, ‖z ⟨q.1, i⟩‖ ^ 2 : ℝ) : ℂ)

def Pts (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Set ((Σ k, ι k × ι k) → ℂ) :=
  proj '' conePts P

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

def rep (x : Pts P) : (Σ k, ι k) → ℂ := x.2.choose

theorem rep_mem (x : Pts P) : rep x ∈ conePts P := x.2.choose_spec.1

theorem proj_rep (x : Pts P) : proj (rep x) = x.1 := x.2.choose_spec.2


variable (P) in
def src (p : (k : K) → ι k) : Set (Pts P) := {x | ∀ k, rep x ⟨k, p k⟩ ≠ 0}


variable (P) in
def coord (p : (k : K) → ι k) (x : Pts P) : Fin (Fintype.card (Σ k, ι k)) → ℂ :=
  renPt (affCoord p (rep x))


variable (P) in
def ideal (p : (k : K) → ι k) : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  (chartIdeal P p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)


open Classical in
def lift (p : (k : K) → ι k) (q : Σ k, ι k) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  if q.2 = p q.1 then 1 else X (Fintype.equivFin (Σ k, ι k) q)


variable (P) in
def bd (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  ((chartIdeal (P ⊔ D) p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)).radical

theorem finite_minimalPrimes (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : I.minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ I


variable (P) in
def rc (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : ℕ := (finite_minimalPrimes (P ⊔ D)).toFinset.card


variable (P) in
def compIdeal (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).1


variable (P) in
def comp (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Set (Pts P) :=
  {x | ∀ f ∈ compIdeal P D k, eval (rep x) f = 0}

def ordAlong (Q P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) : ℕ :=
  sSup {m : ℕ | ∃ s ∉ Q, s * f ∈ Q ^ m ⊔ P}

theorem compIdeal_mem (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) :
    compIdeal P D k ∈ (P ⊔ D).minimalPrimes := by
  exact (Set.Finite.mem_toFinset _).1 ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).2

theorem eval_lift (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    eval (coord P p x) (lift p q) = affCoord p (rep x) q := by
  classical
  unfold lift
  split_ifs with h
  · obtain ⟨k, i⟩ := q
    simp only at h
    subst h
    simp [affCoord, hx k]
  · simp [coord, renPt]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpan
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem basis_image {Ω M N ι : Type} [Field Ω] [AddCommGroup M] [Module Ω M] [AddCommGroup N] [Module Ω N]
    (b : Module.Basis ι Ω M) (f : M →ₗ[Ω] N) (hf : Function.Injective f) :
    LinearIndependent Ω (fun a => f (b a)) ∧
      Submodule.span Ω (Set.range fun a => f (b a)) = (⊤ : Submodule Ω M).map f := by
  refine ⟨b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  have h : (Set.range fun a => f (b a)) = f '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, b.span_eq]

theorem inW_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x) :
    Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x)
    (τ : CMType H) : Function.Injective (inO A τ) := by
  classical
  unfold inO
  rw [LinearMap.coe_comp]
  refine LinearMap.inr_injective.comp ?_
  rw [LinearMap.coe_single]
  exact Pi.single_injective τ

theorem cc_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO s
  rcases s with τ | τ
  · have h := basis_image (bW τ) ((inW 𝔐).comp (𝔐.Vgen (.inl τ)).subtype)
      ((inW_injective 𝔐).comp Subtype.val_injective)
    rw [Submodule.map_comp, Submodule.map_subtype_top] at h
    exact h
  · exact basis_image (bO τ) (inO 𝔐 τ) (inO_injective 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpanStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_bases_linearIndependent_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [det_of_lowerTriangular (genU Ω r s) fun a b h => ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [genU]
  · have h' : a < b := h
    simp [genU, not_lt.2 h'.le, h'.ne]

variable (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ)

theorem wBlock_gMat : wBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inl τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (wEmb p q b) = .inr b := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (wEmb p q a)) ((blockEquiv p q).symm (wEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem omBlock_gMat : omBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inr τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (omEmb p q b) = .inl b := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (omEmb p q a)) ((blockEquiv p q).symm (omEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem detFac_gMat (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)) :
    detFac p i (gMat p q Ω τ) = 1 := by
  have hw : minorIJ (gMat p q Ω τ) (wIdx (p + q) p) (wIdx (p + q) p) = 1 := by
    rw [minorIJ_wIdx, wBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inl τ)
  have ho : minorIJ (gMat p q Ω τ) (omIdx (p + q) p) (omIdx (p + q) p) = 1 := by
    rw [minorIJ_omIdx, omBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inr τ)
  simp only [detFac, hw, ho, ite_self, mul_one]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOneStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFac_gMat_eq_one : ∀ (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)), detFac p i (gMat p q Ω τ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalytic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalytic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.HoloLift

variable {e : ℕ} {V : Set (Fin e → ℂ)}

def inclChart (hV : IsOpen V) [Nonempty V] : OpenPartialHomeomorph V (Fin e → ℂ) :=
  hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem inclChart_source (hV : IsOpen V) [Nonempty V] : (inclChart hV).source = Set.univ := by
  simp [inclChart]

theorem inclChart_target (hV : IsOpen V) [Nonempty V] : (inclChart hV).target = V := by
  simp [inclChart]

theorem inclChart_apply (hV : IsOpen V) [Nonempty V] (y : V) : inclChart hV y = y := by
  simp [inclChart]

theorem val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    (((inclChart hV).symm w : V) : Fin e → ℂ) = w := by
  have h := (inclChart hV).right_inv (x := w) (by rw [inclChart_target]; exact hw)
  rwa [inclChart_apply] at h

theorem eventually_val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    ∀ᶠ w' in 𝓝 w, (((inclChart hV).symm w' : V) : Fin e → ℂ) = w' := by
  filter_upwards [hV.mem_nhds hw] with w' hw' using val_inclChart_symm hV hw'

def inclAtlas (hV : IsOpen V) [Nonempty V] : FinHolAtlas e V where
  n := 1
  chart _ := inclChart hV
  cover x := ⟨0, by rw [inclChart_source]; trivial⟩
  holo j k := by
    rintro w ⟨hw, -⟩
    rw [inclChart_target] at hw
    refine analyticAt_id.congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw] with w' hw'
    simp only [Function.comp, inclChart_apply, hw', id]

end GlobalTheory.CompanionTheory.Ar.PB.HoloLift


open GlobalTheory.CompanionTheory.Ar.PB.HoloLift in
theorem GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D), J = ⊤ → ∀ (V : Set (Fin e → ℂ)) (μ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (g : (Fin e → ℂ) → R.X), IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V) → (∀ u ∈ V, SameOrbit (R.lift (g u) (g u)) (μ u)) → ContinuousOn g V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ g) (V ∩ g ⁻¹' (R.A.chart k).source) := by
  intro K _ ι _ P J D e R hJ V μ g hV hμ hg
  subst hJ
  rcases V.eq_empty_or_nonempty with rfl | hne
  · refine ⟨continuousOn_empty _, fun k w hw => ?_⟩
    exact absurd hw.1 (Set.notMem_empty w)
  haveI : Nonempty V := hne.to_subtype
  let B : FinHolAtlas e V := inclAtlas hV
  let Vf : V → Set V := fun _ => Set.univ
  let μf : V → V → (Σ k, ι k) → ℂ := fun _ u => μ u
  let h : V → R.X := fun y => g y
  have hVo : ∀ y, IsOpen (Vf y) := fun _ => isOpen_univ
  have hVm : ∀ y, y ∈ Vf y := fun _ => Set.mem_univ _
  have hμf : ∀ y q, B.HoloOn (Vf y) fun u => μf y u q := by
    rintro y q j w ⟨hw, -⟩
    have hw' : w ∈ V := by simpa [B, inclAtlas, inclChart_target] using hw
    refine (hμ q w hw').congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw'] with w' h'
    simp only [Function.comp, μf, B, inclAtlas, h']
  have hc : ∀ y y', ∀ u ∈ Vf y ∩ Vf y', SameOrbit (μf y u) (μf y' u) := fun _ _ u _ =>
    Proj.orbit_trans (Proj.orbit_symm (hg u u.2)) (hg u u.2)
  have hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μf y y) := fun y => hg y y.2
  have hnz : ∀ y k, ∃ i, μf y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (h y) (h y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous h := CovMap.continuous_of_orbit_of_ne R B hVo hVm hμf hnz hc hh
  refine ⟨continuousOn_iff_continuous_restrict.2 hcont, fun k w hw => ?_⟩
  have hA := Proj.analytic_of_orbit R B hVo hVm hμf hc hh hcont (0 : Fin 1) k
  have hmem : w ∈ (B.chart (0 : Fin 1)).target ∩
      (B.chart (0 : Fin 1)).symm ⁻¹' (h ⁻¹' (R.A.chart k).source) := by
    refine ⟨by simpa [B, inclAtlas, inclChart_target] using hw.1, ?_⟩
    have e1 := val_inclChart_symm hV hw.1
    show g (((inclChart hV).symm w : V) : Fin e → ℂ) ∈ (R.A.chart k).source
    rw [e1]
    exact hw.2
  refine (hA w hmem).congr ?_
  filter_upwards [eventually_val_inclChart_symm hV hw.1] with w' h'
  show R.A.chart k (g (((inclChart hV).symm w' : V) : Fin e → ℂ)) = R.A.chart k (g w')
  rw [h']
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalyticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_to_log_resolution_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D), J = ⊤ → ∀ (V : Set (Fin e → ℂ)) (μ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (g : (Fin e → ℂ) → R.X), IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V) → (∀ u ∈ V, SameOrbit (R.lift (g u) (g u)) (μ u)) → ContinuousOn g V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ g) (V ∩ g ⁻¹' (R.A.chart k).source) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift | exact GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonempty
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonempty
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem exists_ratAlgHom_complex (A : Type) [CommRing A] [Nontrivial A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    Nonempty (A →ₐ[ℚ] ℂ) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
  let κ : (A ⧸ M) →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨κ.comp (Ideal.Quotient.mkₐ ℚ M)⟩

theorem aeval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {x : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal x) : aeval x f = 0 := by
  have h0 : mConeMap x f = 0 := hf
  have e : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap x).toRingHom) =
      (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro p
      simp [mConeMap]
  have := congrArg (fun g => g f) e
  simp only [RingHom.comp_apply] at this
  have h1 : (aeval x : MRing ι →ₐ[ℤ] Ω) f = (MvPolynomial.eval fun _ : K => (1 : Ω)) ((mConeMap x) f) := this.symm
  rw [h1, h0, map_zero]

theorem mcPts_mCoordIdeal_nonempty (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (x : (Σ k, ι k) → Ω) (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) : (mcPts (mCoordIdeal x)).Nonempty := by
  choose c hc using hx
  set u : Ω := ∏ k, x ⟨k, c k⟩ with hu
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  let S : Set Ω := Set.range x ∪ {u⁻¹}
  have hS : S.Finite := (Set.finite_range x).union (Set.finite_singleton _)
  let A : Subalgebra ℚ Ω := Algebra.adjoin ℚ S
  have : Algebra.FiniteType ℚ A := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨ρ⟩ := exists_ratAlgHom_complex A
  let xA : (Σ k, ι k) → A := fun p => ⟨x p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩
  let v : A := ⟨u⁻¹, Algebra.subset_adjoin (Or.inr rfl)⟩
  have huv : (∏ k, xA ⟨k, c k⟩) * v = 1 := by
    apply Subtype.ext
    have : ((∏ k, xA ⟨k, c k⟩ : A) : Ω) = u := by
      rw [hu]
      exact map_prod A.val _ _
    show ((∏ k, xA ⟨k, c k⟩ : A) : Ω) * u⁻¹ = 1
    rw [this, mul_inv_cancel₀ hu0]
  have hz : (∏ k, ρ (xA ⟨k, c k⟩)) * ρ v = 1 := by
    rw [← map_prod, ← map_mul, huv, map_one]
  refine ⟨fun p => ρ (xA p), fun k => ⟨c k, fun h0 => ?_⟩, fun f hf => ?_⟩
  · have : ∏ k, ρ (xA ⟨k, c k⟩) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [this, zero_mul] at hz
    exact zero_ne_one hz
  · have h1 : aeval xA f = 0 := by
      apply Subtype.ext
      have e : (A.val.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom) =
          (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro p
          simp [xA]
      have := congrArg (fun g => g f) e
      simp only [RingHom.comp_apply] at this
      exact this.trans (aeval_eq_zero_of_mem_mCoordIdeal hf)
    have e : ((MvPolynomial.eval fun p => ρ (xA p)).comp (MvPolynomial.map (Int.castRingHom ℂ))) =
        ρ.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro p
        simp
    have := congrArg (fun g => g f) e
    simp only [RingHom.comp_apply] at this
    refine this.trans ?_
    show ρ ((aeval xA : MRing ι →ₐ[ℤ] A) f) = 0
    rw [h1, map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonemptyStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiprojective_points_nonempty : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, ι k) → Ω), (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → (mcPts (mCoordIdeal x)).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mcPts_mCoordIdeal_nonempty <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTransferIdealEq
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def coneOver {A : Type} [CommRing A] (Y : (Σ k, ι k) → A) : MRing ι →ₐ[ℤ] MvPolynomial K A :=
  aeval fun p => C (Y p) * X p.1

def scaleBy {F : Type} [Field F] (c : K → F) : MvPolynomial K F →ₐ[F] MvPolynomial K F :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleBy_injective {F : Type} [Field F] (c : K → F) (hc : ∀ k, c k ≠ 0) :
    Function.Injective (scaleBy c) := by
  have h : (scaleBy fun k => (c k)⁻¹).comp (scaleBy c) = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleBy, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleBy fun k => (c k)⁻¹) fun f => DFunLike.congr_fun h f

theorem mConeMap_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F)
    (c : K → F) (hz : ∀ q, z q = c q.1 * f (Y q)) (p : MRing ι) :
    mConeMap z p = scaleBy c (MvPolynomial.map f (coneOver Y p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [mConeMap, coneOver]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, coneOver, aeval_X, scaleBy, map_mul, map_C, map_X, algHom_C, algebraMap_eq, hz q]
    ring

theorem mCoordIdeal_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (hf : Function.Injective f)
    (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F) (c : K → F) (hc : ∀ k, c k ≠ 0)
    (hz : ∀ q, z q = c q.1 * f (Y q)) : mCoordIdeal z = RingHom.ker (coneOver Y) := by
  ext p
  rw [mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_eq f Y z c hz]
  constructor
  · intro h
    have h1 : MvPolynomial.map f (coneOver Y p) = 0 := scaleBy_injective c hc (by rw [h, map_zero])
    exact MvPolynomial.map_injective f hf (by rw [h1, map_zero])
  · intro h
    rw [h, map_zero, map_zero]

theorem map_minorIJ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (h : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : f (minorIJ h I J) = minorIJ (h.map f) I J := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact map_zero f

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

def polyPt (M : FlagModel y Ψ N j) : (Σ k, ι k) → MvPolynomial (LowIdx Ψ N j) M.Ω := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then C (M.x ⟨⟨q.1, h⟩, q.2⟩)
  else ∑ I, C (M.coef q I) * minorIJ (genLow M.Ω N j (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem exists_scale (M : FlagModel y Ψ N j) {F : Type} [Field F] (f : MvPolynomial (LowIdx Ψ N j) M.Ω →+* F)
    (ψ : M.Ω →+* F) (hfC : ∀ a, f (C a) = ψ a) (G B : Ψ → Matrix (Fin N) (Fin N) F)
    (hG : ∀ τ, IsBlockDiag j (G τ))
    (hB : ∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni (G τ * B τ))
    (hf : ∀ q : LowIdx Ψ N j, f (X q) = (G q.1.1 * B q.1.1) q.1.2.1 q.1.2.2)
    (z : (Σ k, ι k) → F)
    (hbase : ∀ q : Σ k, baseIdx ι M.blk k, z ⟨q.1.1, q.2⟩ = ψ (M.x q))
    (hstep : ∀ p k, M.blk p = some k → ∀ m : ι k,
      z ⟨k, m⟩ = ∑ I, ψ (M.coef ⟨k, m⟩ I) * minorIJ (G p.1) I (stepCols N j p.2)) :
    ∃ c : K → F, (∀ k, c k ≠ 0) ∧ ∀ q, z q = c q.1 * f (polyPt M q) := by
  have hmap : ∀ τ, (genLow M.Ω N j τ).map f = G τ * B τ :=
    genLow_map f (H := fun τ => G τ * B τ) (fun τ => ⟨(hG τ).mul (hB τ).1, (hB τ).2.2⟩) hf
  have hdiag : ∀ τ c, B τ c c ≠ 0 := fun τ c h0 => by
    have h1 : (G τ).det * (B τ).det = 1 := by rw [← det_mul, (hB τ).2.2.det]
    have h2 : ∏ i, B τ i i = 0 := Finset.prod_eq_zero (Finset.mem_univ c) h0
    rw [det_of_upperTriangular (hB τ).2.1, h2, mul_zero] at h1
    exact zero_ne_one h1
  let s : Ψ × Fin N → F := fun p => ∏ c ∈ stepCols N j p.2, B p.1 c c
  have hs : ∀ p, s p ≠ 0 := fun p => Finset.prod_ne_zero_iff.2 fun c _ => hdiag p.1 c
  have gen : ∀ a b t : F, t ≠ 0 → a * b = t⁻¹ * (a * (b * t)) := fun a b t ht => by field_simp
  refine ⟨fun k => if h : ∀ p, M.blk p ≠ some k then 1 else (s (stepOf M k h))⁻¹, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact one_ne_zero
    · exact inv_ne_zero (hs _)
  · rintro ⟨k, m⟩
    by_cases h : ∀ p, M.blk p ≠ some k
    · have e := hbase ⟨⟨k, h⟩, m⟩
      simp only [polyPt, dif_pos h, one_mul, hfC]
      exact e
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [polyPt, dif_neg h, map_sum, map_mul, hfC, map_minorIJ, hmap]
      rw [hstep _ k (blk_stepOf M k h) m, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [(GlobalTheory.T.block_diagonal_minor_vanishing F N j (stepOf M k h).2 M.j_le).2.2.1 _ _ I (hB _).1 (hB _).2.1]
      exact gen _ _ _ (hs _)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift

section General

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] {n : ℕ}

theorem analytic_eval {G : (Fin n → ℂ) → (Σ k, J k) → ℂ} {T : Set (Fin n → ℂ)}
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (f : MRing J) :
    AnalyticOnNhd ℂ (fun w => eval (G w) (map (Int.castRingHom ℂ) f)) T := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticOnNhd_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, map_X, eval_X]
    exact hp.mul (hG i)

theorem isOpen_forall_ne {A : Type} [Finite A] {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    {f : A → (Fin n → ℂ) → ℂ} (hf : ∀ a, AnalyticOnNhd ℂ (f a) T) :
    IsOpen {w | w ∈ T ∧ ∀ a, f a w ≠ 0} := by
  have e : {w | w ∈ T ∧ ∀ a, f a w ≠ 0} = T ∩ ⋂ a, (T ∩ f a ⁻¹' {0}ᶜ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨h.1, fun a => ⟨h.1, h.2 a⟩⟩, fun h => ⟨h.1, fun a => (h.2 a).2⟩⟩
  rw [e]
  exact hT.inter (isOpen_iInter_of_finite fun a =>
    (hf a).continuousOn.isOpen_inter_preimage hT isOpen_compl_singleton)

theorem form_notMem_iff (z : (Σ k, J k) → ℂ) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∉ mCoordIdeal z ↔ eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
  rw [Ne, form_mem_mCoordIdeal_iff z hg, aeval_def, algebraMap_int_eq, eval₂_eq_eval_map]

theorem exists_normalised {A : Type} [Finite A] (x : (Σ k, J k) → Ω) (c : ∀ k, J k) (s : A → Ω)
    (G : (Fin n → ℂ) → (Σ k, J k) → ℂ) {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (hmem : ∀ w ∈ T, G w ∈ mcPts (mCoordIdeal x))
    {w₀ : Fin n → ℂ} (hw₀ : w₀ ∈ T) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ mCoordIdeal (G w₀))
    (hreg : ∀ a, RegAt x (mCoordIdeal (G w₀)) (s a)) :
    ∃ (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, J k) → ℂ), V ⊆ T ∧ IsOpen V ∧ w₀ ∈ V ∧
      (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
      (∀ a, AnalyticOnNhd ℂ (fun w => valAt x (s a) (bl w)) V) ∧
      ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal x) ∧ (∀ k, bl w ⟨k, c k⟩ = 1) ∧ SameOrbit (G w) (bl w) ∧
        ∀ a, RegAt x (mCoordIdeal (bl w)) (s a) := by
  choose d g h hg hh hnot heq using hreg
  have hX : ∀ (k : K) (i : J k), IsMultiHomog (X ⟨k, i⟩ : MRing J) (fun k' => if k' = k then 1 else 0) := fun k i =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩
  have hx : ∀ a, aeval x (h a) ≠ 0 := fun a e0 => by
    have h1 := (hmem w₀ hw₀).2 _ (mem_mCoordIdeal_of_aeval_eq_zero x (hh a) e0)
    exact (form_notMem_iff _ (hh a)).1 (hnot a) h1
  set bl : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun w p => G w p / G w ⟨p.1, c p.1⟩ with hbl
  set T₁ : Set (Fin n → ℂ) := {w | w ∈ T ∧ ∀ k, G w ⟨k, c k⟩ ≠ 0} with hT₁
  have hT₁o : IsOpen T₁ := isOpen_forall_ne hT fun k => hG ⟨k, c k⟩
  have hT₁T : T₁ ⊆ T := fun w hw => hw.1
  have hblq : ∀ q, AnalyticOnNhd ℂ (fun w => bl w q) T₁ := fun q =>
    ((hG q).mono hT₁T).div ((hG ⟨q.1, c q.1⟩).mono hT₁T) fun w hw => hw.2 q.1
  have hevh : ∀ a, AnalyticOnNhd ℂ (fun w => eval (bl w) (map (Int.castRingHom ℂ) (h a))) T₁ := fun a =>
    analytic_eval hblq (h a)
  have horb : ∀ w ∈ T₁, SameOrbit (G w) (bl w) := fun w hw =>
    ⟨fun k => G w ⟨k, c k⟩, hw.2, funext fun p => by
      have := hw.2 p.1
      simp only [hbl]
      field_simp⟩
  have hw₁ : w₀ ∈ T₁ := ⟨hw₀, fun k e0 => (form_notMem_iff _ (hX k (c k))).1 (hc k) (by simpa using e0)⟩
  refine ⟨{w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0}, bl,
    fun w hw => hw.1.1, isOpen_forall_ne hT₁o hevh, ⟨hw₁, fun a => ?_⟩, fun q => (hblq q).mono fun w hw => hw.1,
    fun a => ?_, fun w hw => ?_⟩
  · rw [← form_notMem_iff _ (hh a), ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit (horb w₀ hw₁)]
    exact hnot a
  · have hV : IsOpen {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} :=
      isOpen_forall_ne hT₁o hevh
    have hsub : {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} ⊆ T₁ :=
      fun w hw => hw.1
    refine AnalyticOnNhd.congr hV (((analytic_eval hblq (g a)).mono hsub).div
      ((hevh a).mono hsub) fun w hw => hw.2 a) fun w hw => ?_
    have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact (valAt_eq hz ⟨d a, g a, h a, hg a, hh a, hx a, heq a, hw.2 a, rfl⟩).symm
  · have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact ⟨hz, fun k => div_self (hw.1.2 k), horb w hw.1,
      fun a => ⟨d a, g a, h a, hg a, hh a, (form_notMem_iff _ (hh a)).2 (hw.2 a), heq a⟩⟩

end General

theorem exists_baseChart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X)
    (hgood : M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀))) :
    ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ),
      x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  obtain ⟨kb, hkb⟩ := Rb.A.cover x₀
  have hT : IsOpen ((Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀) :=
    (Rb.A.chart kb).isOpen_inter_preimage_symm (Rb.isOpen_U x₀)
  have hlw : Rb.lift x₀ ((Rb.A.chart kb).symm (Rb.A.chart kb x₀)) = Rb.lift x₀ x₀ := by
    rw [(Rb.A.chart kb).left_inv hkb]
  have hw₀ : Rb.A.chart kb x₀ ∈ (Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀ :=
    ⟨(Rb.A.chart kb).map_source hkb, by
      show (Rb.A.chart kb).symm (Rb.A.chart kb x₀) ∈ Rb.U x₀
      rw [(Rb.A.chart kb).left_inv hkb]
      exact Rb.mem_U x₀⟩
  let s : (((Σ k, ι k) × Finset (Fin N)) ⊕ ((Σ k, ι k) × Finset (Fin N))) ⊕
      ({p : Ψ × Fin N // M.blk p = none} ⊕ {p : Ψ × Fin N // M.blk p = none}) → M.Ω :=
    Sum.elim (Sum.elim (fun a => F.u a.1 a.2) (fun a => F.u' a.2 a.1))
      (Sum.elim (fun p => F.υ p.1) (fun p => (F.υ p.1)⁻¹))
  obtain ⟨V, bl, hVT, hVo, hV₀, hq, hval, hpt⟩ := exists_normalised M.x F.c s
    (fun w => Rb.lift x₀ ((Rb.A.chart kb).symm w)) hT (fun q => Rb.holo x₀ q kb)
    (fun w hw => Rb.mem x₀ _ hw.2) hw₀
    (by simpa only [hlw] using hgood.1)
    (by
      simp only [hlw]
      rintro ((⟨q, I⟩ | ⟨q, I⟩) | (⟨p, hp⟩ | ⟨p, hp⟩))
      · exact (hgood.2.1 q I).1
      · exact (hgood.2.1 q I).2
      · exact (hgood.2.2 p hp).2.1
      · exact (hgood.2.2 p hp).2.2)
  refine ⟨kb, V, bl, hkb, hV₀, hVo, fun w hw => (hVT hw).1, hq,
    fun q I => hval (Sum.inl (Sum.inl (q, I))), fun w hw => ?_⟩
  obtain ⟨hz, h1, hor, hr⟩ := hpt w hw
  refine ⟨hz, h1, ⟨fun k e0 => ?_, fun q I => ⟨hr (Sum.inl (Sum.inl (q, I))), hr (Sum.inl (Sum.inr (q, I)))⟩,
    fun p hp => ⟨(hgood.2.2 p hp).1, hr (Sum.inr (Sum.inl ⟨p, hp⟩)), hr (Sum.inr (Sum.inr ⟨p, hp⟩))⟩⟩,
    orbit_trans (Rb.compat _ x₀ _ ⟨Rb.mem_U _, (hVT hw).2⟩) hor⟩
  have := (form_mem_mCoordIdeal_iff (bl w) (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single
    (⟨k, F.c k⟩ : Σ k, baseIdx ι M.blk k))).1 e0
  rw [aeval_X, h1 k] at this
  exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_chart_at_good_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X), M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀)) → ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ), x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem isValueAt_coord_ratio :
    ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω]
      (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (k : K') (c : ι' k),
      z ∈ mcPts (mCoordIdeal y') → z ⟨k, c⟩ ≠ 0 →
        y' ⟨k, c⟩ ≠ 0 ∧ ∀ i : ι' k, IsValueAt y' (y' ⟨k, i⟩ / y' ⟨k, c⟩) z ((z ⟨k, c⟩)⁻¹ * z ⟨k, i⟩) := by
  intro K' _ ι' _ Ω _ y' z k c hz hzc
  have hy : y' ⟨k, c⟩ ≠ 0 := by
    intro h0
    have hm : (X ⟨k, c⟩ : MRing ι') ∈ mCoordIdeal y' := by
      refine RingHom.mem_ker.2 ?_
      simp [mConeMap, h0]
    have h1 := hz.2 _ hm
    simp only [map_X, eval_X] at h1
    exact hzc h1
  refine ⟨hy, fun i => ⟨fun l => if l = k then 1 else 0, X ⟨k, i⟩, X ⟨k, c⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, c⟩, ?_, ?_, ?_, ?_⟩⟩
  · simpa using hy
  · simp only [aeval_X]
    field_simp
  · simpa using hzc
  · simp only [map_X, eval_X]
    rw [div_eq_inv_mul]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_ratio_value_at_point : ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (k : K') (c : ι' k), z ∈ mcPts (mCoordIdeal y') → z ⟨k, c⟩ ≠ 0 → y' ⟨k, c⟩ ≠ 0 ∧ ∀ i : ι' k, IsValueAt y' (y' ⟨k, i⟩ / y' ⟨k, c⟩) z ((z ⟨k, c⟩)⁻¹ * z ⟨k, i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio <;> assumption)
end
end
