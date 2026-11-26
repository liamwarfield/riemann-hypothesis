module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace OrbMark

section Twist

variable {O : Type} [CommRing O]

def twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : Fin n → O := fun i => σ (a i)

@[simp] theorem twv_apply (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) (i : Fin n) : twv σ a i = σ (a i) := rfl

theorem twv_zero (σ : O ≃+* O) (n : ℕ) : twv σ (0 : Fin n → O) = 0 := funext fun _ => map_zero σ

theorem twv_smul (σ : O ≃+* O) {n : ℕ} (c : O) (a : Fin n → O) : twv σ (c • a) = σ c • twv σ a :=
  funext fun _ => by simp [twv]

theorem twv_twv (σ τ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv τ (twv σ a) = twv (σ.trans τ) a := rfl

theorem twv_symm_twv (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ.symm (twv σ a) = a :=
  funext fun _ => σ.symm_apply_apply _

theorem twv_twv_symm (σ : O ≃+* O) {n : ℕ} (a : Fin n → O) : twv σ (twv σ.symm a) = a :=
  funext fun _ => σ.apply_symm_apply _

def conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) : (Fin n → O) →ₗ[O] (Fin m → O) where
  toFun a := twv σ.symm (r (twv σ a))
  map_add' a b := by
    have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
    rw [e, map_add (f := _)]
    exact funext fun _ => map_add σ.symm _ _
  map_smul' c a := by
    rw [twv_smul, map_smul, twv_smul, RingHom.id_apply, σ.symm_apply_apply]

theorem twv_conjLin (σ : O ≃+* O) {n m : ℕ} (r : (Fin n → O) →ₗ[O] (Fin m → O)) (a : Fin n → O) :
    twv σ (conjLin σ r a) = r (twv σ a) := twv_twv_symm σ _

theorem conjLin_surjective (σ : O ≃+* O) {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) :
    Function.Surjective (conjLin σ r) := fun b => by
  obtain ⟨a, ha⟩ := hr (twv σ b)
  refine ⟨twv σ.symm a, ?_⟩
  show twv σ.symm (r (twv σ (twv σ.symm a))) = b
  rw [twv_twv_symm, ha, twv_symm_twv]

end Twist

section Mark

variable {O : Type} [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]

def IsOrbForm (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Prop :=
  ∃ s : (Fin n → O) →ₗ[O] (X₀ ⧸ (CarDim.orad v : Submodule O X₀)), Function.Surjective s ∧
    ∀ (a b : Fin n → O) (x y : X₀), Submodule.Quotient.mk x = s a → Submodule.Quotient.mk y = s b →
      B (twv σ a) (twv σ b) = v x y

theorem isOrbForm_comp_iff (v : LinearMap.BilinForm ℤ X₀) (σ : O ≃+* O) {n m : ℕ}
    {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r) (B : (Fin m → O) → (Fin m → O) → ℝ) :
    IsOrbForm v σ n (fun a b => B (r a) (r b)) ↔ IsOrbForm v σ m B := by
  set r' := conjLin σ r
  have hr' : Function.Surjective r' := conjLin_surjective σ hr
  constructor
  · rintro ⟨s, hs, H⟩
    obtain ⟨t, ht⟩ := Module.projective_lifting_property r' LinearMap.id hr'
    have hrt : ∀ a, r' (t a) = a := fun a => LinearMap.congr_fun ht a
    have hker : ∀ z, r' z = 0 → s z = 0 := by
      intro z hz
      obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
      rw [← hx]
      refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
      obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
      have h1 := H (c • z) b (c • x) y (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
      have h2 := H 0 b 0 y (by rw [map_zero]; rfl) hb.symm
      have e : r (twv σ (c • z)) = 0 := by
        rw [← twv_conjLin, map_smul, hz, smul_zero, twv_zero]
      have e0 : r (twv σ 0) = 0 := by rw [twv_zero, map_zero]
      dsimp only at h1 h2
      rw [e] at h1
      rw [e0, map_zero, LinearMap.zero_apply] at h2
      exact_mod_cast h1.symm.trans h2
    refine ⟨s ∘ₗ t, fun y => ?_, fun a b x y hx hy => ?_⟩
    · obtain ⟨a, rfl⟩ := hs y
      refine ⟨r' a, ?_⟩
      have : s (a - t (r' a)) = 0 := hker _ (by rw [map_sub, hrt, sub_self])
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    · have h := H (t a) (t b) x y hx hy
      dsimp only at h
      rwa [← twv_conjLin, ← twv_conjLin, hrt, hrt] at h
  · rintro ⟨s, hs, H⟩
    refine ⟨s ∘ₗ r', hs.comp hr', fun a b x y hx hy => ?_⟩
    have h := H (r' a) (r' b) x y hx hy
    show B (r (twv σ a)) (r (twv σ b)) = _
    rwa [twv_conjLin, twv_conjLin] at h

theorem eq_zero_of_isOrbForm_zero {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {B : (Fin 0 → O) → (Fin 0 → O) → ℝ}
    (h : IsOrbForm v σ 0 B) : v = 0 := by
  obtain ⟨s, hs, -⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  have hx : x ∈ (CarDim.orad v : Submodule O X₀) := by
    obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact (Submodule.Quotient.mk_eq_zero _).1 ha.symm
  simpa using hx 1 y

end Mark

section Fun

variable (O : Type) [CommRing O] {X₀ : Type} [AddCommGroup X₀] [Module O X₀]


open Classical in
def orbFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) : InvFun O where
  toFun n B := if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0
  inv n m r hr B := by
    simp only [isOrbForm_comp_iff v _ hr]
  zero B := by
    rw [if_neg]
    rintro ⟨hv, σ, -, h⟩
    exact hv (eq_zero_of_isOrbForm_zero h)

variable {O}

open Classical in
theorem orbFun_toFun (w0 : O) (v : LinearMap.BilinForm ℤ X₀) (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) :
    (orbFun O w0 v).toFun n B = if v ≠ 0 ∧ ∃ σ : O ≃+* O, σ w0 = w0 ∧ IsOrbForm v σ n B then 1 else 0 := rfl

theorem orbFun_eval_eq_zero_or_one (w0 : O) (v : LinearMap.BilinForm ℤ X₀) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] (B : X → X → ℝ) : (orbFun O w0 v).eval X B = 0 ∨ (orbFun O w0 v).eval X B = 1 := by
  unfold InvFun.eval
  rw [orbFun_toFun]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem eq_zero_of_isOrbForm_const {v : LinearMap.BilinForm ℤ X₀} {σ : O ≃+* O} {n : ℕ}
    (h : IsOrbForm v σ n fun _ _ => 0) : v = 0 := by
  obtain ⟨s, hs, H⟩ := h
  refine LinearMap.ext₂ fun x y => ?_
  obtain ⟨a, ha⟩ := hs (Submodule.Quotient.mk x)
  obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
  have := H a b x y ha.symm hb.symm
  simp only [LinearMap.zero_apply]
  have h0 : ((v x y : ℤ) : ℝ) = 0 := this.symm
  exact_mod_cast h0

theorem orbFun_evalZ_zero (w0 : O) {v : LinearMap.BilinForm ℤ X₀} (hv : v ≠ 0) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : (orbFun O w0 v).evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_neg]
  rintro ⟨-, σ, -, h⟩
  refine hv (eq_zero_of_isOrbForm_const (σ := σ) (n := n) ?_)
  simpa using h

theorem orbFun_evalZ_self (w0 : O) {v : LinearMap.BilinForm ℤ X₀} [Module.Finite O X₀] (hv : v ≠ 0)
    (hsym : ∀ y z, v y z = v z y) : (orbFun O w0 v).evalZ v = 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X₀
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun, if_pos]
  refine ⟨hv, RingEquiv.refl O, rfl, (CarDim.orad v).mkQ ∘ₗ r, (Submodule.mkQ_surjective _).comp hr,
    fun a b x y hx hy => ?_⟩
  have hx' : x - r a ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hx
  have hy' : y - r b ∈ (CarDim.orad v : Submodule O X₀) := (Submodule.Quotient.eq _).1 hy
  have e1 : v x y = v (r a) y := by
    have := hx' 1 y
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have e2 : v (r a) y = v (r a) (r b) := by
    have := hy' 1 (r a)
    rw [one_smul, map_sub, LinearMap.sub_apply, sub_eq_zero, hsym, hsym (r b)] at this
    exact this
  show ((v (r a) (r b) : ℤ) : ℝ) = (v x y : ℝ)
  rw [e1, e2]

end Fun

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]

theorem isTwInv_orbFun (H : Host E) (v : LinearMap.BilinForm ℤ X₀) : IsTwInv H (orbFun (𝓞 E) H.w0 v) := by
  intro τ hτ n B
  rw [orbFun_toFun, orbFun_toFun]
  congr 2
  apply propext
  constructor
  · rintro ⟨σ, hσ, s, hs, h⟩
    exact ⟨σ.trans τ, by simp [hσ, hτ], s, hs, fun a b x y hx hy => h a b x y hx hy⟩
  · rintro ⟨σ, hσ, s, hs, h⟩
    refine ⟨σ.trans τ.symm, by simp [hσ, RingEquiv.symm_apply_eq, hτ], s, hs, fun a b x y hx hy => ?_⟩
    have := h a b x y hx hy
    show B (twv τ (twv (σ.trans τ.symm) a)) (twv τ (twv (σ.trans τ.symm) b)) = _
    rw [twv_twv, twv_twv]
    convert this using 3 <;> ext i <;> simp

end Host

end OrbMark

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
noncomputable section

open MvPolynomial Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.PointChern

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coordOf {H : Host E} {Dw : Datum H} {n : ℕ} (e : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ :=
  fun τ i j => w (e.symm (τ, i, j))

def InDom {H : Host E} {Dw : Datum H} (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) : Prop :=
  ∀ τ, (1 - (z τ)ᴴ * z τ).PosDef

theorem mult_of_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult τ = Dw.p := by
  simp [Datum.mult, h]

theorem mult_of_not_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    Dw.mult τ = Dw.q := by
  simp [Datum.mult, h]


open Classical in
def modelGram (H : Host E) (Dw : Datum H) (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) :
    GlobalTheory.FlagBundle.Mat Dw.mult ℂ := fun τ =>
  if h : τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
      (1 - (z ⟨τ, h⟩).map (starRingEnd ℂ) * (z ⟨τ, h⟩)ᵀ)⁻¹
  else if h' : conjEmb τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
      (1 - (z ⟨conjEmb τ, h'⟩)ᴴ * z ⟨conjEmb τ, h'⟩)⁻¹
  else 1

def relPoly {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)

end GlobalTheory.PointChern
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorNotOverLevelPrimes
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

theorem exists_hilbert_le_O (hR : RayField) (B : Base) (δ : FieldDat B.toPre) (hδ : δ.ray ≤ B.KsC) :
    ∃ M : IntermediateField ℚ ℂ, IsRayFieldIn B.host.φ₀ ⊤ M ∧
      ∀ z ∈ M, IsIntegral ℤ z → ∃ y : B.O, B.embLL (B.OtoLL y) = z := by
  obtain ⟨M, hM⟩ := exists_isRayFieldIn B.host.φ₀ hR (𝔮 := ⊤) top_ne_bot
  refine ⟨M, hM, fun z hz hI => ?_⟩
  have hle : M ≤ δ.ray := RayMono.le_of_isRayFieldIn_of_dvd _ _ _ _ _ _ (natIdeal_ne_bot (modulus_ne_zero B.toPre))
    (Ideal.dvd_iff_le.2 le_top) hM δ.isRay
  obtain ⟨x, hx, rfl⟩ := B.mem_KsC.1 (hδ (hle hz))
  have hx' : IsIntegral ℤ x :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hI
  obtain ⟨y, hy⟩ := B.O_full x hx hx'
  exact ⟨y, by rw [hy]⟩

theorem twistConductor_not_over_levelPrimes (B : Base) (T : TwDat B) (w : B.places.Pl) {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : v ∈ T.Q w)
    (u : B.Word) (hp : (B.T u).Prime) : ¬ OverP B.host (B.T u) v := by
  intro ho
  obtain ⟨-, h1, -, h2⟩ := (T.psi_tw w).2.2.2 v fun h => ((T.psi_is w).ram v).1 h hv
  have := Examples₂.PlacesToy.prime_mem_unique v h1 hp (Ideal.absNorm_mem _) ho
  exact h2 (this ▸ .inr (.inr (.inr (.inr (.inl ⟨u, rfl⟩)))))

end GlobalTheory.Mem.HD
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem hostPins_wpt : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), GlobalTheory.Mem.HD.HostPins (q.w.D q.Z) q.O.ex.nch := by
  intro hR 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  have hmu := x.what₂.mu
  have key := GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st Z) f T x.Wt w.I.xi hmu
  have hδ : w.δ.ray ≤ B.KsC := w.exact.lower.1
  have hQ : ∀ v ∈ x.Wt, O.ex.nch.Q v = T.Q v := fun v hv => (x.n.Q v hv).1
  refine ⟨fun u i => (w.D Z).T_ne_g u i, ?_, fun v hv v' hv' u => ?_, B.galLL, GlobalTheory.Mem.HD.exists_hilbert_le_O hR B w.δ hδ⟩
  · exact key.2.1.subset fun v hv => (key.1 v).1 hv
  · have hvW := (key.1 v).1 hv
    rw [hQ v hvW] at hv'
    have e : ((w.D Z).mem u).A.T = B.T u := (w.st Z).C.A_T u
    have hp : (B.T u).Prime := e ▸ ((w.D Z).mem u).A.T_prime
    rw [e]
    exact GlobalTheory.Mem.HD.twistConductor_not_over_levelPrimes B T v hv' u hp

end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

namespace Mark

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (ψ lab : InvFun O) (i : ℕ)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

def InFace (β x : LinearMap.BilinForm ℤ X) : Prop :=
  x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ (∀ y, β y y = 0 → x y y = 0) ∧
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x ∧ lab.evalZ (β + x) = lab.evalZ β

def IsIndec (β x : LinearMap.BilinForm ℤ X) : Prop :=
  InFace bar ψ lab β x ∧ x ≠ 0 ∧ ∀ y z, InFace bar ψ lab β y → InFace bar ψ lab β z → y ≠ 0 → z ≠ 0 → y + z ≠ x

variable (X) in
def IsMarked (β : LinearMap.BilinForm ℤ X) : Prop :=
  β ∈ balForms bar X ∧ (∀ y, 0 ≤ β y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    lab.evalZ β = ((i + 1 : ℕ) : ℝ) ∧
    ∃ S : Finset (LinearMap.BilinForm ℤ X), (∀ x, x ∈ S ↔ IsIndec bar ψ lab β x) ∧
      ∃ k : ℕ, 0 < k ∧ (k : ℤ) • β = ∑ x ∈ S, x

open Classical in
def markVal (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : ℝ :=
  if h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b then
    (if IsMarked bar ψ lab i (Fin n → O) h.choose then 1 else 0) else 0

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]

open Classical in
theorem markVal_int (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    markVal bar ψ lab i n (fun a b => (β a b : ℝ)) = if IsMarked bar ψ lab i (Fin n → O) β then 1 else 0 := by
  classical
  unfold markVal
  have h : ∃ β' : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, ((β a b : ℤ) : ℝ) = β' a b := ⟨β, fun _ _ => rfl⟩
  rw [dite_eq_left h]
  have e : h.choose = β := LinearMap.ext₂ fun a b => by
    have := h.choose_spec a b
    exact_mod_cast this.symm
  rw [e]

end Basic

end Mark

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EllEqOfInRCone
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

theorem ell_eq_of_inRCone {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hlin : φ.LinearOn γ) (hsw : StrictWith bar φ N ℓ γ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hsw.1 i]; ring

end GlobalTheory.PolFan.StarKey
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCell
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isCell_face_of_isFaceCut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ)
    (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell H.bar ψ (fun j => v (s j)) := by
  intro E _ _ _ H q ψ hψ X _ _ _ _ hX hD m v hv m' s h hcut
  have hP := hψ X hX
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓpos : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNr e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hℓpos
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨b, hb⟩ : ∃ b : ℕ, ∀ γ ∈ S, ψ.evalZ γ ≤ b := by
    refine ⟨⌈∑ γ ∈ hS.toFinset, |ψ.evalZ γ|⌉₊, fun γ hγ => ?_⟩
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun γ => |ψ.evalZ γ|) (fun _ _ => abs_nonneg _) (hS.mem_toFinset.2 hγ))
  set K : ℕ := C * (1 + N * b) + 1 with hK
  have hKpos : 0 < K := Nat.succ_pos _

  have gen : ∀ u ∈ balForms H.bar X, (∀ y, 0 ≤ u y y) → ψ.evalZ u ≤ b →
      (0 ≤ h u ∧ (ℓ u : ℝ) = N * ψ.evalZ u) ∨
        (0 : ℝ) < K * (ℓ u : ℝ) + h u - K * N * ψ.evalZ u := by
    intro u hu hp hub
    by_cases heq : (ℓ u : ℝ) = N * ψ.evalZ u
    · left
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp heq.symm
      have e1 : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (v i) := by
        have := congrArg h hc
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
      have hnn : 0 ≤ (k : ℤ) * h u := e1 ▸ Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hcut.1 i)
      exact ⟨(mul_nonneg_iff_of_pos_left (by exact_mod_cast hk)).1 hnn, heq⟩
    · right
      obtain ⟨n, hn⟩ := hP.integral u hu hp
      have hle : (N : ℝ) * ψ.evalZ u ≤ ℓ u := h2 u hu hp
      have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne hle (Ne.symm heq)
      rw [hn] at hlt hub ⊢
      have hint : (N : ℤ) * n + 1 ≤ ℓ u := by
        have : (((N : ℤ) * n : ℤ) : ℝ) < ℓ u := by push_cast; exact hlt
        exact_mod_cast this
      have hint' : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast hint
      have hCu : -h u ≤ C * ℓ u := by simpa using hC u hu hp
      have hCu' : -(h u : ℝ) ≤ C * ℓ u := by exact_mod_cast hCu
      have hKr : (K : ℝ) = C * (1 + N * b) + 1 := by rw [hK]; push_cast; ring
      have hCN : (0 : ℝ) ≤ C * N := by positivity
      have a1 : (K - C : ℝ) * 1 ≤ (K - C) * (ℓ u - N * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [hKr]; have : (0 : ℝ) ≤ C * N * b := by positivity
                                                    nlinarith)
      have a2 : (C * N : ℝ) * n ≤ C * N * b := mul_le_mul_of_nonneg_left hub hCN
      rw [hKr] at a1 ⊢
      nlinarith

  have core : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      ((K * N : ℕ) : ℝ) * ψ.evalZ β ≤ ((K • ℓ + h) β : ℤ) ∧
        (((K * N : ℕ) : ℝ) * ψ.evalZ β = ((K • ℓ + h) β : ℤ) → h β = 0) := by
    intro β hβ hp
    have hR : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (by simp [hβ])
        (by simp [hp]) (by simp)
    obtain ⟨e, mm, γ, c, hγ, hγS, hc, hsum⟩ := hcov (toReal β) hR
    set u : Fin mm → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hu
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply, u] using this
    have hlin : ψ.LinearOn u := (linearOn_pull_iff e.symm.surjective).2 hγ.linear
    have hψβ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu, (linearOn_iff ψ u).1 hlin c hc]
    have hℓβ := apply_eq_of_toReal_eq hβu ℓ
    have hhβ := apply_eq_of_toReal_eq hβu h
    have hT : (((K • ℓ + h) β : ℤ) : ℝ) - ((K * N : ℕ) : ℝ) * ψ.evalZ β =
        ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul]
      rw [hℓβ, hhβ, hψβ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hg : ∀ i, (0 ≤ h (u i) ∧ (ℓ (u i) : ℝ) = N * ψ.evalZ (u i)) ∨
        (0 : ℝ) < K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i) := fun i =>
      gen (u i) (pull_mem _ (hγ.mem i)) (fun y => hγ.nonneg i _)
        (by rw [hu, evalZ_pull ψ e.symm.surjective]; exact hb _ (hγS i))
    have hterm : ∀ i, 0 ≤ c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := fun i => by
      refine mul_nonneg (hc i) ?_
      rcases hg i with ⟨h0, he⟩ | hpos
      · rw [he]
        have : (0 : ℝ) ≤ h (u i) := by exact_mod_cast h0
        nlinarith
      · exact hpos.le
    refine ⟨?_, fun heq => ?_⟩
    · have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
      linarith
    · have h0 : ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) = 0 := by
        rw [← hT, heq, sub_self]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 h0
      have : (h β : ℝ) = 0 := by
        rw [hhβ]
        refine Finset.sum_eq_zero fun i hi => ?_
        rcases eq_or_ne (c i) 0 with hci | hci
        · rw [hci, zero_mul]
        · have hTi := (mul_eq_zero.1 (hz i hi)).resolve_left hci
          rcases hg i with ⟨-, he⟩ | hpos
          · rw [he] at hTi
            have : (h (u i) : ℝ) = 0 := by linarith
            rw [this, mul_zero]
          · exact absurd hTi hpos.ne'
      exact_mod_cast this
  refine ⟨fun j => hv.mem _, fun j => hv.nonneg _, linearOn_comp hv.linear s, K * N, K • ℓ + h,
    Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => (core β hβ hp).1, fun β hβ hp heq => ?_⟩
  · have hz : h (v (s i)) = 0 := (hcut.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hz, add_zero, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul]
    rw [h1]; ring
  · have hh := (core β hβ hp).2 heq
    have hℓ : (N : ℝ) * ψ.evalZ β = ℓ β := by
      have e1 := heq
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hh, add_zero, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul] at e1
      have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
      have : (K : ℝ) * (N * ψ.evalZ β - ℓ β) = 0 := by linarith
      linarith [(mul_eq_zero.1 this).resolve_left hKr.ne']
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp hℓ
    have e1 : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (v j) := by
      have := congrArg h hc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    rw [hh, mul_zero] at e1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (Int.natCast_nonneg (c j)) (hcut.1 j)).1 e1.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
      have hne : h (v j) ≠ 0 := fun h0 => hj ((hcut.2 j).1 h0)
      have := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
      exact_mod_cast this
    refine ⟨k, fun i => c (s i), hk, ?_⟩
    rw [hc]
    classical
    rw [← Finset.sum_map Finset.univ s (fun j => c j • v j)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell H.bar ψ (fun j => v (s j)) := by
  first | exact @GlobalTheory.PolFan.isCell_face_of_isFaceCut | exact GlobalTheory.PolFan.isCell_face_of_isFaceCut | (intros; apply GlobalTheory.PolFan.isCell_face_of_isFaceCut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKOfStd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.KerSK

theorem rowSG_heq {ι : Type} {X X' : Fields} (hX : X = X') {Pr : Primes X} {Pr' : Primes X'} (hPr : HEq Pr Pr')
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)}
    (hsel : HEq sel sel') {S S' : Set ℕ} (hS : S = S') {tup : ι → Tup X.F X.E X.K S} {tup' : ι → Tup X'.F X'.E X'.K S'}
    (htup : HEq tup tup') :
    HEq (fun μ => rowSG Pr sel (tup μ)) (fun μ => rowSG Pr' sel' (tup' μ)) := by
  subst hX; subst hS; cases hPr; cases hsel; cases htup; rfl

theorem sharp_heq {ι : Type} {X X' : Fields} (hX : X = X') {P : ι → Finset (HeightOneSpectrum (𝓞 X.E))}
    {P' : ι → Finset (HeightOneSpectrum (𝓞 X'.E))} (hP : HEq P P') {c : ∀ μ, LocCst X (P μ)} {c' : ∀ μ, LocCst X' (P' μ)}
    (h : HEq c c') (μ : ι) : (c μ).sharp = (c' μ).sharp := by
  subst hX; cases hP; cases h; rfl

theorem ch_cast {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
    {Tw Tw' : TwForms D} (h : Tw = Tw') (x : SymmetricTwistedColumnsAtPrimes tp C Tw) : (h ▸ x).ch = x.ch := by
  subst h; rfl

end GlobalTheory.Mem.Col2.TC.KerSK
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Top.Bl.WitSK

def of_sigma_eq {α : Type*} {β : α → Type*} {a b : Σ x, β x} (h : a = b) (P : ∀ x, β x → Sort*) (hb : P b.1 b.2) :
    P a.1 a.2 := by
  subst h; exact hb

end GlobalTheory.Mem.Top.Bl.WitSK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsKerTie
section BaseLevels₂

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Core.DefKer.stdRd_keep {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts}
    {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hS : I.StdKer l Z t) :
    ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ t'.O = t.O ∧ t'.ent = t.ent := by
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, rfl, rfl⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a


end BaseLevels₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Core GlobalTheory.Core.Cls NumberField IsDedekindDomain GlobalTheory.Mem.Db Formalism.L2 Formalism.L2.Ker Formalism.L2.Forms
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), EntC q.x.ker → ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t ∧ GlobalTheory.Svd.StdAt q.w.I q.w.l q.w.l0 q.Z q.O t ∧ GlobalTheory.Pdv.StdRd q.w.I q.w.l q.Z t := by
  intro 𝒮 K q hE
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
  simp only [ofObj, extraObj] at ker_eq
  cases ker_eq
  obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
    ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
      nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
    kT.unf kT.ok kT.served
  obtain ⟨t, s, r, p, o, e⟩ := GlobalTheory.Core.DefKer.stdRd_keep w.I w.ok w.l Z t1 ((StdModel.stdKer_iff w.I w.l Z t1).2 s1)
  have ha : t.Adapted := by
    unfold Formalism.L2.Ker.KerEntTied.Adapted at a1 ⊢
    rw [o, e]
    exact a1
  have hc : GlobalTheory.Pdv.IsEntC t := by
    unfold GlobalTheory.Pdv.IsEntC
    rw [o, e, o1, e1]
    exact hE
  exact ⟨t, ⟨s, o.trans o1, heq_of_eq (e.trans e1), ha, p⟩, ⟨w.ok, w.pins, pin.isTw, pin.jets, rfl, s, hc, ha, p⟩, r⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBound
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

namespace StarUpper

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone_cell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he


omit [Module O X] [Module.Finite O X] in
theorem sum_mem_rcone {p : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (d : Fin m → ℕ), 0 < k ∧ k • δ i = ∑ j, d j • γ j) :
    ∑ i, x i • toReal (δ i) ∈ rcone γ := by
  classical
  have hi : ∀ i, ∃ g : Fin m → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (γ j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨k, d, hk, hkd⟩ := h i h0
    have hxi := hx i
    refine ⟨fun j => x i / k * d j, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
    have e := LinearMap.congr_fun₂ hkd a b
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at e
    have e' : (k : ℝ) * (δ i a b : ℝ) = ∑ j, (d j : ℝ) * (γ j a b : ℝ) := by exact_mod_cast e
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    calc x i * (δ i a b : ℝ) = x i / k * ((k : ℝ) * (δ i a b : ℝ)) := by field_simp
      _ = _ := by rw [e', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

end StarUpper


open StarUpper in
theorem evalR_starDepth_le : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s : ℝ),
    IsCell bar ψ γ → B ∈ rcone γ → 0 ≤ s → (∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v →
      ∀ t : ℝ, 0 < t → B - t • toReal v ∈ rcone γ → t ≤ s) → evalR (starDepth bar ψ w) B ≤ s := by
  intro O _ bar ψ w X _ _ _ m γ B s hγ hB hs H
  obtain ⟨c, hc, hBc⟩ := hB
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' O X
  show (starDepth bar ψ w).eval X (fun a b => B a b) ≤ s
  rw [InvFun.eval_eq _ hq]
  refine Real.sSup_le (fun t ht => ?_) hs
  obtain ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB₁, ht0, m₁, γ₁, v₁, hγ₁, hv₁, hv₁p, hwv₁, ⟨e, he, hev⟩, -,
    ⟨d, hd, hdv⟩⟩ := ht
  rcases ht0.eq_or_lt with rfl | htpos
  · exact hs

  have hker : LinearMap.ker q ≤ LinearMap.ker ρ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hrad _ fun y => ?_
    obtain ⟨y', rfl⟩ := hρ y
    have h1 := hB₁ x y'
    simp only [hx, map_zero, LinearMap.zero_apply] at h1
    exact h1.symm
  let ρ' : X →ₗ[O] X₁ := (LinearMap.ker q).liftQ ρ hker ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hρ' : ∀ a, ρ' (q a) = ρ a := fun a => by
    have : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hρs : Function.Surjective ρ' := fun x => by
    obtain ⟨a, rfl⟩ := hρ x
    exact ⟨q a, hρ' a⟩
  have hBB : ∀ x y, B x y = B₁ (ρ' x) (ρ' y) := fun x y => by
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [hρ', hρ']
    exact hB₁ a b

  set δ : Fin m₁ → LinearMap.BilinForm ℤ X := fun i => pull ρ' (γ₁ i) with hδ
  set v : LinearMap.BilinForm ℤ X := pull ρ' v₁ with hv
  have hv_eq : toReal v = ∑ i, e i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hev (ρ' a) (ρ' b)
    simpa [hδ, hv, LinearMap.sum_apply] using this
  have hd_eq : B - t • toReal v = ∑ i, d i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hdv (ρ' a) (ρ' b)
    simpa [hδ, hv, hBB, LinearMap.sum_apply] using this
  have hrel : ∑ i, (d i + t * e i) • toReal (δ i) = ∑ j, c j • toReal (γ j) := by
    rw [← hBc]
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := LinearMap.congr_fun₂ hd_eq a b
    have h2 := LinearMap.congr_fun₂ hv_eq a b
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at h1 h2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← h1, ← h2]
    ring
  have hnn : ∀ i, 0 ≤ d i + t * e i := fun i => add_nonneg (hd i) (mul_nonneg ht0 (he i))
  have hlin : evalR ψ (∑ i, (d i + t * e i) • toReal (δ i)) = ∑ i, (d i + t * e i) * ψ.evalZ (δ i) :=
    (linearOn_iff ψ δ).1 ((linearOn_pull_iff hρs).2 hγ₁.linear) _ hnn
  have hcone := inCone_cell hγ (fun i => pull_mem ρ' (hγ₁.mem i)) (fun i y => hγ₁.nonneg i _) hnn hc hlin hrel
  have hInR : InRCone γ v := by
    obtain ⟨c', hc', h'⟩ := sum_mem_rcone e he fun i hi => hcone i
      (add_pos_of_nonneg_of_pos (hd i) (mul_pos htpos (lt_of_le_of_ne (he i) (Ne.symm hi)))).ne'
    exact ⟨c', hc', hv_eq.trans h'⟩
  have hBt : B - t • toReal v ∈ rcone γ := by
    rw [hd_eq]
    exact sum_mem_rcone d hd fun i hi => hcone i
      (add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hd i) (Ne.symm hi)) (mul_nonneg ht0 (he i))).ne'
  exact H v (pull_mem ρ' hv₁) (fun y => hv₁p _) (by rw [hv, evalZ_pull w hρs]; exact hwv₁) hInR t htpos hBt

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBoundStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalR_starDepth_le_of_centre_bound : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s : ℝ), IsCell bar ψ γ → B ∈ rcone γ → 0 ≤ s → (∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → ∀ t : ℝ, 0 < t → B - t • toReal v ∈ rcone γ → t ≤ s) → evalR (starDepth bar ψ w) B ≤ s := by
  first | exact @GlobalTheory.PolFan.evalR_starDepth_le | exact GlobalTheory.PolFan.evalR_starDepth_le | (intros; apply GlobalTheory.PolFan.evalR_starDepth_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GJStage_GIs2_pinned : StepW Pinned fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := by
  first | exact @GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep | exact GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep | (intros; apply GlobalTheory.Mem.Top.Bl.TrueLocal.exists_trueVolumeStage_columnChoiceStep <;> assumption)
end
