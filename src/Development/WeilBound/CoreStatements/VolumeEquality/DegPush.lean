module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushAsm
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPullB
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushUnit
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushNumEq
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFib
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushTest
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushMass
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGeneric
public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushFibLink
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSum

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLink
section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushMuLinkA
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section Lin

variable {Ω₃ : Type} [Field Ω₃] (O : ValuationSubring Ω₃) {r : ℕ}

theorem mu_det_le (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : ∀ k, (fun m => T m k) ∈ Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det ≤ O.valuation T'.det := by
  choose N hN using fun k => (Submodule.mem_span_range_iff_exists_fun O).1 (h k)
  have e : T = T' * (Matrix.of fun a b => N b a).map O.subtype := by
    ext m k
    have := congrFun (hN k) m
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have e2 : ((Matrix.of fun a b => N b a).map O.subtype).det = ((Matrix.of fun a b => N b a).det : O) :=
    (RingHom.map_det O.subtype _).symm
  rw [e, Matrix.det_mul, map_mul, e2]
  exact mul_le_of_le_one_right' (O.valuation_le_one _)

theorem mu_det_eq (T T' : Matrix (Fin r) (Fin r) Ω₃)
    (h : Submodule.span O (Set.range fun k m => T m k) = Submodule.span O (Set.range fun k m => T' m k)) :
    O.valuation T.det = O.valuation T'.det :=
  le_antisymm (mu_det_le O T T' fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)
    (mu_det_le O T' T fun k => h ▸ Submodule.subset_span ⟨k, rfl⟩)

theorem mu_coord {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω) (i : Ω →+* Ω₃) (hi : ∀ a ∈ R, i a ∈ O)
    (c : Fin r → V) (hc : LinearIndependent Ω c) (Z : Set V) (Λ : Submodule O (Fin r → Ω₃))
    (hZ : ∀ w ∈ Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ) (x : Fin r → Ω)
    (hx : ∑ m, x m • c m ∈ Submodule.span R Z) : (fun m => i (x m)) ∈ Λ := by
  have key : ∀ w ∈ Submodule.span R Z, ∃ x : Fin r → Ω, w = ∑ m, x m • c m ∧ (fun m => i (x m)) ∈ Λ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hZ w hw
    | zero => exact ⟨0, by simp, by simp only [Pi.zero_apply, map_zero]; exact Λ.zero_mem⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, rfl, hx⟩ := ha
      obtain ⟨y, rfl, hy⟩ := hb
      refine ⟨x + y, by simp [add_smul, Finset.sum_add_distrib], ?_⟩
      convert Λ.add_mem hx hy using 1
      ext m; simp
    | smul a w _ hw =>
      obtain ⟨x, rfl, hx⟩ := hw
      refine ⟨fun m => (a : Ω) * x m, ?_, ?_⟩
      · rw [Subring.smul_def]
        simp [Finset.smul_sum, mul_smul]
      · convert Λ.smul_mem ⟨i a, hi a a.2⟩ hx using 1
        ext m
        show i (a * x m) = i a * i (x m)
        exact map_mul _ _ _
  obtain ⟨x', e, hx'⟩ := key _ hx
  have : x = x' := funext (Fintype.linearIndependent_iffₛ.1 hc x x' e)
  exact this ▸ hx'

theorem mu_alg {G : Type} [CommGroupWithZero G] {m₁ m₂ e₁ e₂ t₁ t₂ r₁ r₂ : G} (h₁ : m₁ * e₁ * t₁ = 1) (h₂ : m₂ * e₂ * t₂ = 1)
    (h : r₁ * t₁ = r₂ * t₂) (hr : r₁ ≠ 0) : m₂ = e₁ * r₂ / (r₁ * e₂) * m₁ := by
  have he : e₂ ≠ 0 := by rintro rfl; simp at h₂
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hr he)]
  calc m₂ * (r₁ * e₂) = m₂ * (r₁ * e₂) * (m₁ * e₁ * t₁) := by rw [h₁, mul_one]
    _ = m₂ * e₂ * (r₁ * t₁) * (m₁ * e₁) := by ac_rfl
    _ = m₂ * e₂ * t₂ * (e₁ * r₂ * m₁) := by rw [h]; ac_rfl
    _ = _ := by rw [h₂, one_mul]

end Lin

section Lats

variable {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] {ξ : Sp Ω ⟶ X} {q : Cpt ξ}

theorem mu_gen_ratio {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t) (h' : Λ.IsGenAt q t') : t' / t ∈ regAt ξ q := by
  have : t' ∈ Submodule.span (regAt ξ q) {t} := h.2 ▸ h'.2 ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
  have e : (a : Ω) * t = t' := ha
  rw [← e, mul_div_cancel_right₀ _ h.1]
  exact a.2

theorem mu_gen_val {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q) {Λ : Lat ξ Ω} {t t' : Ω} (h : Λ.IsGenAt q t)
    (h' : Λ.IsGenAt q t') : O.valuation (i t) = O.valuation (i t') := by
  have k : ∀ {t t' : Ω}, Λ.IsGenAt q t → Λ.IsGenAt q t' → O.valuation (i t') ≤ O.valuation (i t) := fun {t t'} h h' => by
    have h1 := (O.valuation_le_one_iff _).2 (hD.1 _ (mu_gen_ratio h h'))
    have e : t' = t * (t' / t) := (mul_div_cancel₀ _ h.1).symm
    rw [e, map_mul, map_mul]
    exact mul_le_of_le_one_right' h1
  exact le_antisymm (k h' h) (k h h')

theorem mu_tens_gen {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} (a : I → ℤ) {t : I → Ω} (h : ∀ j, (Λ j).IsGenAt q (t j)) :
    (Lat.tens Λ a).IsGenAt q (∏ j, t j ^ a j) := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (h j).1, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨s, hs, rfl⟩
    have hm : ∏ j, (s j / t j) ^ a j ∈ regAt ξ q := prod_mem fun j _ => by
      obtain ⟨n, e | e⟩ := (a j).eq_nat_or_neg
      · rw [e, zpow_natCast]; exact pow_mem (mu_gen_ratio (h j) (hs j)) _
      · rw [e, zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem (mu_gen_ratio (hs j) (h j)) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ j, (s j / t j) ^ a j) * ∏ j, t j ^ a j = _
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← mul_zpow, div_mul_cancel₀ _ (h j).1]
  · rintro _ rfl
    exact Submodule.subset_span ⟨t, h, rfl⟩

theorem mu_tens_ex {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {a : I → ℤ} {w : Ω} (h : (Lat.tens Λ a).IsGenAt q w) :
    ∃ t : I → Ω, ∀ j, (Λ j).IsGenAt q (t j) := by
  by_contra hn
  have e : (Lat.tens Λ a) q = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨s, hs, rfl⟩
    exact absurd ⟨s, hs⟩ hn
  have : w ∈ (Lat.tens Λ a) q := h.2 ▸ Submodule.mem_span_singleton_self _
  rw [e] at this
  exact h.1 this

theorem mu_deg_gen {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {Λ : Lat ξ Ω} {a : K → ℤ} {e : Ω}
    (h : Λ.IsDegOn Set.univ y a e) {ch : ∀ k, J k} (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ch q) :
    Λ.IsGenAt q ((∏ k, y ⟨k, ch k⟩ ^ a k) * e) :=
  ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _))) h.1,
    h.2 q trivial ch hc⟩

theorem mu_char0 [Algebra ℚ Ω₃] {O : ValuationSubring Ω₃} {i : Ω →+* Ω₃} (hD : Dom O i ξ q)
    (hO : ∀ x : ℚ, algebraMap ℚ Ω₃ x ∈ O) (p : ℕ) (hp : p.Prime) : ¬ InFibre ξ p q := by
  have : CharZero Ω₃ := algebraRat.charZero Ω₃
  have h0 : (p : Ω) ≠ 0 := fun h => by
    have := congrArg i h
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (Nat.cast_eq_zero.1 this)
  refine not_not.2 ⟨h0, natCast_mem _ _, hD.2 _ (natCast_mem _ _) h0 ?_⟩
  simpa using hO (p : ℚ)⁻¹

theorem mu_side {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) {r r' : ℕ} (hr : r = r') (W : Submodule Ω V)
    (hL : L.IsVB r W) (c : Fin r → V) (hc : LinearIndependent Ω c) (hW : Submodule.span Ω (Set.range c) = W)
    (s : Fin r' → V) (hs : LinearIndependent Ω s) (hsW : ∀ k, s k ∈ W) :
    ∃ ρ : Ω, ρ ≠ 0 ∧ ∀ (q : Cpt ξ) (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃) (Ω₀ : Type) (ψ : Ω₀ → Ω) (B : Set (Fin r → Ω₀)),
      Dom O i ξ q → L q = Submodule.span (regAt ξ q) {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} →
      ∃ (t : Ω) (T : Matrix (Fin r) (Fin r) Ω₃), (detLat L s).IsGenAt q t ∧ T.det = i (ρ * t) ∧
        Submodule.span O (Set.range fun k m => T m k) = Submodule.span O {x | ∃ a ∈ B, x = fun m => i (ψ (a m))} := by
  subst hr
  subst hW
  choose P hP using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hsW k)
  have hPi : LinearIndependent Ω P := by
    refine LinearIndependent.of_comp (Fintype.linearCombination Ω c) ?_
    convert hs using 1
    funext k
    simpa [Fintype.linearCombination_apply] using hP k
  set Pm : Matrix (Fin r) (Fin r) Ω := (Matrix.of P).transpose with hPm
  have hd : Pm.det ≠ 0 := by
    rw [hPm, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hPi)).ne_zero
  refine ⟨Pm.det, hd, fun q O i Ω₀ ψ B hD hq => ?_⟩
  obtain ⟨U, hU, b, hb, hf⟩ := hL q trivial
  have hf := hf q trivial hU
  choose T₀ hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1
    (show b k ∈ Submodule.span Ω (Set.range c) from hb ▸ Submodule.subset_span ⟨k, rfl⟩)
  set Tm : Matrix (Fin r) (Fin r) Ω := (Matrix.of T₀).transpose with hTm
  have hPT : Pm * (Pm⁻¹ * Tm) = Tm := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hd), Matrix.one_mul]
  have hbs : ∀ k, b k = ∑ k', (Pm⁻¹ * Tm) k' k • s k' := fun k => by
    rw [← hT k]
    simp only [← hP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun hPT m) k
    rw [Matrix.mul_apply] at this
    rw [show T₀ k m = Tm m k from rfl, ← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨(Pm⁻¹ * Tm).det, Tm.map i, GlobalTheory.T.det_lattice_frame_gen X Ω ξ V L r s b _ q hs hf hbs, ?_, le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_le.2 ?_)⟩
  · rw [← Matrix.det_mul, hPT]
    exact (RingHom.map_det i _).symm
  · rintro _ ⟨k, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc {w | ∃ a ∈ B, w = ∑ m, ψ (a m) • c m} _ ?_ (T₀ k) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨_, rfl, Submodule.subset_span ⟨a, ha, rfl⟩⟩
    · rw [← hq, hT k, hf.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine mu_coord O (regAt ξ q) i hD.1 c hc (Set.range b) _ ?_ (fun m => ψ (a m)) ?_
    · rintro _ ⟨k, rfl⟩
      exact ⟨T₀ k, (hT k).symm, Submodule.subset_span ⟨k, rfl⟩⟩
    · rw [← hf.2, hq]
      exact Submodule.subset_span ⟨a, ha, rfl⟩

end Lats

end SheetDecomposition
end
end

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

def muRev (p q : ℕ) (m : Fin q) : Fin (p + q) := ⟨p + q - 1 - m, by have := m.2; omega⟩

theorem muDeg_eq {Ψ K : Type} [Fintype Ψ] {p q : ℕ} (x : Ψ × Fin (p + q) → K → ℤ) :
    muDeg x = ∑ τ, ∑ m : Fin q, x (τ, muRev p q m) := by
  refine Finset.sum_congr rfl fun τ _ => (Finset.sum_bij (fun m _ => muRev p q m) ?_ ?_ ?_ fun _ _ => rfl).symm
  · intro m _
    have := m.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, muRev]
    omega
  · intro a _ b _ h
    have h := congrArg Fin.val h
    have := a.2
    have := b.2
    simp only [muRev] at h
    exact Fin.ext (by omega)
  · intro i hi
    have h1 := (Finset.mem_filter.1 hi).2
    have h2 := i.2
    exact ⟨⟨p + q - 1 - i, by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [muRev]; omega)⟩

theorem mu_mono_sum {Ω K I : Type} [Field Ω] [Fintype K] (z : K → Ω) (hz : ∀ k, z k ≠ 0) (s : Finset I) (a : I → K → ℤ) :
    ∏ k, z k ^ (∑ j ∈ s, a j) k = ∏ j ∈ s, ∏ k, z k ^ a j k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, ← ih, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hz k) _ _

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S' : Finset ℕ} {Ω' : Type} [Field Ω'] {K' : Type} [Fintype K']
  {J' : K' → Type} [∀ k, Fintype (J' k)] {y' : (Σ k, J' k) → Ω'} {𝔐' : HodgeCpt Y S' y'} (Fl : 𝔐'.Flag)

omit [∀ k, Fintype (J' k)] in
theorem mu_rootLat (τ : CMType H) (m : Fin D.q) : Fl.rootLat (τ, muRev D.p D.q m) =
    Lat.tens (fun _ : Unit => (𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) m) fun _ => -1 := by
  have hm := m.2
  have h0 : ¬ ((muRev D.p D.q m : ℕ) < D.p) := by simp only [muRev]; omega
  have h1 : HodgeCpt.rootIdx D (τ, muRev D.p D.q m) = ⟨.inr τ, m⟩ := by
    unfold HodgeCpt.rootIdx
    rw [dite_eq_right h0]
    congr 1
    exact Fin.ext (by simp only [muRev]; omega)
  have h2 : HodgeCpt.rootSgn D (τ, muRev D.p D.q m) = -1 := if_neg h0
  unfold HodgeCpt.Flag.rootLat
  rw [h1, h2]

theorem mu_flag_side (hC : ChartVal) {x : CMType H × Fin (D.p + D.q) → K' → ℤ} {e : CMType H × Fin (D.p + D.q) → Ω'}
    (hR : Fl.RootLines x e) (hb : ∀ s, LinearIndependent Ω' (Fl.b s)) {Ω₃ : Type} [Field Ω₃] {O : ValuationSubring Ω₃}
    {i : Ω' →+* Ω₃} {q : Cpt 𝔐'.ξ} (hD : Dom O i 𝔐'.ξ q) {t : CMType H → Ω'}
    (ht : ∀ τ, (detLat (𝔐'.V (.inr τ)) (Fl.b (.inr τ))).IsGenAt q (t τ)) :
    vdeg O (fun a => i (y' a)) (muDeg x) * O.valuation (i (∏ τ, ∏ m, e (τ, muRev D.p D.q m))) * O.valuation (i (∏ τ, t τ)) = 1 := by
  obtain ⟨ch, hch⟩ := 𝔐'.tie.cover q
  have hz : ∀ k, y' ⟨k, ch k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ _)
  have g1 := fun τ m => mu_deg_gen (hR (τ, muRev D.p D.q m)) hch
  simp only [mu_rootLat] at g1
  choose g hg using fun τ m => mu_tens_ex (g1 τ m)
  have v1 : ∀ τ m, O.valuation (i ((∏ k, y' ⟨k, ch k⟩ ^ x (τ, muRev D.p D.q m) k) * e (τ, muRev D.p D.q m))) *
      O.valuation (i (g τ m ())) = 1 := fun τ m => by
    rw [mu_gen_val hD (g1 τ m) (mu_tens_gen _ (hg τ m)), ← map_mul, ← map_mul]
    simp [(hg τ m ()).1]
  have v2 : ∀ τ, O.valuation (i (t τ)) = ∏ m, O.valuation (i (g τ m ())) := fun τ => by
    have h := ht τ
    rw [GlobalTheory.T.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb _) (Fl.sub _)] at h
    rw [mu_gen_val hD h (mu_tens_gen _ fun m => hg τ m ())]
    simp only [zpow_one, map_prod]
    rfl
  rw [hC _ _ _ O i _ q _ _ y' ch _ hD hch, muDeg_eq, mu_mono_sum _ hz]
  simp only [mu_mono_sum _ hz, map_prod O.valuation, map_prod i (s := Finset.univ (α := CMType H)),
    map_prod i (s := Finset.univ (α := Fin D.q)), v2, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun m _ => ?_
  rw [← v1 τ m, map_mul, map_mul]

end

theorem muLink : ChartVal → Centre → CoordLat → MuLink := by
  intro hC hZ hL E _ _ _ _ H D Xo l c Y S' Ω' _ K' _ J' _ y' 𝔐' Fl x e II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or ψ Ω₃ _ _ i₁ i₂ hR hbg hsm hS
    hψ hi
  classical
  obtain ⟨b, u, hb, -, -, hFl, -, -, hstep, -⟩ := Fl.generic
  obtain ⟨A, hA, hj, hoth⟩ := hL E H D l (Xo l) c Y S' Ω' K' J' y' 𝔐' Fl b hb
  obtain ⟨b₁, hb₁, hA₁⟩ := hoth S₀ Ω K J Dc.y Or.𝔐 ψ hψ
  have hmem : ∀ s m, Fl.b s m ∈ 𝔐'.Vgen s := fun s m => by
    have h1 : Fl.b s m ∈ flagStep Ω' (Fl.b s) (labelRk D s) := Submodule.subset_span ⟨m, m.2, rfl⟩
    rw [hstep] at h1
    refine (Submodule.span_le.2 ?_ : _ ≤ 𝔐'.Vgen s) h1
    rintro _ ⟨k, -, rfl⟩
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ((hj s).2 ▸ Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨ch₀, hch₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨n, f, cc, -, -, hsum, hloc⟩ := Hd.locally ch₀ hch₀.1
  obtain ⟨l₀⟩ : Nonempty (Fin n) := by
    by_contra h
    have := not_nonempty_iff.1 h
    simp at hsum
  obtain ⟨bb, -, w, -, hΛ⟩ := hloc l₀
  have hs : ∀ τ k, ∃ z, z ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - z ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    obtain ⟨a, ha, z, hz, h⟩ := Submodule.mem_sup.1
      (Or.i_range τ ▸ LinearMap.mem_range_self (Or.i τ) (bb τ (tailIdx Dc.j_le_N k)))
    exact ⟨z, hz, by rw [← h, add_sub_cancel_right]; exact ha⟩
  choose s hs using hs
  obtain ⟨hsi, hdeg⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or 0 bb s _ hs hΛ
  have hSB : Dc.SB 0 = ∅ := by simp [ComponentData.SB, hS]
  have hmu : muTwDeg Hd 0 = Hd.aMu := by simp [muTwDeg, hSB]
  rw [hmu, hSB, Finset.union_empty, hsm] at hdeg
  obtain ⟨e₁, hdeg⟩ : ∃ e₁, (Lat.tens (fun τ => detLat (Or.𝔐.V (.inr τ)) (s τ)) fun _ => -1).IsDegOn Set.univ Dc.y Hd.aMu e₁ :=
    ⟨_, hdeg⟩
  have hrk : ∀ τ : CMType H, labelRk D (.inr τ) = Dc.N - Dc.j := fun τ => by
    have := Or.rk_sm τ
    rwa [hsm] at this
  choose ρ₁ hρ₁ h₁ using fun τ => mu_side (Ω₃ := Ω₃) (Or.𝔐.V (.inr τ)) (hrk τ) _ (Or.𝔐.vb _) _ (hb₁ _).1 (hb₁ _).2 (s τ) (hsi τ)
    fun k => by
      have := (hs τ k).1
      rwa [hsm] at this
  choose ρ₂ hρ₂ h₂ using fun τ => mu_side (Ω₃ := Ω₃) (𝔐'.V (.inr τ)) rfl _ (𝔐'.vb _) _ (hj _).1 (hj _).2 (Fl.b (.inr τ)) (hFl _)
    (hmem _)
  have n1 : i₁ (∏ τ, ρ₁ τ) ≠ 0 := (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => hρ₁ τ)
  have n2 : i₂ (∏ τ, ρ₂ τ) ≠ 0 := (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => hρ₂ τ)
  have n3 : i₂ (∏ τ, ∏ m, e (τ, muRev D.p D.q m)) ≠ 0 :=
    (map_ne_zero _).2 (Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun m _ => (hR _).1)
  refine ⟨i₁ e₁ * i₂ (∏ τ, ρ₂ τ) / (i₁ (∏ τ, ρ₁ τ) * i₂ (∏ τ, ∏ m, e (τ, muRev D.p D.q m))),
    div_ne_zero (mul_ne_zero ((map_ne_zero _).2 hdeg.1) n2) (mul_ne_zero n1 n3), fun O hO => ?_⟩
  obtain ⟨q, q', hD, hD', hq⟩ := hZ E H D l (Xo l) c Y S₀ S' Ω Ω' Ω₃ K K' J J' Dc.y y' Or.𝔐 𝔐' i₁ i₂ O (by
    have e1 : Or.𝔐.ξ ≫ Or.𝔐.f = spMap ψ ≫ 𝔐'.ξ₀ := hψ
    have e2 : 𝔐'.ξ ≫ 𝔐'.f = spMap 𝔐'.fn ≫ 𝔐'.ξ₀ := 𝔐'.fn_over
    rw [e1, e2, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hi])
  choose t₁ T₁ g₁ d₁ sp₁ using fun τ => h₁ τ q O i₁ _ ψ _ hD (hA₁ q (mu_char0 hD hO) (.inr τ))
  choose t₂ T₂ g₂ d₂ sp₂ using fun τ => h₂ τ q' O i₂ _ 𝔐'.fn _ hD' (hA q' (mu_char0 hD' hO) (.inr τ))
  have hi' : ∀ a, i₁ (ψ a) = i₂ (𝔐'.fn a) := fun a => DFunLike.congr_fun hi a
  have k3 : O.valuation (i₁ (∏ τ, ρ₁ τ)) * O.valuation (i₁ (∏ τ, t₁ τ)) =
      O.valuation (i₂ (∏ τ, ρ₂ τ)) * O.valuation (i₂ (∏ τ, t₂ τ)) := by
    simp only [map_prod, ← Finset.prod_mul_distrib, ← map_mul, ← d₁, ← d₂]
    refine Finset.prod_congr rfl fun τ _ => mu_det_eq O _ _ ?_
    rw [sp₁, sp₂, hq]
    simp only [hi']
  have k2 := mu_flag_side Fl hC hR hFl hD' g₂
  obtain ⟨ch, hch⟩ := Or.𝔐.tie.cover q
  have k1 : vdeg O (fun a => i₁ (Dc.y a)) Hd.aMu * O.valuation (i₁ e₁) * O.valuation (i₁ (∏ τ, t₁ τ)) = 1 := by
    rw [hC _ _ _ O i₁ _ q _ _ Dc.y ch _ hD hch, ← map_mul O.valuation (i₁ _) (i₁ e₁), ← map_mul i₁, mu_gen_val hD (mu_deg_gen hdeg hch) (mu_tens_gen _ g₁),
      ← map_mul, ← map_mul, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun τ _ => by simp [(g₁ τ).1]]
    simp
  rw [map_div₀, map_mul, map_mul]
  exact mu_alg k1 k2 k3 ((map_ne_zero _).2 n1)

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushJoin
noncomputable section

namespace SheetDecomposition

open scoped TensorProduct

namespace Join

theorem tower {P Ω : Type} [Field P] [Field Ω] (φ : P →+* Ω) (K₀ : Subfield P) :
    Module.finrank (K₀.map φ) Ω = Module.finrank K₀ P * Module.finrank φ.fieldRange Ω := by
  letI : Algebra P Ω := φ.toAlgebra
  letI : Algebra K₀ Ω := (φ.comp K₀.subtype).toAlgebra
  haveI : IsScalarTower K₀ P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : Module.finrank P Ω = Module.finrank φ.fieldRange Ω :=
    Algebra.finrank_eq_of_equiv_equiv φ.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)
  have h2 : Module.finrank K₀ Ω = Module.finrank (K₀.map φ) Ω :=
    Algebra.finrank_eq_of_equiv_equiv (K₀.toSubring.equivMapOfInjective φ φ.injective) (RingEquiv.refl Ω)
      (RingHom.ext fun _ => rfl)
  rw [← h1, ← h2, Module.finrank_mul_finrank]

theorem finrank_congr {Ω : Type} [Field Ω] {A B : Subfield Ω} (h : A = B) : Module.finrank A Ω = Module.finrank B Ω := by
  subst h; rfl

theorem map_adjoin {F P Ω : Type} [Field F] [Field P] [Field Ω] [Algebra F P] [Algebra F Ω] (φ : P →+* Ω)
    (hφ : φ.comp (algebraMap F P) = algebraMap F Ω) {I : Type} (w : I → P) :
    (IntermediateField.adjoin F (Set.range w)).toSubfield.map φ =
      (IntermediateField.adjoin F (Set.range fun q => φ (w q))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    ← Set.range_comp, ← Set.range_comp, ← hφ]
  rfl

theorem core (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A] [Algebra F B] {I : Type} (w : I → B) (d₂ e : ℕ)
    (hw : AlgebraicIndependent F w) (hd : 0 < d₂) (hB : Module.finrank (IntermediateField.adjoin F (Set.range w)) B = d₂)
    (he : 0 < e) (hA : Module.finrank F A = e) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra A Ω) (i : B →+* Ω) (d n : ℕ),
      i.comp (algebraMap F B) = (algebraMap A Ω).comp (algebraMap F A) ∧ AlgebraicIndependent A (fun q => i (w q)) ∧ 0 < d ∧
      Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω = d ∧
      Module.finrank i.fieldRange Ω = n ∧ 0 < n ∧ n * d₂ = d * e := by
  haveI : FiniteDimensional F A := Module.finite_of_finrank_pos (hA ▸ he)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (B ⊗[F] A)
  letI : Field ((B ⊗[F] A) ⧸ m) := Ideal.Quotient.field m
  let j : A →ₐ[F] ((B ⊗[F] A) ⧸ m) := (Ideal.Quotient.mkₐ F m).comp Algebra.TensorProduct.includeRight
  letI : Algebra A ((B ⊗[F] A) ⧸ m) := j.toRingHom.toAlgebra
  haveI : IsScalarTower F A ((B ⊗[F] A) ⧸ m) := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Module.Finite B ((B ⊗[F] A) ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ B m).toLinearMap (Ideal.Quotient.mkₐ_surjective B m)
  let Ω := ((B ⊗[F] A) ⧸ m)
  let i : B →+* Ω := algebraMap B Ω
  have hi : i.comp (algebraMap F B) = algebraMap F Ω := (IsScalarTower.algebraMap_eq F B Ω).symm
  have hx0 : AlgebraicIndependent F (fun q => i (w q)) :=
    hw.map' (f := IsScalarTower.toAlgHom F B Ω) (algebraMap B Ω).injective
  have hx : AlgebraicIndependent A (fun q => i (w q)) := hx0.extendScalars A
  have hn : 0 < Module.finrank i.fieldRange Ω := by
    rw [← Algebra.finrank_eq_of_equiv_equiv i.rangeRestrictFieldEquiv (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)]
    exact Module.finrank_pos
  have t1 := tower i (IntermediateField.adjoin F (Set.range w)).toSubfield
  rw [finrank_congr (map_adjoin i hi w)] at t1
  let P := FractionRing (MvPolynomial I A)
  let φ : P →+* Ω := (IntermediateField.adjoin A (Set.range fun q => i (w q))).val.toRingHom.comp hx.aevalEquivField.toRingEquiv.toRingHom
  letI : Algebra F P := ((algebraMap A P).comp (algebraMap F A)).toAlgebra
  have hφA : ∀ a, φ (algebraMap A P a) = algebraMap A Ω a := fun a => congrArg Subtype.val (hx.aevalEquivField.commutes a)
  have hφ : φ.comp (algebraMap F P) = algebraMap F Ω := RingHom.ext fun a =>
    (hφA _).trans (IsScalarTower.algebraMap_apply F A Ω a).symm
  have hX : (fun q => φ (algebraMap (MvPolynomial I A) P (MvPolynomial.X q))) = fun q => i (w q) := funext fun q =>
    (hx.aevalEquivField_algebraMap_apply_coe _).trans (MvPolynomial.aeval_X _ q)
  have hr : φ.fieldRange = (IntermediateField.adjoin A (Set.range fun q => i (w q))).toSubfield := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hx.aevalEquivField y).2
    · intro hz
      exact ⟨hx.aevalEquivField.symm ⟨z, hz⟩, congrArg Subtype.val (hx.aevalEquivField.apply_symm_apply ⟨z, hz⟩)⟩
  have t2 := tower φ (IntermediateField.adjoin F (Set.range fun q => algebraMap (MvPolynomial I A) P (MvPolynomial.X q))).toSubfield
  rw [finrank_congr (map_adjoin φ hφ _), hX, finrank_congr hr] at t2
  have t3 := GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq F A I rfl
  have key : d₂ * Module.finrank i.fieldRange Ω =
      e * Module.finrank (IntermediateField.adjoin A (Set.range fun q => i (w q))) Ω := by
    rw [← hB, ← hA, ← t3]
    exact t1.symm.trans t2
  refine ⟨Ω, inferInstance, inferInstance, i, _, _, hi.trans (IsScalarTower.algebraMap_eq F A Ω), hx, ?_, rfl, rfl, hn, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, mul_zero] at key
    exact (Nat.mul_pos hd hn).ne' key
  · rw [mul_comm, key, mul_comm]

theorem adjoin_entries (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {S : Type} {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1) (h0 : ∀ s l m, l < m → u s l m = 0) :
    IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k
        (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    show u s l m ∈ _
    rcases lt_trichotomy l m with h | rfl | h
    · rw [h0 s l m h]; exact zero_mem _
    · rw [h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, m), h⟩⟩, rfl⟩
  · rintro _ ⟨⟨s, lm, h⟩, rfl⟩
    exact ⟨⟨s, lm⟩, rfl⟩

end Join

theorem fieldJoin : FieldJoin := by
  intro Ω₀ Ω₁ Ω₂ _ _ _ _ _ S _ r u d₂ e ⟨h1, h0, hi, hd, hf⟩ he hA
  rw [Join.adjoin_entries Ω₀ u h1 h0] at hf
  obtain ⟨Ω, _, _, i, d, n, a1, a2, a3, a4, a5, a6, a7⟩ := Join.core Ω₀ Ω₁ Ω₂ _ d₂ e hi hd hf he hA
  have g1 : ∀ s m, (u s).map i m m = 1 := fun s m => by simp [h1]
  have g0 : ∀ s l m, l < m → (u s).map i l m = 0 := fun s l m h => by simp [h0 s l m h]
  refine ⟨Ω, inferInstance, inferInstance, i, d, n, a1, ⟨g1, g0, a2, a3, ?_⟩, a5, a6, a7⟩
  rw [Join.adjoin_entries Ω₁ (fun s => (u s).map i) g1 g0]
  exact a4

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushCentre
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem genMap_fromSpec {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (q : Cpt ξ) :
    spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 = ξ := by
  have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
  have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 : spMap (genMap ξ q) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
    rw [← Spec.map_comp]
    rfl
  rw [e2, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4

theorem genMap_bij {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (h : IsCptGen ξ) (q : Cpt ξ) (e : q.1 = genPt ξ) :
    Function.Bijective (genMap ξ q) := by
  obtain ⟨p, hp⟩ := q
  subst e
  have : X.presheaf.stalkSpecializes hp = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  simp only [this]
  exact h.bij

theorem genIso : GenIso := by
  intro X Ω Ω' _ _ ξ ξ' h h' e
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  let q' : Cpt ξ' := ⟨genPt ξ, e ▸ specializes_rfl⟩
  let a := RingEquiv.ofBijective _ (genMap_bij h q rfl)
  let a' := RingEquiv.ofBijective _ (genMap_bij h' q' e)
  refine ⟨a'.symm.trans a, ?_⟩
  have hc : (a'.symm.trans a).toRingHom.comp (genMap ξ' q') = genMap ξ q := by
    ext x
    show a (a'.symm (a' x)) = a x
    rw [a'.symm_apply_apply]
  have h1 := genMap_fromSpec ξ q
  have h2 := genMap_fromSpec ξ' q'
  rw [← hc] at h1
  calc ξ = _ := h1.symm
    _ = spMap (a'.symm.trans a).toRingHom ≫ spMap (genMap ξ' q') ≫ X.fromSpecStalk q'.1 := by
      rw [← Category.assoc, ← Spec.map_comp]
      rfl
    _ = _ := by rw [h2]

theorem seg_ratio {Ω : Type} [Field Ω] {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} (y : (Σ k, J k) → Ω)
    (ch : ∀ k, J k) (h : ∏ k, y ⟨k, ch k⟩ ≠ 0) (k : K) (j : J k) :
    (∏ k', y ⟨k', Function.update ch k j k'⟩) / ∏ k', y ⟨k', ch k'⟩ = y ⟨k, j⟩ / y ⟨k, ch k⟩ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)] at h
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun k' => y ⟨k', ch k'⟩) (Finset.mem_univ k),
    Function.update_self, Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')],
    mul_div_mul_right _ _ (right_ne_zero_of_mul h)]

theorem chartVal : ChartVal := by
  intro X Ω Ω₃ _ _ O i ξ q K _ J _ y ch a hD hc
  classical
  unfold vdeg
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow₀, map_zpow₀]
  congr 1
  refine le_antisymm (Finset.sup_le fun j _ => ?_) (Finset.le_sup (f := fun j => O.valuation (i (y ⟨k, j⟩))) (Finset.mem_univ _))
  have h0 : y ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ _)
  have h1 := hD.1 _ (hc.2 (Function.update ch k j))
  rw [seg_ratio y ch hc.1, ← O.valuation_le_one_iff, map_div₀, map_div₀,
    div_le_one₀ (zero_lt_iff.2 (by simpa using h0))] at h1
  exact h1

theorem dom_of_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) (ha : ∀ q : X, genPt ξ ⤳ q) (z : Sp O ⟶ X) (hz : spMap O.subtype ≫ z = spMap i ≫ ξ) :
    ∃ q : Cpt ξ, Dom O i ξ q := by
  let q : Cpt ξ := ⟨z (IsLocalRing.closedPoint O), ha _⟩
  let φ : X.presheaf.stalk q.1 →+* O := (Scheme.stalkClosedPointTo z).hom
  have hl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have e1 : spMap φ ≫ X.fromSpecStalk q.1 = z := Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
  have e2 : spMap (O.subtype.comp φ) = spMap (i.comp (genMap ξ q)) := by
    rw [← cancel_mono (X.fromSpecStalk q.1)]
    calc _ = spMap O.subtype ≫ spMap φ ≫ X.fromSpecStalk q.1 := by
          rw [← Category.assoc, ← Spec.map_comp]; rfl
      _ = spMap i ≫ spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [e1, genMap_fromSpec, hz]
      _ = _ := by rw [← Category.assoc, ← Spec.map_comp]; rfl
  have e3 : ∀ s, ((φ s : O) : Ω₃) = i (genMap ξ q s) := fun s =>
    congrArg (fun f => f.hom s) (Spec.map_injective e2)
  refine ⟨q, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← e3]
    exact (φ s).2
  · rintro _ ⟨s, rfl⟩ h0 h1
    have hu : IsUnit (φ s) := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
      show ((φ s : O) : Ω₃) * _ = 1
      rw [e3, mul_inv_cancel₀ ((map_ne_zero i).2 h0)]))
    obtain ⟨t, ht⟩ := (hl.1 s hu).exists_right_inv
    refine ⟨t, eq_inv_of_mul_eq_one_right ?_⟩
    rw [← map_mul, ht, map_one]

theorem exists_point {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {κ : Type} (x : κ → Ω) (ht : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (hO : ∀ j, i (x j / x c) ∈ O) :
    ∃ z : Sp O ⟶ X, spMap O.subtype ≫ z = spMap i ≫ ξ := by
  obtain ⟨U, hU, hm⟩ := ht.affine c hc
  let q : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hq : q.1 ∈ U := (hm _).2 ⟨q.2, hc, fun c' => (genMap_bij ht.gen q rfl).2 _⟩
  let φ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hq).hom
  have h1 : ∀ s, i (φ s) ∈ O := fun s => by
    have : φ s ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := (ht.ring c hc _).2 fun p hp => by
      have hpU : p.1 ∈ U := (hm _).2 ⟨p.2, hp⟩
      refine ⟨X.presheaf.germ U p.1 hpU s, ?_⟩
      show Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes p.2 _) =
        Scheme.stalkClosedPointTo ξ (X.presheaf.stalkSpecializes q.2 _)
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, TopCat.Presheaf.germ_stalkSpecializes_apply]
    generalize φ s = a at this
    induction this using Algebra.adjoin_induction with
    | mem a h => obtain ⟨j, rfl⟩ := h; exact hO j
    | algebraMap n => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let ψ : Γ(X, U) →+* O := (i.comp φ).codRestrict O.toSubring h1
  refine ⟨spMap ψ ≫ hU.fromSpec, ?_⟩
  have e : Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec = X.fromSpecStalk q.1 := hU.fromSpecStalk_eq_fromSpecStalk hq
  calc _ = spMap i ≫ spMap (genMap ξ q) ≫ Spec.map (X.presheaf.germ U q.1 hq) ≫ hU.fromSpec := by
        simp only [← Category.assoc, ← Spec.map_comp]
        rfl
    _ = _ := by rw [e, genMap_fromSpec]

theorem exists_dom {X : Scheme.{0}} {Ω Ω₃ : Type} [Field Ω] [Field Ω₃] (O : ValuationSubring Ω₃) (i : Ω →+* Ω₃)
    (ξ : Sp Ω ⟶ X) {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (ha : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) : ∃ q : Cpt ξ, Dom O i ξ q := by
  obtain ⟨c₀, hc₀, -⟩ := ht.cover ⟨genPt ξ, specializes_rfl⟩
  have hm : ∀ k, ∃ j : J k, ∀ j', O.valuation (i (y ⟨k, j'⟩)) ≤ O.valuation (i (y ⟨k, j⟩)) := fun k => by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => O.valuation (i (y ⟨k, j⟩))) ⟨c₀ k, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose ch hch using hm
  have hp : ∀ k, 0 < O.valuation (i (y ⟨k, ch k⟩)) := fun k =>
    lt_of_lt_of_le (zero_lt_iff.2 (by simpa using Finset.prod_ne_zero_iff.1 hc₀ k (Finset.mem_univ _))) (hch k (c₀ k))
  have h0 : ∀ k, y ⟨k, ch k⟩ ≠ 0 := fun k h => by simpa [h] using hp k
  obtain ⟨z, hz⟩ := exists_point O i ξ _ ht ch (Finset.prod_ne_zero_iff.2 fun k _ => h0 k) fun j => by
    rw [← Finset.prod_div_distrib, map_prod]
    refine prod_mem fun k _ => ?_
    rw [← O.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ (hp k)]
    exact hch k (j k)
  exact dom_of_point O i ξ ha z hz

theorem centre : Centre := by
  intro E _ _ _ H D l Xo c Y S S' Ω Ω' Ω₃ _ _ _ K K' _ _ J J' _ _ y y' 𝔐 𝔐' i i' W hξ
  obtain ⟨q, hq⟩ := exists_dom W i 𝔐.ξ y 𝔐.all 𝔐.tie
  obtain ⟨q', hq'⟩ := exists_dom W i' 𝔐'.ξ y' 𝔐'.all 𝔐'.tie
  refine ⟨q, q', hq, hq', ?_⟩
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W i q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐'.ξ W i' q' (𝔐'.tie.gen.inj q') hq'
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐'.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    simpa only [Category.assoc] using hξ
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐'.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐'.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐'.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushLat
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat.CptStalk

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω₀ : Type} [Field Ω₀] {ξ₀ : Sp Ω₀ ⟶ Y.X} {Li₀ : Type}
  [AddCommGroup Li₀] [Module Ω₀ Li₀] (M₀ : LieModel Y.t.G ξ₀ Li₀) (ρ₀ : 𝓞 E →+* Module.End Ω₀ Li₀) (cst₀ : c.F →+* Ω₀)
  (b : ∀ s, Fin (labelRk D s) → Li₀)

def coordSet (s : CMType H ⊕ CMType H) (y₀ : Y.X) : Set (Fin (labelRk D s) → Ω₀) :=
  {a | ∃ h : genPt ξ₀ ⤳ y₀, ∑ m, a m • b s m ∈ M₀.eigLat ρ₀ (cst₀.comp (labelEmb c s)) ⟨y₀, h⟩}

variable {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

omit [∀ k, Fintype (J k)] in
theorem cst_eq (𝔐 : HodgeCpt Y S y) (ψ : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ ξ₀ 𝔐.f ψ)
    (hs : ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F))) : ψ.comp cst₀ = 𝔐.cst := by
  have h1 := 𝔐.cst_over
  rw [← Category.assoc, hd, Category.assoc, hs] at h1
  have h2 : 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) = (ψ.comp cst₀).comp (algebraMap (𝓞 c.F) c.F) := by
    have h3 := h1.symm
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h3
    have h4 := Spec.map_injective h3
    have h5 := congrArg CommRingCat.Hom.hom h4
    simpa using h5
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  exact (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2).symm

theorem lat_core (𝔐 : HodgeCpt Y S y) (ψ : Ω₀ →+* Ω) (j : Li₀ →+ 𝔐.Li) (hg : IsCptGen ξ₀)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ ξ₀ 𝔐.f ψ) (hs : ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)))
    (hact : M₀.IsActOf Y.t.act.act ρ₀)
    (hj : ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap ψ) ≫ (M₀.pt e).left)
    (hb : ∀ s, LinearIndependent Ω₀ (b s) ∧ Submodule.span Ω₀ (Set.range (b s)) = eigSp ρ₀ (cst₀.comp (labelEmb c s))) :
    (∀ s, LinearIndependent Ω (fun m => j (b s m)) ∧ Submodule.span Ω (Set.range fun m => j (b s m)) = 𝔐.Vgen s) ∧
      ∀ q : Cpt 𝔐.ξ, (∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q)
        {w | ∃ a ∈ coordSet M₀ ρ₀ cst₀ b s (𝔐.f q.1), w = ∑ m, ψ (a m) • j (b s m)} := by
  have hcst : ψ.comp cst₀ = 𝔐.cst := cst_eq (cst₀ := cst₀) 𝔐 ψ hd hs
  haveI : CharZero Ω₀ := (RingHom.charZero_iff cst₀.injective).mp inferInstance
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).mp inferInstance
  have hsemi : ∀ (a : Ω₀) (e : Li₀), j (a • e) = ψ a • j e := LiePull.semilin 𝔐.m.cart hj
  refine ⟨fun s => ?_, fun q hq s => ?_⟩
  · have hsm : Smooth Y.t.G.hom := Y.t.semi.smooth
    have hsm' : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
    obtain ⟨hext, htop, -⟩ := LiePull.main _ _ _ _ ξ₀ 𝔐.ξ 𝔐.f ψ Y.t.G 𝔐.t.G 𝔐.m.φ _ _ M₀ 𝔐.M j hg
      𝔐.tie.gen hd 𝔐.m.cart hsm hj
    have hli : LinearIndependent Ω (fun m => j (b s m)) := hext.2 _ (b s) (hb s).1
    refine ⟨hli, ?_⟩
    have hle : Submodule.span Ω (Set.range fun m => j (b s m)) ≤ 𝔐.Vgen s := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      have hm : b s m ∈ eigSp ρ₀ (cst₀.comp (labelEmb c s)) := (hb s).2 ▸ Submodule.subset_span ⟨m, rfl⟩
      have h1 := map_mem_eigSp 𝔐.m hact 𝔐.act hj hsemi _ hm
      rw [← RingHom.comp_assoc, hcst] at h1
      exact h1
    haveI : Module.Finite Ω₀ Li₀ := (LieProj.lie_finite_projective_baseChange _ _ _ _ _ M₀).1
    haveI : Module.Finite Ω 𝔐.Li := (LieProj.lie_finite_projective_baseChange _ _ _ _ _ 𝔐.M).1
    letI : Algebra Ω₀ Ω := ψ.toAlgebra
    have hsemi' : ∀ (a : Ω₀) (e : Li₀), j (a • e) = (algebraMap Ω₀ Ω) a • j e := hsemi
    let B := Module.finBasis Ω₀ Li₀
    have hBspan : Submodule.span Ω (Set.range fun k => j (B k)) = ⊤ := by
      rw [eq_top_iff, ← htop, Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← B.sum_repr e, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [hsemi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hfr := EigRank.finrank_eigSp_baseChange Ω₀ Ω (𝓞 E) Li₀ 𝔐.Li _ B j hsemi'
      (hext.2 _ B B.linearIndependent) hBspan ρ₀ 𝔐.ρ
      (fun a e => (map_act 𝔐.m hact 𝔐.act hj a e).symm) (cst₀.comp (labelEmb c s))
    have h0 : Module.finrank Ω₀ (eigSp ρ₀ (cst₀.comp (labelEmb c s))) = labelRk D s := by
      rw [← (hb s).2, finrank_span_eq_card (hb s).1, Fintype.card_fin]
    have h2 : (algebraMap Ω₀ Ω).comp (cst₀.comp (labelEmb c s)) = 𝔐.cst.comp (labelEmb c s) := by
      rw [RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc, hcst]
    rw [h2, h0] at hfr
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin, hfr]
    rfl
  · have hnot : ¬ ∃ p ∈ S, InFibre 𝔐.ξ p q := fun ⟨p, hp, hf⟩ => hq p (𝔐.S_prime p hp) hf
    have hV : 𝔐.V s q = 𝔐.M.eigLat 𝔐.ρ ((ψ.comp cst₀).comp (labelEmb c s)) q := by
      simp only [HodgeCpt.V, Lat.patch, if_neg hnot, HodgeCpt.dR, HodgeCpt.emb, hcst]
    rw [hV, eigLat_eq_pull c 𝔐.m cst₀ hg 𝔐.tie.gen hd hact 𝔐.act (isIntegrallyClosed_regAt Y.normal hg)
      (isIntegrallyClosed_regAt (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩) 𝔐.tie.gen) hj s q hq]
    simp only [Lat.pull]
    congr 1
    ext w
    simp only [Set.mem_setOf_eq, coordSet]
    constructor
    · rintro ⟨h, e, he, rfl⟩
      have he' : e ∈ eigSp ρ₀ (cst₀.comp (labelEmb c s)) := by
        simp only [LieModel.eigLat, Lat.inter] at he
        exact (Submodule.mem_inf.1 he).2
      rw [← (hb s).2, Submodule.mem_span_range_iff_exists_fun] at he'
      obtain ⟨a, rfl⟩ := he'
      refine ⟨a, ⟨h, he⟩, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hsemi]
    · rintro ⟨a, ⟨h, ha⟩, rfl⟩
      refine ⟨h, _, ha, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hsemi]

end

private theorem coordLat_lemma {S : Scheme} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V)
    {O : Type} [CommRing O] (act : OAct O G) : ∃ ρ : O →+* Module.End R V, M.IsActOf act.act ρ := by
  have htan : ∀ (a : O) (e : V), IsTanAt G x (M.pt e ≫ act.act a) := by
    intro a e
    haveI := act.hom a
    have h1 := M.tan e
    simp only [IsTanAt] at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  choose F hF using fun a e => M.onto _ (htan a e)
  have hadd : ∀ a e e', F a (e + e') = F a e + F a e' := by
    intro a e e'
    haveI := act.hom a
    apply M.inj
    rw [hF, M.add, M.add, hF, hF, MonObj.mul_comp]
  have hsmul : ∀ a (r : R) e, F a (r • e) = r • F a e := by
    intro a r e
    apply M.inj
    apply Over.OverMorphism.ext
    simp only [hF, Over.comp_left, M.smul, Category.assoc]
  let L : O → Module.End R V := fun a =>
    { toFun := F a, map_add' := hadd a, map_smul' := hsmul a }
  have hL : ∀ a e, M.pt (L a e) = M.pt e ≫ act.act a := hF
  have hone : L 1 = 1 := by
    ext e
    apply M.inj
    rw [hL, act.one, Category.comp_id]
    rfl
  have hmul : ∀ a b, L (a * b) = L a * L b := by
    intro a b
    ext e
    apply M.inj
    rw [Module.End.mul_apply, hL, hL, hL, show a * b = b * a from mul_comm a b, act.mul, Category.assoc]
  have haddL : ∀ a b, L (a + b) = L a + L b := by
    intro a b
    ext e
    apply M.inj
    rw [LinearMap.add_apply, M.add, hL, hL, hL, act.add, MonObj.comp_mul]
  have hzero : L 0 = 0 := by
    have h := haddL 0 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  exact ⟨{ toFun := L, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := haddL },
    fun a e => hL a e⟩

private theorem coordLat_lemma_2 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme}
    {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f) {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    {ξ₀ : Sp Ω₀ ⟶ X} {ξ : Sp Ω ⟶ X'} {ψ : Ω₀ →+* Ω} {V V' : Type} [AddCommGroup V] [Module Ω₀ V]
    [AddCommGroup V'] [Module Ω V'] (M₀ : LieModel t.G ξ₀ V) (M : LieModel t'.G ξ V')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f ψ) :
    ∃ j : V →+ V', ∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap ψ) ≫ (M₀.pt e).left := by
  obtain ⟨Mp, hMp⟩ := (LiePull.lieModel_pullback _ _ _ _ f m.φ m.cart Ω ξ V').2 M
  have key : ∀ x₂ : Sp Ω ⟶ X, ξ ≫ f = x₂ →
      ∃ Mq : LieModel t.G x₂ V', ∀ e, (Mq.pt e).left = (Mp.pt e).left := by
    rintro x₂ rfl
    exact ⟨Mp, fun _ => rfl⟩
  obtain ⟨Mq, hMq⟩ := key (spMap ψ ≫ ξ₀) hd
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts X t.G Ω₀ Ω ψ ξ₀ V V' M₀ Mq
  refine ⟨j.toAddMonoidHom, fun e => ?_⟩
  have h1 := hj e
  simp only [LieModel.Lifts, Category.comp_id] at h1
  change (M.pt (j e)).left ≫ m.φ = _
  rw [hMp, ← hMq, h1]

theorem coordLat : CoordLat := by
  intro E _ _ _ H D l Xo c Y S' Ω' _ K' _ J' _ y' 𝔐' Fl b hb
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  haveI : CharZero 𝔐'.Ω₀ := (RingHom.charZero_iff 𝔐'.fn.injective).mpr
    ((RingHom.charZero_iff 𝔐'.cst.injective).mp inferInstance)
  obtain ⟨ρ₀, hact⟩ := coordLat_lemma Fl.M₀ Y.t.act
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 c.F →+* 𝔐'.Ω₀, 𝔐'.ξ₀ ≫ Y.s = spMap r :=
    ⟨(Spec.preimage (𝔐'.ξ₀ ≫ Y.s)).hom, by simp [spMap, Spec.map_preimage]⟩
  have hfr : 𝔐'.fn.comp r = 𝔐'.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have h1 := 𝔐'.cst_over
    rw [← Category.assoc, 𝔐'.fn_over, Category.assoc, hr] at h1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    simpa using h2
  have hrinj : Function.Injective r := by
    have h1 : Function.Injective (𝔐'.fn.comp r) := by
      rw [hfr]
      exact 𝔐'.cst.injective.comp hβ
    exact Function.Injective.of_comp h1
  let cst₀ : c.F →+* 𝔐'.Ω₀ := IsFractionRing.lift hrinj
  have hcst₀ : cst₀.comp (algebraMap (𝓞 c.F) c.F) = r :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap hrinj x
  have hs : 𝔐'.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [hcst₀]
    exact hr
  have hcst' : 𝔐'.fn.comp cst₀ = 𝔐'.cst := cst_eq (cst₀ := cst₀) 𝔐' 𝔐'.fn 𝔐'.fn_over hs
  have hsemi : ∀ (a : 𝔐'.Ω₀) (e : Fl.Li₀), Fl.j (a • e) = 𝔐'.fn a • Fl.j e :=
    LiePull.semilin 𝔐'.m.cart Fl.j_pt
  obtain ⟨hext, -, -⟩ := LiePull.main _ _ _ _ 𝔐'.ξ₀ 𝔐'.ξ 𝔐'.f 𝔐'.fn Y.t.G 𝔐'.t.G 𝔐'.m.φ _ _ Fl.M₀ 𝔐'.M
    Fl.j 𝔐'.gen₀ 𝔐'.tie.gen 𝔐'.fn_over 𝔐'.m.cart Y.t.semi.smooth Fl.j_pt
  have hjinj : ∀ x, Fl.j x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have h1 := hext.2 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)
    exact (linearIndependent_unique_iff.1 h1) hx
  have hV0 : ∀ s, Fl.V₀ s = eigSp ρ₀ (cst₀.comp (labelEmb c s)) := by
    intro s
    ext e
    rw [Fl.V₀_mem]
    simp only [HodgeCpt.Vgen, HodgeCpt.emb, eigSp, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, RingHom.coe_comp, Function.comp_apply]
    refine forall_congr' fun a => ?_
    have h1 : Fl.j (ρ₀ a e - cst₀ (labelEmb c s a) • e) =
        𝔐'.ρ a (Fl.j e) - 𝔐'.cst (labelEmb c s a) • Fl.j e := by
      rw [map_sub, hsemi, map_act 𝔐'.m hact 𝔐'.act Fl.j_pt, ← RingHom.comp_apply 𝔐'.fn cst₀, hcst']
    constructor
    · intro h
      exact hjinj _ (h1.trans h)
    · intro h
      rw [← h1, h, map_zero]
  have hb₀ : ∀ s, LinearIndependent 𝔐'.Ω₀ (b s) ∧
      Submodule.span 𝔐'.Ω₀ (Set.range (b s)) = eigSp ρ₀ (cst₀.comp (labelEmb c s)) :=
    fun s => ⟨(hb s).1, (hb s).2.trans (hV0 s)⟩
  have hmain := lat_core (M₀ := Fl.M₀) (ρ₀ := ρ₀) (cst₀ := cst₀) (b := b) 𝔐' 𝔐'.fn Fl.j 𝔐'.gen₀
    𝔐'.fn_over hs hact Fl.j_pt hb₀
  refine ⟨fun s y₀ => coordSet Fl.M₀ ρ₀ cst₀ b s y₀, hmain.2, hmain.1, ?_⟩
  intro S Ω _ K _ J _ y 𝔐 ψ hd
  obtain ⟨j, hj⟩ := coordLat_lemma_2 𝔐.m Fl.M₀ 𝔐.M hd
  exact ⟨fun s m => j (b s m), lat_core (M₀ := Fl.M₀) (ρ₀ := ρ₀) (cst₀ := cst₀) (b := b) 𝔐 ψ j 𝔐'.gen₀
    hd hs hact hj hb₀⟩

end SheetDecomposition
end
end

namespace SheetDecomposition

theorem degPush : DegPush :=
  have hEq : NumEq := numEq ptDim numPull (unitZero ptDim)
  degPush_of hEq (geoPF ptDim) (fibNum hEq) trdegU testRelabel geoTest numMap muMass fieldJoin genIso
    (fibLink chartVal centre coordLat) (muLink chartVal centre coordLat)

end SheetDecomposition
