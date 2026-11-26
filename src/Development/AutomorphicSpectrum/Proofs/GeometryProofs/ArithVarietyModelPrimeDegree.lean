module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceLocalizationExists
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceTestFunction
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeCmTypeWeight

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceCoordinatesExist
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceCoordinates

theorem mem_of_loc {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (x : Ω)
    (h : ∀ 𝔮 : Ideal R, 𝔮.IsPrime → ∃ u v : R, v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) : x ∈ R := by
  let I : Ideal R :=
    { carrier := {v | x * (v : Ω) ∈ R}
      add_mem' := fun {a b} ha hb => by
        have := R.add_mem ha hb
        simpa [mul_add] using this
      zero_mem' := by simpa using R.zero_mem
      smul_mem' := fun c v hv => by
        have := R.mul_mem c.2 hv
        simp only [smul_eq_mul, Set.mem_setOf_eq, MulMemClass.coe_mul]
        rwa [mul_left_comm] }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨u, v, hv, huv⟩ := h M hM.isPrime
    refine hv (hle ?_)
    show x * (v : Ω) ∈ R
    rw [huv]; exact u.2
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  have h2 : x * ((1 : R) : Ω) ∈ R := h1
  simpa using h2

theorem mem_htW_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n : ℕ)
    {B : Type} [CommRing B] (ρ : B →+* Module.End Ω Li) (σ : B →+* Ω) (𝔡 : Ideal B) (q : Cpt ξ)
    (hσ : ∀ d, σ d ∈ regAt ξ q) (x : B) (hx : x ∈ 𝔡) (o : Ω) (ho : o ∈ regAt ξ q) (hox : o * σ x = 1) (e : Li) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ M.htDual L n ρ σ q := by
  constructor
  · intro he
    refine (Submodule.span_le.2 ?_ : M.htW L n ρ σ 𝔡 q ≤ M.htDual L n ρ σ q) he
    rintro e ⟨-, he⟩
    have h1 : o • σ x • e ∈ M.htDual L n ρ σ q := (M.htDual L n ρ σ q).smul_mem ⟨o, ho⟩ (he x hx)
    rw [smul_smul, hox, one_smul] at h1
    exact h1
  · intro he
    refine Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩
    exact (M.htDual L n ρ σ q).smul_mem ⟨σ d, hσ d⟩ he

theorem span_apply_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (R : Subring Ω)
    (T : Set (Module.Dual Ω V)) (e : V) :
    (∀ w ∈ Submodule.span R T, w e ∈ R) ↔ ∀ w ∈ T, w e ∈ R := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using R.zero_mem
  | add x y _ _ hx hy => simpa using R.add_mem hx hy
  | smul c x _ hx => exact R.mul_mem c.2 hx

end PositivityTheory.Xgn.SequenceCoordinates

theorem PositivityTheory.Xgn.sequence_coordinates_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ _ p _ _ b hb A _ _ _ m _ _ O _ _ _ _ _ _ _ G c' _ P s
    hemb hdiff hCR hpr hloc a
  have he : (∑ k, a k • b s k) ∈ eigSp 𝔐.ρ (𝔐.emb s) := by
    have h := (hb s).2
    unfold HodgeCpt.Vgen at h
    rw [← h]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨x, hx, o, hox⟩ := hdiff
  have key : ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) →
      ((∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ regAt 𝔐.ξ q) := by
    intro q h1 h2
    have hD : (∑ k, a k • b s k) ∈ 𝔐.HT p s q ↔
        (∑ k, a k • b s k) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q := by
      cases s with
      | inl τ =>
        refine PositivityTheory.Xgn.SequenceCoordinates.mem_htW_iff 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (.inl τ)) _ q
          (fun d => ?_) x hx _ (h2 o) hox _
        obtain ⟨o', ho'⟩ := hemb d
        rw [← ho']; exact h2 o'
      | inr τ => exact Iff.rfl
    rw [hD, LieModel.mem_htDual_iff, and_iff_right he]
    have hl : 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q = _ := hloc q h1 h2
    rw [hl, PositivityTheory.Xgn.SequenceCoordinates.span_apply_iff]
    rfl
  have hm : a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q →
      (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∑ k, a k • b s k ∈ 𝔐.HT p s q := by
    simp [coordLat, AddSubgroup.mem_iInf, Fintype.linearCombination_apply]
  rw [hm]
  constructor
  · intro h u hu
    refine PositivityTheory.Xgn.SequenceCoordinates.mem_of_loc _ _ fun 𝔮 h𝔮 => ?_
    obtain ⟨q, h1, h2, h3⟩ := hpr 𝔮 h𝔮
    exact (h3 _).1 ((key q h1 h2).1 (h q h1 h2) u hu)
  · intro h q h1 h2
    exact (key q h1 h2).2 fun u hu => hCR q h1 h2 _ (h u hu)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBound
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

open Module GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

section Abstract

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_std {R : Subalgebra o Ω} {T : Type} {x : T → Ω} : x ∈ stdLat R T ↔ ∀ k, x k ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_mulLat {V : Type} [AddCommGroup V] [Module Ω V] {c : Ω} {L : AddSubgroup V} {x : V} :
    x ∈ mulLat c L ↔ ∃ y ∈ L, c • y = x := by
  simp [mulLat, AddSubgroup.mem_map]

theorem mem_dotDual {R : Subalgebra o Ω} {m : ℕ} {L : AddSubgroup (Fin m → Ω)} {z : Fin m → Ω} :
    z ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ z ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem seqHyp_of_mod (R : Subalgebra o Ω) {r s n : ℕ}
    {W : AddSubgroup (Fin r → Ω)} {om : AddSubgroup (Fin s → Ω)}
    {i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)} {q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)} {w u P : Ω}
    (hw : w ∈ R) (hu : u ∈ R) (hP : P = w * u)
    (hWs : ∀ t ∈ R, ∀ a ∈ W, t • a ∈ W) (hos : ∀ t ∈ R, ∀ z ∈ om, t • z ∈ om)
    (h1 : ∀ a ∈ W, i a ∈ stdLat R (Fin n)) (h2 : ∀ b ∈ stdLat R (Fin n), q b ∈ om)
    (Rt : (Fin n → Ω) →ₗ[Ω] (Fin r → Ω)) (hRt : ∀ x ∈ stdLat R (Fin n), Rt x ∈ W)
    (h3 : ∀ a ∈ W, ∃ a' ∈ W, Rt (i a) = a + P • a')
    (h4 : ∀ a ∈ W, ∃ y ∈ om, q (i a) = P • y)
    (h5 : ∀ b ∈ stdLat R (Fin n), ∀ y ∈ om, q b = P • y →
      ∃ a ∈ W, ∃ x ∈ stdLat R (Fin n), b = i a + P • x)
    (h6 : ∀ z ∈ om, ∃ b ∈ stdLat R (Fin n), ∃ y ∈ om, z = q b + P • y) :
    SeqHyp R w W om i q := by
  have hstd : ∀ t ∈ R, ∀ x ∈ stdLat R (Fin n), t • x ∈ stdLat R (Fin n) := fun t ht x hx =>
    mem_std.2 fun k => by simpa using R.mul_mem ht (mem_std.1 hx k)
  refine ⟨h1, h2, ?_, fun b hb => ⟨?_, ?_⟩, ?_⟩
  · intro a ha hia
    obtain ⟨x, hx, hxe⟩ := mem_mulLat.1 hia
    obtain ⟨a', ha', e⟩ := h3 a ha
    refine mem_mulLat.2 ⟨Rt x - u • a', W.sub_mem (hRt x hx) (hWs u hu a' ha'), ?_⟩
    have e1 : w • Rt x = a + P • a' := by rw [← map_smul, hxe, e]
    rw [smul_sub, e1, hP, smul_smul]
    abel
  · intro hq
    obtain ⟨y, hy, hye⟩ := mem_mulLat.1 hq
    obtain ⟨x₁, hx₁, y', hy', e⟩ := h6 y hy
    have e1 : q (b - w • x₁) = P • (w • y') := by
      rw [map_sub, map_smul, ← hye, e, hP]
      simp only [smul_add, smul_smul, add_sub_cancel_left]
      congr 1
      ring
    obtain ⟨a, ha, x, hx, e2⟩ := h5 _ ((stdLat R _).sub_mem hb (hstd w hw _ hx₁)) _ (hos w hw _ hy') e1
    refine ⟨a, ha, mem_mulLat.2 ⟨x₁ + u • x, (stdLat R _).add_mem hx₁ (hstd u hu _ hx), ?_⟩⟩
    rw [smul_add, smul_smul, ← hP]
    rw [sub_eq_iff_eq_add] at e2
    rw [e2]
    abel
  · rintro ⟨a, ha, hx⟩
    obtain ⟨x, hx, hxe⟩ := mem_mulLat.1 hx
    obtain ⟨y, hy, e⟩ := h4 a ha
    refine mem_mulLat.2 ⟨u • y + q x, om.add_mem (hos u hu _ hy) (h2 x hx), ?_⟩
    have e1 : b = i a + w • x := by rw [hxe]; abel
    rw [e1, map_add (f := _), map_smul, e, hP, smul_add, smul_smul]
  · intro z hz
    obtain ⟨b, hb, y, hy, e⟩ := h6 z hz
    refine ⟨b, hb, mem_mulLat.2 ⟨u • y, hos u hu _ hy, ?_⟩⟩
    rw [e, hP, smul_smul]
    abel

end Abstract

section Chart

variable {o Ω Li : Type} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p Rr N : ℕ} [AddCommGroup Li] [Module Ω Li]
  (D : HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li)

theorem mem_range_iff (x : Ω) : x ∈ (algebraMap R Ω).range ↔ x ∈ R :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_lat {V : Submodule Ω Li} {e : Li} :
    e ∈ HTL.latOn D V (algebraMap R Ω 1) (algebraMap R Ω).range ↔ e ∈ V ∧ ∀ u ∈ D.om', u e ∈ R :=
  ⟨fun h => ⟨h.1, fun u hu => by simpa [mem_range_iff] using h.2 u hu⟩,
    fun h => ⟨h.1, fun u hu => by simpa [mem_range_iff] using h.2 u hu⟩⟩

variable (hc : ∀ x, c (c x) = x)
  (hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))

include hc hact

theorem form_mem (σ : E →+* Ω) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom))
    (hl : ∀ u ∈ D.om', u e ∈ R) {f : Module.Dual Ω Li} (hf : f ∈ D.omHT σ) : f e ∈ R := by
  obtain ⟨u, hu, rfl⟩ := hf
  have : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u e = u e := HTL.eigProj_apply D ρ hc hact σ he u
  change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u e ∈ R
  rw [this]
  exact hl u hu

theorem eq_zero_of_forms [CharZero Ω] [Fact p.Prime] (σ : E →+* Ω) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom))
    (h : ∀ f ∈ D.omHT σ, f e = 0) : e = 0 := by
  refine HTL.eq_zero_of_forall_om' D D.om_lat.span_eq_top fun u hu => ?_
  rw [← HTL.eigProj_apply D ρ hc hact σ he u]
  exact h _ ⟨u, hu, rfl⟩

theorem form_eq_zero (σ : E →+* Ω) {f : Module.Dual Ω Li} (hf : f ∈ D.omHT σ)
    (h : ∀ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), f e = 0) : f = 0 := by
  obtain ⟨u, hu, rfl⟩ := hf
  change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u = 0
  have hP : ∀ x : Li, eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ x ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
    intro x
    have h' := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ x
    rw [LatBasic.mem_eigSp] at h' ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h' (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  ext x
  have e1 : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u x = u (GlobalTheory.CompanionTheory.Ar.HT.eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ x) := by
    rw [HTL.eigProj_dual D ρ hact, LinearMap.comp_apply]
  have e2 := HTL.eigProj_apply D ρ hc hact σ (hP x) u
  have e3 := h _ (hP x)
  change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u _ = 0 at e3
  rw [e2] at e3
  rw [e1, e3]
  rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

open Module GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

section Refl

variable {o Ω Li : Type} [CommRing o] [Field Ω] [Algebra o Ω] {R : Subalgebra o Ω}
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p Rr N : ℕ} [AddCommGroup Li] [Module Ω Li]
  (D : HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li)
  (hc : ∀ x, c (c x) = x)
  (hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))

include hc hact

theorem exists_form [IsNoetherianRing R] [IsFractionRing R Ω] [CharZero Ω] [Fact p.Prime]
    (σ : E →+* Ω) (hproj : Module.Projective R (D.omHT σ)) {s : ℕ} (v' : Fin s → Li)
    (hv' : LinearIndependent Ω v')
    (hs : Submodule.span Ω (Set.range v') = GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom))
    (z : Fin s → Ω) (hz : ∀ l : Fin s → Ω, (∀ u ∈ D.om', u (∑ k, l k • v' k) ∈ R) → l ⬝ᵥ z ∈ R) :
    ∃ f ∈ D.omHT σ, ∀ k, f (v' k) = z k := by
  classical
  set V' := GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) with hV'
  obtain ⟨ψ, hψk⟩ : ∃ ψ : Li →ₗ[Ω] Ω, ∀ k, ψ (v' k) = z k := by
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hv').constr Ω z)
    refine ⟨g, fun k => ?_⟩
    have := congrArg (fun F => F (Basis.span hv' k)) hg
    simpa [Basis.span_apply, Basis.constr_basis, Finsupp.single_apply, ite_mul] using this
  have hψ : ∀ l : Fin s → Ω, ψ (∑ k, l k • v' k) = l ⬝ᵥ z := by
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hψk, dotProduct]
  have hψR : ∀ e ∈ V', (∀ u ∈ D.om', u e ∈ R) → ψ e ∈ R := by
    intro e he hl
    obtain ⟨l, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 (hs ▸ he)
    rw [hψ]
    exact hz l hl
  have hle : D.om' ≤ D.om := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨x, rfl⟩
      exact D.h_mem x
    · rintro _ ⟨w, hw, rfl⟩
      exact D.om.smul_mem _ hw
  haveI hfin : Module.Finite R (D.omHT σ) :=
    Module.Finite.iff_fg.2 ((Submodule.FG.of_le D.om_lat.fg hle).map _)
  haveI := hproj
  have hvec : ∀ g : Module.Dual R (D.omHT σ), ∃ e ∈ V', ∀ y : D.omHT σ,
      (y : Module.Dual Ω Li) e = algebraMap R Ω (g y) :=
    fun g => HTL.exists_vec D ρ hc hact σ g
  choose ev hev hevg using hvec
  have hevL : ∀ g, ∀ u ∈ D.om', u (ev g) ∈ R := by
    intro g u hu
    have h1 := hevg g ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u, ⟨u, hu, rfl⟩⟩
    have h2 : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u (ev g) = u (ev g) := HTL.eigProj_apply D ρ hc hact σ (hev g) u
    change GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ u (ev g) = _ at h1
    rw [← h2, h1]
    exact (g _).2
  have huniq : ∀ e e', e ∈ V' → e' ∈ V' → (∀ y : D.omHT σ, (y : Module.Dual Ω Li) e = (y : Module.Dual Ω Li) e') → e = e' := by
    intro e e' he he' h
    have := eq_zero_of_forms D ρ hc hact σ (V'.sub_mem he he') (fun f hf => by
      rw [map_sub, h ⟨f, hf⟩, sub_self])
    exact sub_eq_zero.1 this
  let Φ : Module.Dual R (D.omHT σ) →ₗ[R] R :=
    { toFun := fun g => ⟨ψ (ev g), hψR _ (hev g) (hevL g)⟩
      map_add' := fun g g' => by
        apply Subtype.ext
        have : ev (g + g') = ev g + ev g' := huniq _ _ (hev _) (V'.add_mem (hev g) (hev g')) (fun y => by
          rw [map_add (f := _), hevg, hevg, hevg, LinearMap.add_apply, map_add (f := _)])
        simp [this]
      map_smul' := fun a g => by
        apply Subtype.ext
        have : ev (a • g) = (a : Ω) • ev g := huniq _ _ (hev _) (V'.smul_mem _ (hev g)) (fun y => by
          rw [map_smul, hevg, hevg, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
          rfl)
        simp [this] }
  let f := (Module.evalEquiv R (D.omHT σ)).symm Φ
  have hf : ∀ g : Module.Dual R (D.omHT σ), g f = Φ g := fun g => by
    simpa [f] using Module.apply_evalEquiv_symm_apply (R := R) g Φ
  refine ⟨f, f.2, fun k => ?_⟩
  have key : ∀ e ∈ V', (∀ u ∈ D.om', u e ∈ R) → (f : Module.Dual Ω Li) e = ψ e := by
    intro e he hl
    let g : Module.Dual R (D.omHT σ) :=
      { toFun := fun y => ⟨(y : Module.Dual Ω Li) e, form_mem D ρ hc hact σ he hl y.2⟩
        map_add' := fun y y' => Subtype.ext (by simp)
        map_smul' := fun a y => Subtype.ext (by simp [Subalgebra.smul_def]) }
    have h1 : ev g = e := huniq _ _ (hev g) he (fun y => by rw [hevg]; rfl)
    have h2 := congrArg Subtype.val (hf g)
    change (f : Module.Dual Ω Li) e = ψ (ev g) at h2
    rw [h2, h1]
  have hloc : HTL.IsLocIn R (⊤ : Subring Ω) := by
    refine ⟨fun _ => trivial, fun b _ => ?_⟩
    obtain ⟨a, b', hb', rfl⟩ := IsFractionRing.div_surjective (A := R) b
    have h0 : algebraMap R Ω b' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'
    exact ⟨b', a, h0, trivial, mul_div_cancel₀ _ h0⟩
  obtain ⟨t, ht0, -, ht⟩ := HTL.exists_unit_smul R Ω E c hc p Rr N Li D ρ hact V' 1 ⊤ hloc (v' k)
    ⟨hs ▸ Submodule.subset_span ⟨k, rfl⟩, fun _ _ => trivial⟩
  have h3 := key _ ht.1 (fun u hu => by simpa [mem_range_iff] using ht.2 u hu)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, hψk] at h3
  exact mul_left_cancel₀ ht0 h3

end Refl

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure

open Module GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem frame {Ω Li : Type} [Field Ω] [AddCommGroup Li] [Module Ω Li] {r : ℕ} {v : Fin r → Li}
    {V : Submodule Ω Li} (hv : LinearIndependent Ω v) (hs : Submodule.span Ω (Set.range v) = V) :
    (∀ a : Fin r → Ω, ∑ k, a k • v k ∈ V) ∧ (∀ e ∈ V, ∃ a : Fin r → Ω, ∑ k, a k • v k = e) ∧
      ∀ a b : Fin r → Ω, ∑ k, a k • v k = ∑ k, b k • v k → a = b := by
  refine ⟨fun a => hs ▸ Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩),
    fun e he => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hs ▸ he), fun a b h => ?_⟩
  have := Fintype.linearIndependent_iff.1 hv (a - b) (by simp [sub_smul, Finset.sum_sub_distrib, h])
  funext k
  exact sub_eq_zero.1 (this k)

theorem seqHyp_chart : ∀ (o Ω Li : Type) [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω] (R : Subalgebra o Ω) [IsNoetherianRing R] [IsFractionRing R Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (_ : ∀ x, c (c x) = x) (p Rr N r s m : ℕ) [Fact p.Prime] [AddCommGroup Li] [Module Ω Li] (D : HT.HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li), (∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* Ω) (i₀ : Module.Dual R (D.omHT (σ.comp c.toRingHom)) →ₗ[R] (Fin N → R)), D.ExactMod σ m i₀ → D.IsDualMap σ 1 m i₀ → Module.Projective R (D.omHT σ) → ∀ (v : Fin r → Li) (v' : Fin s → Li), LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω v' → Submodule.span Ω (Set.range v') = HT.eigSp ρ (σ.comp c.toRingHom) → ∀ (W : AddSubgroup (Fin r → Ω)) (W' : AddSubgroup (Fin s → Ω)), (∀ a, a ∈ W ↔ ∀ u ∈ D.om', u (∑ k, a k • v k) ∈ R) → (∀ a, a ∈ W' ↔ ∀ u ∈ D.om', u (∑ k, a k • v' k) ∈ R) → ∀ w : Ω, w ∈ R → (∃ u ∈ R, (p : Ω) ^ m = w * u) → ∃ i : (Fin r → Ω) →ₗ[Ω] (Fin N → Ω), SeqHyp R w W (dotDual R W') i (Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k)) ∧ ∀ a ∈ W, ∀ j, ∃ z ∈ R, ∑ l, i a l * D.gram σ 1 l j = D.h (Pi.single j 1) (∑ k, a k • v k) + (p : Ω) ^ m * z := by
  intro o Ω Li _ _ _ _ R _ _ E _ _ c hc p Rr N r s m _ _ _ D ρ hact σ i₀ hex hdual hproj v v' hv hvs hv' hvs' W W'
    hW hW' w hwR hwu
  obtain ⟨u, huR, hwu⟩ := hwu
  classical
  have hσσ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  obtain ⟨J, Rr', hJ1, hJ2, hJ3⟩ := GlobalTheory.T.hodge_tate_chart_dual_action R Ω E c hc p Rr N Li D ρ hact σ 1 m i₀ (by simp) hex
  obtain ⟨hVv, hSv, hIv⟩ := frame hv hvs
  obtain ⟨hVv', hSv', hIv'⟩ := frame hv' hvs'
  have hLat : ∀ e, e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap R Ω 1) (algebraMap R Ω).range ↔
      e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ ∧ ∀ u ∈ D.om', u e ∈ R := fun e => mem_lat D
  have hWl : ∀ a, a ∈ W ↔ (∑ k, a k • v k) ∈
      HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap R Ω 1) (algebraMap R Ω).range := fun a => by
    rw [hLat, hW]
    exact ⟨fun h => ⟨hVv a, h⟩, fun h => h.2⟩
  have hE : ∀ k (x : Module.Dual Ω Li), GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ σ x (v' k) = x (v' k) := fun k x =>
    HTL.eigProj_apply D ρ hc hact σ (hvs' ▸ Submodule.subset_span ⟨k, rfl⟩) x
  have hEσ : ∀ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ, ∀ x : Module.Dual Ω Li,
      GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) x e = x e :=
    fun e he x => HTL.eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rwa [hσσ]) x
  set q := Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k) with hq
  have hqM : ∀ x : Fin N → R, D.q σ x ∈ D.omHT σ := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ⟨_, HTL.h_mem_om' D _, rfl⟩
  have hqc : ∀ (x : Fin N → R) k, D.q σ x (v' k) = q (fun n => (x n : Ω)) k := by
    intro x k
    simp [HTChart.q, hq, Fintype.linearCombination_apply, Finset.sum_apply, hE, Subalgebra.smul_def]
  have hcd : ∀ z, z ∈ dotDual R W' ↔ ∃ f ∈ D.omHT σ, ∀ k, f (v' k) = z k := by
    intro z
    constructor
    · intro hz
      exact exists_form D ρ hc hact σ hproj v' hv' hvs' z fun l hl => mem_dotDual.1 hz l ((hW' l).2 hl)
    · rintro ⟨f, hf, hfz⟩
      refine mem_dotDual.2 fun l hl => ?_
      have h1 : l ⬝ᵥ z = f (∑ k, l k • v' k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [dotProduct, map_sum, hfz, mul_comm]
      rw [h1]
      exact form_mem D ρ hc hact σ (hVv' l) ((hW' l).1 hl) hf
  have hci : ∀ f ∈ D.omHT σ, ∀ f' ∈ D.omHT σ, (∀ k, f (v' k) = f' (v' k)) → f = f' := by
    intro f hf f' hf' h
    refine sub_eq_zero.1 (form_eq_zero D ρ hc hact σ ((D.omHT σ).sub_mem hf hf') fun e he => ?_)
    obtain ⟨a, rfl⟩ := hSv' e he
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, h]
  have hlift : ∀ b ∈ stdLat R (Fin N), ∃ b₀ : Fin N → R, (fun n => (b₀ n : Ω)) = b :=
    fun b hb => ⟨fun n => ⟨b n, mem_std.1 hb n⟩, rfl⟩
  let Lv := Fintype.linearCombination Ω v
  have hLv : ∀ a, Lv a = ∑ k, a k • v k := fun a => Fintype.linearCombination_apply Ω v a
  have hWs : ∀ t ∈ R, ∀ a ∈ W, t • a ∈ W := by
    intro t ht a ha
    refine (hW _).2 fun u' hu' => ?_
    have : ∑ k, (t • a) k • v k = t • ∑ k, a k • v k := by
      simp [Finset.smul_sum, smul_smul]
    rw [this, map_smul, smul_eq_mul]
    exact R.mul_mem ht ((hW a).1 ha u' hu')
  have hos : ∀ t ∈ R, ∀ z ∈ dotDual R W', t • z ∈ dotDual R W' := fun t ht z hz =>
    mem_dotDual.2 fun l hl => by
      rw [dotProduct_smul, smul_eq_mul]
      exact R.mul_mem ht (mem_dotDual.1 hz l hl)
  have hJf : ∀ a ∈ W, ∃ f : Module.Dual R (D.omHT (σ.comp c.toRingHom)),
      (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap R Ω (f z) = (z : Module.Dual Ω Li) (∑ k, a k • v k)) ∧
        ∀ l, J (Lv a) l = algebraMap R Ω (i₀ f l) := by
    intro a ha
    obtain ⟨f, hf1, hf2⟩ := hJ1 _ ((hWl a).1 ha)
    exact ⟨f, fun z => by rw [hf1 z, map_one, _root_.one_mul], fun l => by rw [hLv]; exact hf2 l⟩
  have h1 : ∀ a ∈ W, (J ∘ₗ Lv) a ∈ stdLat R (Fin N) := by
    intro a ha
    obtain ⟨f, -, hf⟩ := hJf a ha
    exact mem_std.2 fun l => by rw [LinearMap.comp_apply, hf l]; exact (i₀ f l).2
  have hqd : ∀ x : Fin N → R, q (fun n => (x n : Ω)) ∈ dotDual R W' := fun x =>
    (hcd _).2 ⟨_, hqM x, fun k => hqc x k⟩
  have h2 : ∀ b ∈ stdLat R (Fin N), q b ∈ dotDual R W' := by
    intro b hb
    obtain ⟨b₀, rfl⟩ := hlift b hb
    exact hqd b₀
  have hak : ∀ n : Fin N, ∃ a ∈ W, Lv a = Rr' (Pi.single n 1) := by
    intro n
    have h := (hLat _).1 (hJ2 n)
    obtain ⟨a, ha⟩ := hSv _ h.1
    refine ⟨a, (hWl a).2 ?_, by rw [hLv, ha]⟩
    rw [ha]
    exact hJ2 n
  choose ak hakW hakL using hak
  let Rt : (Fin N → Ω) →ₗ[Ω] (Fin r → Ω) := Fintype.linearCombination Ω ak
  have hRtL : ∀ x, Lv (Rt x) = Rr' x := by
    intro x
    have hx : x = ∑ n, x n • Pi.single n (1 : Ω) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Rt, Fintype.linearCombination_apply, map_sum, map_smul, hakL]
  have hRt : ∀ x ∈ stdLat R (Fin N), Rt x ∈ W := by
    intro x hx
    simp only [Rt, Fintype.linearCombination_apply]
    exact W.sum_mem fun n _ => hWs _ (mem_std.1 hx n) _ (hakW n)
  have h3 : ∀ a ∈ W, ∃ a' ∈ W, Rt ((J ∘ₗ Lv) a) = a + (p : Ω) ^ m • a' := by
    intro a ha
    obtain ⟨e', he', h⟩ := hJ3 _ ((hWl a).1 ha)
    obtain ⟨a', ha'⟩ := hSv _ ((hLat _).1 he').1
    refine ⟨a', (hWl a').2 (by rw [ha']; exact he'), hIv _ _ ?_⟩
    have e1 : Lv (Rt ((J ∘ₗ Lv) a)) = Lv (a + (p : Ω) ^ m • a') := by
      rw [hRtL, LinearMap.comp_apply, hLv a, h, map_add (f := _), map_smul, hLv, hLv, ha']
    rwa [hLv, hLv] at e1
  have h4 : ∀ a ∈ W, ∃ y ∈ dotDual R W', q ((J ∘ₗ Lv) a) = (p : Ω) ^ m • y := by
    intro a ha
    obtain ⟨f, -, hf⟩ := hJf a ha
    obtain ⟨y, hyM, hy⟩ := (hex.2.1 (i₀ f)).2 ⟨f, 0, by simp⟩
    refine ⟨fun k => y (v' k), (hcd _).2 ⟨y, hyM, fun _ => rfl⟩, ?_⟩
    have e1 : (J ∘ₗ Lv) a = fun n => ((i₀ f n : R) : Ω) := funext fun n => hf n
    rw [e1]
    funext k
    rw [← hqc (i₀ f) k, hy]
    simp [Subalgebra.smul_def]
  have h5 : ∀ b ∈ stdLat R (Fin N), ∀ y ∈ dotDual R W', q b = (p : Ω) ^ m • y →
      ∃ a ∈ W, ∃ x ∈ stdLat R (Fin N), b = (J ∘ₗ Lv) a + (p : Ω) ^ m • x := by
    intro b hb y hy hqy
    obtain ⟨b₀, rfl⟩ := hlift b hb
    obtain ⟨f, hfM, hfy⟩ := (hcd y).1 hy
    have e1 : D.q σ b₀ = ((p : R) ^ m) • f := hci _ (hqM b₀) _ ((D.omHT σ).smul_mem _ hfM) fun k => by
      rw [hqc, hqy]
      simp [Subalgebra.smul_def, hfy]
    obtain ⟨g, x', hgx⟩ := (hex.2.1 b₀).1 ⟨f, hfM, e1⟩
    obtain ⟨e, he, hge⟩ := HTL.exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hσσ] at he
    have heL : e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap R Ω 1) (algebraMap R Ω).range := by
      refine (hLat e).2 ⟨he, fun u hu => ?_⟩
      have h' : GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) u e =
          algebraMap R Ω (g ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) u, ⟨u, hu, rfl⟩⟩) :=
        hge ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) u, ⟨u, hu, rfl⟩⟩
      rw [← hEσ e he u, h']
      exact (g _).2
    obtain ⟨a, rfl⟩ := hSv e he
    have ha : a ∈ W := (hWl a).2 heL
    obtain ⟨f₁, hf₁, hJf₁⟩ := hJf a ha
    have hfg : f₁ = g := LinearMap.ext fun z => Subtype.ext ((hf₁ z).trans (hge z))
    refine ⟨a, ha, fun n => (x' n : Ω), mem_std.2 fun n => (x' n).2, ?_⟩
    funext n
    have h6 := congrArg (fun x : R => (x : Ω)) (congrFun hgx n)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h6
    rw [Pi.add_apply, LinearMap.comp_apply, hJf₁ n, hfg]
    rw [h6]
    simp
  have h6 : ∀ z ∈ dotDual R W', ∃ b ∈ stdLat R (Fin N), ∃ y ∈ dotDual R W', z = q b + (p : Ω) ^ m • y := by
    intro z hz
    obtain ⟨f, hfM, hfz⟩ := (hcd z).1 hz
    obtain ⟨x, y', hy', e⟩ := hex.2.2 f hfM
    refine ⟨fun n => (x n : Ω), mem_std.2 fun n => (x n).2, fun k => y' (v' k),
      (hcd _).2 ⟨y', hy', fun _ => rfl⟩, ?_⟩
    funext k
    rw [← hfz k, e, LinearMap.add_apply, hqc]
    simp [Subalgebra.smul_def]
  refine ⟨J ∘ₗ Lv, seqHyp_of_mod R hwR huR hwu hWs hos h1 h2 Rt hRt h3 h4 h5 h6, ?_⟩
  intro a ha j
  obtain ⟨f, hf1, hf2⟩ := hJf a ha
  let y : D.omHT (σ.comp c.toRingHom) :=
    ⟨GlobalTheory.CompanionTheory.Ar.HT.eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single j 1)), ⟨_, HTL.h_mem_om' D _, rfl⟩⟩
  obtain ⟨z, hz⟩ := hdual f j y rfl
  refine ⟨(z : Ω), z.2, ?_⟩
  have e1 : algebraMap R Ω (f y) = D.h (Pi.single j 1) (∑ k, a k • v k) := by
    rw [hf1 y]
    exact hEσ _ (hVv a) _
  simp only [LinearMap.comp_apply, hf2]
  rw [hz, map_add (f := _), e1, map_mul, map_pow, map_natCast]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBoundStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_chart_exists_seqHyp_gram_congr_mod_pow : ∀ (o Ω Li : Type) [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω] (R : Subalgebra o Ω) [IsNoetherianRing R] [IsFractionRing R Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (_ : ∀ x, c (c x) = x) (p Rr N r s m : ℕ) [Fact p.Prime] [AddCommGroup Li] [Module Ω Li] (D : HT.HTChart R Ω c p Rr N (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li), (∀ (a : 𝓞 E) (w : Module.Dual Ω Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* Ω) (i₀ : Module.Dual R (D.omHT (σ.comp c.toRingHom)) →ₗ[R] (Fin N → R)), D.ExactMod σ m i₀ → D.IsDualMap σ 1 m i₀ → Module.Projective R (D.omHT σ) → ∀ (v : Fin r → Li) (v' : Fin s → Li), LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω v' → Submodule.span Ω (Set.range v') = HT.eigSp ρ (σ.comp c.toRingHom) → ∀ (W : AddSubgroup (Fin r → Ω)) (W' : AddSubgroup (Fin s → Ω)), (∀ a, a ∈ W ↔ ∀ u ∈ D.om', u (∑ k, a k • v k) ∈ R) → (∀ a, a ∈ W' ↔ ∀ u ∈ D.om', u (∑ k, a k • v' k) ∈ R) → ∀ w : Ω, w ∈ R → (∃ u ∈ R, (p : Ω) ^ m = w * u) → ∃ i : (Fin r → Ω) →ₗ[Ω] (Fin N → Ω), SeqHyp R w W (dotDual R W') i (Fintype.linearCombination Ω fun (n : Fin N) (k : Fin s) => D.h (Pi.single n 1) (v' k)) ∧ ∀ a ∈ W, ∀ j, ∃ z ∈ R, ∑ l, i a l * D.gram σ 1 l j = D.h (Pi.single j 1) (∑ k, a k • v k) + (p : Ω) ^ m * z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeRelay
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_model_prime_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), P.Dh.HasTestPoints (algebraMap O (CR O y c') w) := by
  first | exact @PositivityTheory.Xgn.sequence_test_function | exact PositivityTheory.Xgn.sequence_test_function
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeRelayStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_model_prime_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), P.Dh.HasTestPoints (algebraMap O (CR O y c') w) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_model_prime_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_model_prime_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_model_prime_relay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeHeight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeHeight
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li)) := by
  first | exact @PositivityTheory.Xgn.sequence_localization_exists | exact PositivityTheory.Xgn.sequence_localization_exists
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeHeightStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_height | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_height | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_height <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeValue
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chart_om_eigQuot_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), IsNoetherianRing (CR O y c') → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → Module.Projective (CR O y c') P.Dh.om' ∧ ∀ t : CMType H ⊕ CMType H, ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) → Module.Projective (CR O y c') (P.Dh.omHT σ) :=
  @PositivityTheory.Xgn.sequence_projection_exists

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeValueStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), IsNoetherianRing (CR O y c') → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → Module.Projective (CR O y c') P.Dh.om' ∧ ∀ t : CMType H ⊕ CMType H, ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) → Module.Projective (CR O y c') (P.Dh.omHT σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_om_eigQuot_projective | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_om_eigQuot_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_om_eigQuot_projective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeDegree
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff

theorem embedding_integers_and_different_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 :=
  @PositivityTheory.Xgn.sequence_differentials_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeDegreeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) ∧ ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff.embedding_integers_and_different_unit | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff.embedding_integers_and_different_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff.embedding_integers_and_different_unit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeRelay
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) ∧ ∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω) := by
  first | exact @PositivityTheory.Xgn.sequence_ring_exists | exact PositivityTheory.Xgn.sequence_ring_exists
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeRelayStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) ∧ ∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeCount
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeCount
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem mem_coordLat_iff_forall_om_mem_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' :=
  PositivityTheory.Xgn.sequence_coordinates_exist

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeHodgeCountStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.mem_coordLat_iff_forall_om_mem_chartRing | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.mem_coordLat_iff_forall_om_mem_chartRing | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.mem_coordLat_iff_forall_om_mem_chartRing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmEmbeddingConjugateCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmEmbeddingConjugateCompat
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab

theorem exists_labelEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 t
  have uniq : ∀ f g : E →+* Ω, (∀ a : 𝓞 E, f (a : E) = g (a : E)) → f = g := by
    intro f g h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    exact h a
  rcases t with τ | τ
  · let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F (c.conj τ.1))
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
    rw [H.bar_eq a]
  · let σ : E →+* Ω :=
      𝔐.cst.comp ((τ.1.codRestrict c.F (c.conj τ.1)).comp (GlobalTheory.CompanionTheory.Ar.HT.cmConj E).toRingHom)
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inr τ) a := by
      intro a
      change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
        𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
      rw [H.bar_eq a]
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1)
        (NumberField.IsCMField.complexConj E (NumberField.IsCMField.complexConj E (a : E)))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (a : E))
    rw [NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmEmbeddingConjugateCompatStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_embedding_conjugate_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab.exists_labelEmbedding | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab.exists_labelEmbedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab.exists_labelEmbedding <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeDegree
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq

theorem isCp_dvd_sq (Ω : Type) [Field Ω] (A : Subring Ω) (p : ℕ) [hp : Fact p.Prime] (κ : Ω) (hκA : κ ∈ A)
    (hκ : HT.IsCp p κ) : ∃ u ∈ A, (p : Ω) ^ 2 = κ * u := by
  unfold HT.IsCp at hκ
  split_ifs at hκ with h2
  · exact ⟨1, A.one_mem, by rw [hκ, h2]; norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    have hζA : ζ ∈ A := by simpa using A.add_mem hκA A.one_mem
    have hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0 := hζ.geom_sum_eq_zero hp.out.one_lt
    have hp' : (p : Ω) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    have hterm : ∀ i, (1 : Ω) - ζ ^ i = (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := fun i => by
      rw [mul_comm, geom_sum_mul_neg]
    have hv : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ∈ A :=
      A.sum_mem fun i _ => A.sum_mem fun j _ => A.pow_mem hζA j
    have hpv : (p : Ω) = -(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
      rw [hp', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm]
      ring
    refine ⟨-(p : Ω) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j,
      A.mul_mem (A.neg_mem (natCast_mem A p)) hv, ?_⟩
    calc (p : Ω) ^ 2 = p * p := sq _
      _ = p * (-(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) := by rw [← hpv]
      _ = _ := by ring

theorem generatesDiff_one {O Ω E : Type} [CommRing O] [Field Ω] [Algebra O Ω] [Field E] [NumberField E]
    (R : Subalgebra O Ω) (σ : E →+* Ω) (h1 : ∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E))
    (h2 : ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1) :
    HT.GeneratesDiff σ (1 : R) := by
  have hmem : ∀ a : 𝓞 E, σ (a : E) ∈ R := fun a => by
    obtain ⟨o, ho⟩ := h1 a
    rw [← ho]
    exact R.algebraMap_mem o
  obtain ⟨x, hx, o, ho⟩ := h2
  unfold HT.GeneratesDiff
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, map_one]
    have : (1 : Ω) = (algebraMap O R o) • σ (x : E) := by
      rw [← ho]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨z, -, rfl⟩
    have : σ (z : E) = (⟨σ (z : E), hmem z⟩ : R) • algebraMap R Ω 1 := by
      rw [map_one]; exact (_root_.mul_one _).symm
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem seq_holds : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (t : CMType H ⊕ CMType H), ∃ i : (Fin (labelRk D t) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p t) (b t) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p t.swap) (b t.swap) c')) i (qMap P (b t.swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb t a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p t) (b t) c') (b t) i := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hA hpq p _ hpS hfree hp2 hdisc b hb A _ _ _ m _ hpm O _ _ _
    _ _ _ _ w hw G c' hc' P t
  obtain ⟨hchar, hN, hI, hFr, hreg, hpt⟩ := GlobalTheory.T.arith_variety_prime_hodge_relay E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS A m hpm O c' hc'
  haveI := hchar
  haveI := hN
  haveI := hI
  haveI := hFr
  have hc : ∀ x, HT.cmConj E (HT.cmConj E x) = x := fun x => by simp [HT.cmConj]
  obtain ⟨σ, hσ, hσ', huniq⟩ := GlobalTheory.T.cm_embedding_conjugate_compat E H D l Xo c O₀ β Y S Ω K J y 𝔐 t
  have hd := GlobalTheory.T.arith_variety_prime_hodge_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hdisc A m hpm O
  have hgd : ∀ τ : E →+* Ω, HT.GeneratesDiff τ (1 : CR O y c') := fun τ =>
    generatesDiff_one _ τ (hd τ).1 (hd τ).2
  have hloc := GlobalTheory.T.arith_variety_prime_hodge_height E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS A m hpm O G c' hc' P
  obtain ⟨hpO, hpH⟩ := GlobalTheory.T.arith_variety_prime_hodge_value E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hfree hdisc A m hpm O G c' hc' P hN hpt hloc
  have htest := GlobalTheory.T.arith_variety_model_prime_relay hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hp2 A m hpm O w hw G c' hc' P
  have hR := 𝔐.R_ge p hpS
  obtain ⟨n, hn⟩ : ∃ n, 𝔐.R p = (n + 2) + 2 := ⟨𝔐.R p - 4, by omega⟩
  have hm : 𝔐.R p - 2 = n + 2 := by omega
  obtain ⟨u, huR, hu⟩ := isCp_dvd_sq Ω (CR O y c').toSubring p (algebraMap O Ω w)
    ((CR O y c').algebraMap_mem w) hw
  have hdiv : algebraMap O (CR O y c') w * (p : CR O y c') ^ (𝔐.R p - 2) ∣ (p : CR O y c') ^ (𝔐.R p) := by
    refine ⟨⟨u, huR⟩, Subtype.ext ?_⟩
    rw [hm, hn]
    push_cast
    rw [pow_add (p : Ω) (n + 2) 2, hu]
    ring
  obtain ⟨-, hseq⟩ := GlobalTheory.T.chart_sequence_holds (CR O y c') Ω E (HT.cmConj E) hc p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) P.Dh
    (algebraMap O (CR O y c') w) (𝔐.R p - 2) hdiv htest hpO
  obtain ⟨i₀, hDm, hEx⟩ := hseq σ 1 1 (hgd σ) (hgd _) (hpH t σ hσ) (hpH t.swap _ hσ')
  have hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), P.Dh.ρΩ a w = w ∘ₗ 𝔐.ρ (RingOfIntegers.mapRingEquiv (HT.cmConj E) a) :=
    fun a w => by
      rw [HT.ModelTest.bar_eq H a]
      exact P.Dh_act a w
  have hV : ∀ (s : CMType H ⊕ CMType H) (τ : E →+* Ω), (∀ a : 𝓞 E, τ (a : E) = 𝔐.emb s a) →
      Submodule.span Ω (Set.range (b s)) = HT.eigSp 𝔐.ρ τ := by
    intro s τ hτ
    rw [(hb s).2]
    unfold HodgeCpt.Vgen GlobalTheory.CompanionTheory.Ar.eigSp HT.eigSp
    refine iInf_congr fun a => ?_
    rw [hτ a]
    rfl
  have hcoord := fun (s : CMType H ⊕ CMType H) (τ : E →+* Ω) (hτ : ∀ a : 𝓞 E, τ (a : E) = 𝔐.emb s a) =>
    GlobalTheory.T.arith_variety_prime_hodge_count E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS b hb A m hpm O G c' hc' P s
      (fun a => by rw [← hτ a]; exact (hd τ).1 a)
      (by
        obtain ⟨x, hx, o, ho⟩ := (hd τ).2
        exact ⟨x, hx, o, by rw [← hτ x]; exact ho⟩) hreg hpt hloc
  have hwu : ∃ v ∈ CR O y c', (p : Ω) ^ (𝔐.R p - 2) = algebraMap O Ω w * v := by
    refine ⟨u * (p : Ω) ^ n, (CR O y c').mul_mem huR ((CR O y c').pow_mem (natCast_mem _ p) n), ?_⟩
    rw [hm, pow_add, mul_comm ((p : Ω) ^ n), hu]
    ring
  obtain ⟨i, h1, h2⟩ := GlobalTheory.T.hodge_chart_exists_seqHyp_gram_congr_mod_pow O Ω 𝔐.Li (CR O y c') E (HT.cmConj E) hc p (𝔐.R p) (D.p + D.q) _ _ (𝔐.R p - 2) P.Dh 𝔐.ρ hact σ
    i₀ hEx hDm (hpH t σ hσ) (b t) (b t.swap) (hb t).1 (hV t σ hσ) (hb t.swap).1 (hV t.swap _ hσ') _ _
    (hcoord t σ hσ) (hcoord t.swap _ hσ') (algebraMap O Ω w) ((CR O y c').algebraMap_mem w) hwu
  refine ⟨i, h1, fun σE hσE a ha j => ?_⟩
  rw [huniq σE hσE]
  exact h2 a ha j

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeDegreeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_model_prime_degree : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (t : CMType H ⊕ CMType H), ∃ i : (Fin (labelRk D t) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p t) (b t) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p t.swap) (b t.swap) c')) i (qMap P (b t.swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb t a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p t) (b t) c') (b t) i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq.seq_holds | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq.seq_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq.seq_holds <;> assumption)
end
