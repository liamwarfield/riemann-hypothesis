module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGermEigen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGermEigen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame

section Abstract

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {E : Type} [Field E] [NumberField E]
  {A : Subring K}

theorem mem_of_isFreeOn {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) (i : Fin N) : t i ∈ L := by
  have e : t i = ρ 1 (t i) := by simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h.2.2, e, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _

theorem exists_lift_basis {R Y : Type} [CommRing R] [AddCommGroup Y] [Module R Y] (f : R →+* K)
    (hf : Function.Injective f) (hA : ∀ a, a ∈ A ↔ ∃ c, f c = a) (Φ : Y →+ V)
    (hsmul : ∀ (c : R) y, Φ (c • y) = f c • Φ y) (hinj : Function.Injective Φ)
    {ρ : 𝓞 E →+* Module.End K V} {L : Submodule A V} (hrange : ∀ v, v ∈ L ↔ ∃ y, Φ y = v)
    (rB : 𝓞 E → Y → Y) (hact : ∀ a y, Φ (rB a y) = ρ a (Φ y)) {N : ℕ} {t : Fin N → V}
    (h : HT.IsFreeOn ρ L t) :
    ∃ x : Fin N → Y, (∀ j, Φ (x j) = t j) ∧
      LinearIndependent R (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) ∧
      Submodule.span R (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        rB (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ := by
  choose x hx using fun i => (hrange (t i)).1 (mem_of_isFreeOn h i)
  have hΦ : ∀ c : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R,
      Φ (∑ q, c q • rB (RingOfIntegers.basis E q.2) (x q.1)) =
        ∑ q, f (c q) • ρ (RingOfIntegers.basis E q.2) (t q.1) := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hsmul, hact, hx]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := Fintype.linearIndependent_iff.1 h.1 (fun q => f (c q)) (by rw [← hΦ, hc, map_zero])
    exact hf ((h1 q).trans (map_zero f).symm)
  · rw [eq_top_iff]
    rintro y -
    have hy : Φ y ∈ L := (hrange _).2 ⟨y, rfl⟩
    rw [h.2.2] at hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hy
    choose c' hc' using fun q => (hA (c q : K)).1 (c q).2
    have e : y = ∑ q, c' q • rB (RingOfIntegers.basis E q.2) (x q.1) := hinj (by
      rw [hΦ, ← hc]
      exact Finset.sum_congr rfl fun q _ => by rw [hc']; rfl)
    rw [e]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end Abstract

theorem exists_of_mem_stdLat {Ω : Type} [Field Ω] {A : Subring Ω} {d : ℕ}
    {T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)} {w : (Fin d → Ω) × (Fin d → Ω)}
    (h : w ∈ stdLat A T) : ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ w = T y₀ := by
  induction h using Submodule.span_induction with
  | mem w hw => exact hw
  | zero => exact ⟨0, fun i => ⟨A.zero_mem, A.zero_mem⟩, (map_zero T).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, hy, rfl⟩ := ha
    obtain ⟨z, hz, rfl⟩ := hb
    exact ⟨y + z, fun i => ⟨A.add_mem (hy i).1 (hz i).1, A.add_mem (hy i).2 (hz i).2⟩, (map_add T y z).symm⟩
  | smul c a _ ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨(c : Ω) • y, fun i => ⟨A.mul_mem c.2 (hy i).1, A.mul_mem c.2 (hy i).2⟩, (map_smul T (c : Ω) y).symm⟩

theorem toVec_injective (Ω : Type) [Field Ω] (d : ℕ) : Function.Injective (toVec Ω d) := by
  intro y y' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 ((dotProductEquiv Ω (Fin d)).injective h2)

theorem toVec_surjective (Ω : Type) [Field Ω] (d : ℕ) : Function.Surjective (toVec Ω d) := by
  rintro ⟨a, φ⟩
  obtain ⟨b, rfl⟩ := (dotProductEquiv Ω (Fin d)).surjective φ
  exact ⟨(a, b), rfl⟩

section Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω] {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d r : ℕ}
  {M : LieModel t.G ξ (Fin d → Ω)} {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)}

theorem vmap_injective {R S : Type} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (vmap (d := d) f) := fun _ _ h =>
  Prod.ext (funext fun i => hf (congrFun (congrArg Prod.fst h) i))
    (funext fun i => hf (congrFun (congrArg Prod.snd h) i))

theorem toH_injective (hξ : IsCptGen ξ) (S : GermSys t ξ M) (p : Cpt ξ) : Function.Injective (toH S p) :=
  fun _ _ h => vmap_injective (hξ.inj p)
    ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.1.1 (toVec_injective Ω d h))

theorem toH_mem_iff (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ)
    (v : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) : v ∈ 𝓗.HL p ↔ ∃ y, toH S p y = v := by
  constructor
  · intro hv
    obtain ⟨w, rfl⟩ := toVec_surjective Ω d v
    obtain ⟨y₀, hy₀, rfl⟩ := exists_of_mem_stdLat ((hG.2 p w).1 hv)
    choose a ha using fun i => (hy₀ i).1
    choose b hb using fun i => (hy₀ i).2
    refine ⟨(a, b), ?_⟩
    have e : vmap (genMap ξ p) (a, b) = y₀ := Prod.ext (funext ha) (funext hb)
    rw [toH, e]
  · rintro ⟨y, rfl⟩
    exact (hG.2 p _).2 (Submodule.subset_span ⟨vmap (genMap ξ p) y,
      fun i => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩)

theorem toH_rhoH (S : GermSys t ξ M) {𝓗 : HodgeLat M.lat ρ H.bar r} (hG : S.Gives 𝓗) (p : Cpt ξ) (a : 𝓞 E)
    (y : (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) :
    toH S p (rhoH (S.g p).B a y) = 𝓗.ρH a (toH S p y) := by
  have h1 := vmap_rhoH (S.mapK p) a y
  have h2 := LinearMap.congr_fun ((GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (S.iso p)).2.2.2.2.1 a) (vmap (genMap ξ p) y)
  have h3 := hG.1 a (transH (S.φ p) (S.ψ p) (S.lam p) (vmap (genMap ξ p) y))
  have e1 := congrArg (fun z => toVec Ω d (transH (S.φ p) (S.ψ p) (S.lam p) z)) h1
  have e2 := congrArg (toVec Ω d) h2.symm
  exact (e1.trans e2).trans h3.symm

end Germ

theorem exists_basis_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  intro E _ _ _ H _ X t Ω _ _ ξ d r M S ρ 𝓗 σ u hξ hG hσ _ hu p
  obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
  have hfree := hx p hU
  obtain ⟨x', h1, h2, h3⟩ := exists_lift_basis (genMap ξ p) (hξ.inj p) (A := regAt ξ p) (fun _ => Iff.rfl)
    (AddMonoidHom.mk' (toH S p) (toH_add S p)) (toH_smul S p) (toH_injective hξ S p)
    (toH_mem_iff S hG p) (fun a y => rhoH (S.g p).B a y) (toH_rhoH S hG p) hfree
  have hA : ∀ i, ∃ c : Fin r → Ω, ∑ l, c l • u l = HT.eigProj 𝓗.ρH σ (x i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hu ▸ HT.LatBasic.eigProj_mem _ _ _)
  choose A hA using hA
  refine ⟨x', Matrix.of A, ⟨h2, h3⟩, ?_, fun j => ?_⟩
  · have e : (fun j => ∑ l, Matrix.of A j l • u l) = fun j => HT.eigProj 𝓗.ρH σ (x j) := funext hA
    rw [e]
    exact ⟨HodgeDeterminantLattice.linearIndependent_eigProj σ hfree,
      HodgeDeterminantLattice.eigQuot_eq_span σ hfree fun a => ⟨⟨_, hσ p a⟩, rfl⟩⟩
  · have := h1 j
    change toH S p (x' j) = x j at this
    rw [this]
    exact (hA j).symm

end GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGermEigenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_germ_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpEmbeddingFactorsThroughComplex
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpEmbeddingFactorsThroughComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_emb_through_coeff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : Nat.Primes)
    (κ : c.F →+* ℂ_[p]) (s : E →+* ℂ_[p]), ∃ τ : E →+* ℂ, s = κ.comp (inE c τ) := by
  intro E _ _ _ H l c p κ s
  haveI : CharZero ℂ_[p] := charZero_of_injective_ringHom κ.injective
  have hinj : Function.Injective (fun τ : E →+* ℂ => κ.comp (inE c τ)) := by
    intro τ τ' h
    ext a
    have h1 : κ (inE c τ a) = κ (inE c τ' a) := RingHom.congr_fun h a
    have h2 := κ.injective h1
    exact congrArg (fun x : c.F => (x : ℂ)) h2
  have hle : Nat.card (E →+* ℂ_[p]) ≤ Nat.card (E →+* ℂ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ,
      NumberField.Embeddings.card E ℂ_[p]]
  haveI : Finite (E →+* ℂ_[p]) := inferInstance
  obtain ⟨τ, hτ⟩ := (hinj.bijective_of_nat_card_le hle).2 s
  exact ⟨τ, hτ.symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpEmbeddingFactorsThroughComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cp_embedding_factors_through_complex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : Nat.Primes)
    (κ : c.F →+* ℂ_[p]) (s : E →+* ℂ_[p]), ∃ τ : E →+* ℂ, s = κ.comp (inE c τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_emb_through_coeff | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_emb_through_coeff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_emb_through_coeff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj

theorem ev_eigProj : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (h : HL) (hp : HT.eigProj ρH σ (h : Vs × Module.Dual Ω Vs) ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    ev ⟨_, hp⟩ = HT.eigProj ρHC σC (ev h) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g ℓ ψ ρH ρHC HL ev σ σC h hp hev htie hst
  choose hc hψ using htie
  have hsum : (⟨_, hp⟩ : HL) = ∑ k, (⟨σ (HT.dualInt E k), hc _⟩ : R') •
      (⟨ρH (RingOfIntegers.basis E k) (h : Vs × Module.Dual Ω Vs), hst _ _ h.2⟩ : HL) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, hψ, hev.1 _ h]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_eval_eigProj_comm : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (h : HL) (hp : HT.eigProj ρH σ (h : Vs × Module.Dual Ω Vs) ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    ev ⟨_, hp⟩ = HT.eigProj ρHC σC (ev h) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj.ev_eigProj | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj.ev_eigProj | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj.ev_eigProj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasisSpansEigenspace
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasisSpansEigenspace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem adaptedFamily_isBasis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W)
    (u : Fin (p + q) → W × Module.Dual K W),
    IsAdapted ρH σ v w u → LinearIndependent K v → Module.finrank K (HT.eigSp ρH σ) = p + q →
    FiniteDimensional K (HT.eigSp ρH σ) →
    LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  intro E _ _ K W _ _ _ ρH σ p q v w u hA hv hrank hfd
  obtain ⟨hmem, hfst, hsnd⟩ := hA
  have hz : ∀ j : Fin q, (u (Fin.natAdd p j)).1 = 0 := fun j => (hsnd j).1
  have hli : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∑ i, g i • (u i).1 = 0 := by
      have := congrArg Prod.fst hg
      simpa [Prod.fst_sum] using this
    have h2 : ∑ i, g i • (u i).2 = 0 := by
      have := congrArg Prod.snd hg
      simpa [Prod.snd_sum] using this
    rw [Fin.sum_univ_add] at h1 h2
    have h1' : ∑ i : Fin p, g (Fin.castAdd q i) • v i = 0 := by
      simpa [hfst, hz] using h1
    have hcast : ∀ i : Fin p, g (Fin.castAdd q i) = 0 :=
      (Fintype.linearIndependent_iff.mp hv) _ h1'
    have h2' : ∑ j : Fin q, g (Fin.natAdd p j) • (u (Fin.natAdd p j)).2 = 0 := by
      simpa [hcast] using h2
    have hnat : ∀ j' : Fin q, g (Fin.natAdd p j') = 0 := by
      intro j'
      have h3 := congrArg (fun f : Module.Dual K W => f (w j')) h2'
      simpa [LinearMap.sum_apply, (hsnd _).2 j'] using h3
    intro i
    induction i using Fin.addCases with
    | left i => exact hcast i
    | right j => exact hnat j
  refine ⟨hli, ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · rw [finrank_span_eq_card hli, Fintype.card_fin, hrank]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasisSpansEigenspaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_basis_spans_eigenspace : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W)
    (u : Fin (p + q) → W × Module.Dual K W),
    IsAdapted ρH σ v w u → LinearIndependent K v → Module.finrank K (HT.eigSp ρH σ) = p + q →
    FiniteDimensional K (HT.eigSp ρH σ) →
    LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.adaptedFamily_isBasis | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.adaptedFamily_isBasis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.adaptedFamily_isBasis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenbasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenbasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isAdapted_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g p q : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
    (x₁ : Fin p → Fin g → R') (x₂ : Fin q → Fin g → R') (hu : ∀ i, u i ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    IsAdapted ρH σ b₁ b₂ u → (∀ i, b₁ i = comb ℓ (x₁ i)) → (∀ i, b₂ i = comb ℓ (x₂ i)) →
    IsAdapted ρHC σC (fun i k => ψ (x₁ i k)) (fun i k => ψ (x₂ i k)) (fun i => ev ⟨u i, hu i⟩) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g p q ℓ ψ ρH ρHC HL ev σ σC b₁ b₂ u x₁ x₂ hu hE hσ hcl hA hb₁ hb₂
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IsEval at hE
  unfold GlobalTheory.CompanionTheory.Ar.Flat.IsAdapted at hA ⊢
  obtain ⟨hE1, hE2, hE3⟩ := hE
  obtain ⟨hA1, hA2, hA3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro i
    show ev ⟨u i, hu i⟩ ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρHC σC
    have hui := hA1 i
    rw [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf] at hui ⊢
    intro a
    have h1 := hui a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change ρH a (u i) = σ (a : E) • u i at h1
    show ρHC a (ev ⟨u i, hu i⟩) = σC (a : E) • ev ⟨u i, hu i⟩
    obtain ⟨hσa, hψ⟩ := hσ (a : E)
    have hmem : ρH a (u i) ∈ HL := hcl a (u i) (hu i)
    have e1 : ev ⟨ρH a (u i), hmem⟩ = ρHC a (ev ⟨u i, hu i⟩) := hE1 a ⟨u i, hu i⟩ hmem
    have e2 : (⟨ρH a (u i), hmem⟩ : HL) = (⟨σ a, hσa⟩ : R') • (⟨u i, hu i⟩ : HL) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subring.smul_def]
      exact h1
    rw [← e1, e2, map_smulₛₗ, hψ]
  · intro i
    exact hE2 ⟨u (Fin.castAdd q i), hu _⟩ (x₁ i) ((hA2 i).trans (hb₁ i))
  · intro j
    obtain ⟨hj1, hj2⟩ := hA3 j
    constructor
    · have hc : (u (Fin.natAdd p j)).1 = comb ℓ (fun _ => (0 : R')) := by
        rw [hj1]
        simp [GlobalTheory.CompanionTheory.Ar.Flat.CPoint.comb]
      have h3 := hE2 ⟨u (Fin.natAdd p j), hu _⟩ (fun _ => 0) hc
      refine h3.trans ?_
      funext k
      simp
    · intro j'
      have hc : (u (Fin.natAdd p j)).2 (comb ℓ (x₂ j')) = ((if j = j' then 1 else 0 : R') : Ω) := by
        rw [← hb₂ j', hj2 j']
        split_ifs <;> simp
      have h3 := hE3 ⟨u (Fin.natAdd p j), hu _⟩ (x₂ j') (if j = j' then 1 else 0) hj1 hc
      refine h3.trans ?_
      split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenbasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialize_hodge_lattice_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g p q : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
    (x₁ : Fin p → Fin g → R') (x₂ : Fin q → Fin g → R') (hu : ∀ i, u i ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    IsAdapted ρH σ b₁ b₂ u → (∀ i, b₁ i = comb ℓ (x₁ i)) → (∀ i, b₂ i = comb ℓ (x₂ i)) →
    IsAdapted ρHC σC (fun i k => ψ (x₁ i k)) (fun i k => ψ (x₂ i k)) (fun i => ev ⟨u i, hu i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isAdapted_eval | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isAdapted_eval | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isAdapted_eval <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointComponentEigenReduction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointComponentEigenReduction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def baseFn {O : Type} [CommRing O] (s : X ⟶ Sp O) (o : O) : Γ(X, ⊤) :=
  s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)


set_option backward.isDefEq.respectTransparency false in
theorem baseFn_value {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (s : X ⟶ Sp O) (f : Sp R ⟶ X)
    (φ : O →+* R) (hf : f ≫ s = spMap φ) (o : O) :
    (Scheme.stalkClosedPointTo f).hom (X.presheaf.germ ⊤ (centre f) trivial (baseFn s o)) = φ o := by
  have e : X.presheaf.germ ⊤ (f (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo f =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    set_option backward.isDefEq.respectTransparency.types false in
      rw [Scheme.germ_stalkClosedPointTo]
      simp [Iso.trans_hom, Scheme.Hom.appTop]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ f.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom φ := by
    rw [← Category.assoc s.appTop, ← Scheme.Hom.comp_appTop, hf, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  rw [← e] at e2
  exact congrArg (fun q => q.hom o) e2


set_option backward.isDefEq.respectTransparency false in
theorem genMap_germ (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (g : Γ(X, ⊤)) :
    genMap ξ p (X.presheaf.germ ⊤ p.1 trivial g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ ⊤ (genPt ξ) trivial g) := by
  have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := ⊤) (x := genPt ξ) (y := p.1) trivial p.2
  have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom g) e
  exact e2


set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes (ξ : Sp Ω ⟶ X) (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf p.2 h
  have e2 := congrArg (fun r => (r ≫ Scheme.stalkClosedPointTo ξ).hom s) e
  exact e2

theorem exists_inv {A L₁ L₂ : Type} [CommRing A] [Field L₁] [Field L₂] (f₁ : A →+* L₁) (f₂ : A →+* L₂)
    (hl : ∀ b, IsUnit (f₂ b) → IsUnit b) (g : A) (a₁ : L₁) (a₂ : L₂) (ha : a₂ ≠ 0)
    (h₁ : f₁ g = a₁⁻¹) (h₂ : f₂ g = a₂⁻¹) : ∃ u, f₁ u = a₁ ∧ f₂ u = a₂ := by
  obtain ⟨g, rfl⟩ := hl g (by rw [h₂]; exact (inv_ne_zero ha).isUnit)
  refine ⟨(g⁻¹ : Aˣ), ?_, ?_⟩
  · have := map_units_inv f₁.toMonoidHom g
    refine this.trans ?_
    show (f₁ g)⁻¹ = _
    rw [h₁, inv_inv]
  · have := map_units_inv f₂.toMonoidHom g
    refine this.trans ?_
    show (f₂ g)⁻¹ = _
    rw [h₂, inv_inv]

def valMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) : regAt ξ p →+* R :=
  ev.comp (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm.toRingHom

theorem valMap_genMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) (s : X.presheaf.stalk p.1) (h : genMap ξ p s ∈ regAt ξ p) :
    valMap ξ p hi ev ⟨genMap ξ p s, h⟩ = ev s := by
  have : (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm
      ⟨genMap ξ p s, h⟩ = s := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show ev _ = ev s
  exact congrArg ev this

variable {O F V K : Type} [CommRing O] [Field F] [CommRing V] [IsLocalRing V] [Field K] [Algebra V K]

theorem exists_germ (ξ : Sp Ω ⟶ X) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K) (y : Sp K ⟶ X)
    (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β)) (h₁ : genPt ξ ⤳ centre y) (x : F)
    (hx : x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ u : X.presheaf.stalk (centre y), genMap ξ ⟨_, h₁⟩ u = inc x ∧ (Scheme.stalkClosedPointTo y).hom u = βK x := by
  have key : ∀ o : O, genMap ξ ⟨_, h₁⟩ (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = inc (β o) ∧
      (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = βK (β o) := by
    intro o
    refine ⟨?_, baseFn_value s y (βK.comp β) hy o⟩
    exact (genMap_germ ξ ⟨_, h₁⟩ (baseFn s o)).trans (baseFn_value s ξ (inc.comp β) hξ o)
  by_cases h0 : x = 0
  · subst h0
    exact ⟨0, (map_zero _).trans (map_zero inc).symm,
      (map_zero (Scheme.stalkClosedPointTo y).hom).trans (map_zero βK).symm⟩
  rcases hx with ⟨o, rfl⟩ | ⟨o, ho⟩
  · exact ⟨_, key o⟩
  obtain ⟨k1, k2⟩ := key o
  rw [ho] at k1 k2
  exact exists_inv (genMap ξ ⟨_, h₁⟩) (Scheme.stalkClosedPointTo y).hom
    (fun b hb => (Scheme.isLocalHom_stalkClosedPointTo' y).map_nonunit b hb) _ (inc x) (βK x) ((map_ne_zero βK).2 h0)
    (k1.trans (map_inv₀ inc x)) (k2.trans (map_inv₀ βK x))

theorem val_abs (ξ : Sp Ω ⟶ X) (hg : IsCptGen ξ) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K)
    (y : Sp K ⟶ X) (z : Sp V ⟶ X) (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β))
    (hz : spMap (algebraMap V K) ≫ z = y) (h₁ : genPt ξ ⤳ centre y)
    (hF : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K),
      centre y ⤳ centre z ∧ regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ ∧
      (∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a)) ∧
      (∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : F, ∃ h : inc x ∈ regAt ξ ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  have hsp : centre y ⤳ centre z := by
    subst hz
    exact (IsLocalRing.specializes_closedPoint _).map z.continuous
  have h₂ : genPt ξ ⤳ centre z := h₁.trans hsp
  let ψ : regAt ξ ⟨_, h₁⟩ →+* K := valMap ξ ⟨_, h₁⟩ (hg.inj _) (Scheme.stalkClosedPointTo y).hom
  have c3 : ∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a) := by
    rintro ⟨_, s', rfl⟩
    exact ⟨h₁, s', rfl, (valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _).symm⟩
  have c4 : ∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r := by
    rintro a r ⟨h, s', rfl, rfl⟩
    exact ⟨⟨s', rfl⟩, valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _⟩
  refine ⟨h₂, ψ, hsp, ?_, c3, c4, ?_, ?_⟩
  · rintro _ ⟨s', rfl⟩
    refine ⟨(X.presheaf.stalkSpecializes hsp).hom s', ?_⟩
    exact genMap_specializes ξ ⟨_, h₁⟩ ⟨_, h₂⟩ hsp s'
  · rintro a h ⟨s', rfl⟩
    have v : ValAt ξ z (genMap ξ ⟨_, h₂⟩ s') ((Scheme.stalkClosedPointTo z).hom s') := ⟨h₂, s', rfl, rfl⟩
    have v' := GlobalTheory.T.valAt_comp_local_hom X Ω ξ V K (algebraMap V K) z _ _ v (by rw [hz]; exact h₁)
    rw [hz] at v'
    obtain ⟨h', e⟩ := c4 _ _ v'
    exact ⟨_, e.symm⟩
  · intro x
    obtain ⟨u, e1, e2⟩ := exists_germ ξ s inc β βK y hξ hy h₁ x (hF x)
    obtain ⟨h, e⟩ := c4 _ _ (⟨h₁, u, e1, e2⟩ : ValAt ξ y (inc x) (βK x))
    exact ⟨h, e⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem point_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X),
    Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) →
    j.comp βK = κ → y ≫ pullback.snd _ _ = spMap βK → Set.range y ⊆ U → spMap (algebraMap V K) ≫ z = y ≫ Y.j →
    ∃ (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
      (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K),
      centre (y ≫ Y.j) ⤳ centre z ∧ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ ∧
      (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) ∧
      (∀ (a : Z.Ω) (r : K), ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ →
        ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : c.F, ∃ h : Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z p κ V K _ _ _ _ _ _ j βK y z hβ hκ hj hjk hy hU hz
  have hsj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hξ : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, Z.over_inc, ← Spec.map_comp]
    rfl
  have hy' : (y ≫ Y.j) ≫ Y.s = spMap (βK.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, hy, ← Spec.map_comp]
    rfl
  have h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) :=
    ((Z.closure _).1 (hU ⟨IsLocalRing.closedPoint K, rfl⟩)).map Y.j.continuous
  have hF : ∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range := by
    intro x
    by_cases h : ‖κ x‖ ≤ 1
    · exact Or.inl ((hκ x).1 h)
    · refine Or.inr ((hκ _).1 ?_)
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
  obtain ⟨h₂, ψ, r⟩ := PointVal.val_abs (Z.ξ₀ ≫ Y.j) Z.gen Y.s Z.inc β βK (y ≫ Y.j) z hξ hy' hz h₁ hF
  exact ⟨h₁, h₂, ψ, r⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointComponentEigenReductionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_point_component_eigen_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X),
    Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) →
    j.comp βK = κ → y ≫ pullback.snd _ _ = spMap βK → Set.range y ⊆ U → spMap (algebraMap V K) ≫ z = y ≫ Y.j →
    ∃ (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
      (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K),
      centre (y ≫ Y.j) ⤳ centre z ∧ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ ∧
      (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) ∧
      (∀ (a : Z.Ω) (r : K), ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ →
        ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : c.F, ∃ h : Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.point_val | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.point_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.point_val <;> assumption)
end
end
