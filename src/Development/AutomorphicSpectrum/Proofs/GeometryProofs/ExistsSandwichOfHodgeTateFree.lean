module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeLower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTate
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentDataHeightIdentity
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TrivFlagModOfHodgeTateFreeOfRootLines
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeSpreadsOutFiniteTypeSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfRelAmpleRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.InhabZOn

theorem _root_.GlobalTheory.Models.InhabZOn.exists_dim_triple {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
    [ConnectedSpace S] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H S) : ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : GeometricallyIntegral t.G.hom :=
    _root_.GlobalTheory.geometricallyIntegral_of_isSemiAbelian (h := t.semi) _
  let e : S ⟶ t.G.left := (η[t.G]).left
  have he : e ≫ t.G.hom = 𝟙 S := Over.w (η[t.G])
  have hes : ∀ s, t.G.hom (e s) = s := fun s => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfib : ∀ s : S, _root_.IsPreconnected (t.G.hom ⁻¹' {s}) := fun s => by
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  have hsec : _root_.IsPreconnected (Set.range e) :=
    isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  haveI : PreconnectedSpace t.G.left := by
    refine ⟨isPreconnected_of_forall (e s₀) fun x _ => ?_⟩
    refine ⟨Set.range e ∪ t.G.hom ⁻¹' {t.G.hom x}, Set.subset_univ _, Or.inl ⟨s₀, rfl⟩,
      Or.inr rfl, ?_⟩
    exact hsec.union (e (t.G.hom x)) ⟨_, rfl⟩ (hes _) (hfib _)
  exact _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_dim_of_preconnected t.G.hom (e s₀)

end GlobalTheory.Models.InhabZOn

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich

theorem inFibre_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (p r : ℕ), p.Prime → r.Prime → InFibre ξ p q → InFibre ξ r q → r = p := by
  intro X Ω _ _ ξ q p r hp hr hpq hrq
  have key : ∀ n : ℕ, n.Prime → InFibre ξ n q →
      (n : X.presheaf.stalk q.1) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q.1) := by
    intro n hn hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hf
    have hn0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
    have h1 : genMap ξ q (↑u⁻¹ : X.presheaf.stalk q.1) * (n : Ω) = 1 := by
      rw [← map_natCast (genMap ξ q) n, ← map_mul, ← hu, Units.inv_mul, map_one]
    exact ⟨hn0, ⟨(n : X.presheaf.stalk q.1), map_natCast _ n⟩,
      ⟨(↑u⁻¹ : X.presheaf.stalk q.1), eq_inv_of_mul_eq_one_left h1⟩⟩
  by_contra hne
  have hcop : Nat.Coprime p r := (Nat.coprime_primes hp hr).2 (Ne.symm hne)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (1 : X.presheaf.stalk q.1) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q.1) := by
    have : ((a * p + b * r : ℤ) : X.presheaf.stalk q.1) = 1 := by rw [hab]; simp
    rw [← this]
    push_cast
    exact add_mem (Ideal.mul_mem_left _ _ (key p hp hpq)) (Ideal.mul_mem_left _ _ (key r hr hrq))
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem div_mem_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (p : ℕ), p.Prime → (∀ r : ℕ, r.Prime → InFibre ξ r q → r = p) → ∀ (a : ℤ) (b : ℕ), ¬ p ∣ b → (a : Ω) / (b : Ω) ∈ regAt ξ q := by
  intro X Ω _ _ ξ q p hp hover a b hb
  have hinv : ∀ b : ℕ, ¬ p ∣ b → ((b : Ω))⁻¹ ∈ regAt ξ q := by
    refine Nat.recOnMul (motive := fun b => ¬ p ∣ b → ((b : Ω))⁻¹ ∈ regAt ξ q) ?_ ?_ ?_ ?_
    · intro h
      exact absurd (dvd_zero p) h
    · intro _
      simp
    · intro r hr h
      have hne : r ≠ p := fun e => h (e ▸ dvd_rfl)
      have hnf : ¬ InFibre ξ r q := fun hf => hne (hover r hr hf)
      exact (not_not.1 hnf).2.2
    · intro m n hm hn h
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem (hm fun h' => h (dvd_mul_of_dvd_left h' _)) (hn fun h' => h (dvd_mul_of_dvd_right h' _))
  rw [div_eq_mul_inv]
  exact mul_mem (intCast_mem _ a) (hinv b hb)

theorem isCp_dvd : ∀ (Ω : Type) [Field Ω] (A : Subring Ω) (p : ℕ) [Fact p.Prime] (κ : Ω), κ ∈ A → IsCp p κ → ∃ u ∈ A, (p : Ω) ^ 2 = κ * u := by
  intro Ω _ A p hp κ hκA hκ
  unfold IsCp at hκ
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

theorem smul_htDual_mem : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : ReciprocityTheory.ChartRestriction.G.Semi.LB G.left) (n : ℕ) (O : Type) [CommRing O] (ρ : O →+* Module.End Ω Li) (σ : O →+* Ω) (g : ℕ), IsCptGen ξ → SmoothOfRelativeDimension g G.hom → ∀ (q : Cpt ξ) (κ : Ω), (∀ w ∈ M.omLat q, κ • w ∈ M.htOm L n q) → ∀ e ∈ M.htDual L n ρ σ q, κ • e ∈ M.eigLat ρ σ q := by
  intro X Ω _ ξ G _ _ Li _ _ M L n O _ ρ σ g hgen hsm q κ hκ e he
  obtain ⟨hvb, -⟩ := GlobalTheory.CompanionTheory.Ar.lieLat_isVB X G g Ω ξ Li M hgen hsm
  have hbi := (Lat.isVBOn_dual_and_bidual X Ω ξ Li M.lat Set.univ _ hvb).2 q trivial
  rw [M.mem_htDual_iff L n ρ σ q e] at he
  refine ⟨(hbi (κ • e)).2 fun w hw => ?_, Submodule.smul_mem _ κ he.1⟩
  have := he.2 (κ • w) (hκ w hw)
  simpa [map_smul, smul_eq_mul, LinearMap.smul_apply] using this

end GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich

namespace GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich

theorem exists_zp (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] :
    ∃ o : Subalgebra ℤ Ω, ∀ x : Ω, x ∈ o ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  refine ⟨{ carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
            mul_mem' := ?_, add_mem' := ?_, algebraMap_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h <;> contradiction
    · push_cast; rw [div_mul_div_comm]
  · rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    by_cases h0 : (b : Ω) = 0
    · exact ⟨a', b', hb', by simp [h0]⟩
    by_cases h0' : (b' : Ω) = 0
    · exact ⟨a, b, hb, by simp [h0']⟩
    refine ⟨a * b' + a' * b, b * b', fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h <;> contradiction
    · push_cast; rw [div_add_div _ _ h0 h0']; ring
  · intro n
    exact ⟨n, 1, hp.out.not_dvd_one, by simp⟩

theorem sandwich_of_htFree : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q), HTFree 𝔐 p → ∃ κ : Ω, IsCp p κ ∧ Sandwich 𝔐 p κ := by
  intro hF E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq hfree
  obtain ⟨o, ho⟩ := exists_zp Ω p
  have ho' : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
    intro x
    rw [← ho x]
    exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  obtain ⟨hchar, -, -, -, -, -, hch⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho'
  letI := hchar
  have hPT : PointHT := GlobalTheory.T.pointHT_of_fargues_hodge_tate hF
  obtain ⟨Dc, hfam, htest⟩ := GlobalTheory.T.hodge_tate_free_flag_lattice_lower E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho'
  obtain ⟨hproj, -, κ, hκ, hκA⟩ := GlobalTheory.T.hodge_tate_free_flag_lattice_upper E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho' Dc hfam hfree
  refine ⟨κ, hκ, fun q hq => ?_⟩
  have hover : OverZp 𝔐 p q := fun r hr hrq => inFibre_unique _ Ω 𝔐.ξ q p r Fact.out hr hq hrq
  obtain ⟨c', hc'⟩ := 𝔐.tie.cover q
  let s : {s : ∀ k, J k // mseg y s ≠ 0} := ⟨c', hc'.1⟩
  have hin : InChart 𝔐.ξ (mseg y) s.1 q := hc'
  have hreg : ∀ x ∈ chartRing o (mseg y) s.1, x ∈ regAt 𝔐.ξ q := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hin.2 j
    | algebraMap r =>
      obtain ⟨a, b, hb, h⟩ := (ho r).1 r.2
      rw [show algebraMap o Ω r = (r : Ω) from rfl, h]
      exact div_mem_regAt _ Ω 𝔐.ξ q p Fact.out hover a b hb
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hκq : κ ∈ regAt 𝔐.ξ q := hreg κ (hκA s)
  obtain ⟨hN, hIC, hFR, -⟩ := hch s.1 s.2
  let κA : chartRing o (mseg y) s.1 := ⟨κ, hκA s⟩
  obtain ⟨u, hu, hpu⟩ := isCp_dvd Ω (chartRing o (mseg y) s.1).toSubring p κ (hκA s) hκ
  have hdiv : κA * (p : chartRing o (mseg y) s.1) ^ (𝔐.R p - 2) ∣ (p : chartRing o (mseg y) s.1) ^ (𝔐.R p) := by
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, 𝔐.R p = k + 2 := ⟨𝔐.R p - 2, by have := 𝔐.R_ge p hpS; omega⟩
    rw [hk, Nat.add_sub_cancel]
    push_cast
    rw [pow_add, hpu]
    show _ = κ * _ * u
    ring
  have hinv : ∀ x : E, cmConj E (cmConj E x) = x := fun x => by simp [cmConj]
  obtain ⟨⟨-, hsm⟩, -⟩ := GlobalTheory.T.chart_sequence_holds (chartRing o (mseg y) s.1) Ω E (cmConj E) hinv p (𝔐.R p) (D.p + D.q)
    (Module.Dual Ω 𝔐.Li) (Dc s) κA (𝔐.R p - 2) hdiv (htest s κA hPT hκ) (hproj s).1
  have hκω : ∀ w ∈ 𝔐.M.omLat q, κ • w ∈ omP 𝔐 p q := by
    intro w hw
    rw [hfam.om_loc s q hin hover] at hw
    rw [hfam.om'_loc s q hin hq]
    induction hw using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ?_
      have := hsm x hx
      rwa [← algebraMap_smul Ω κA x] at this
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul r x _ hx =>
      have : κ • (r • x) = r • (κ • x) := by
        rw [Subring.smul_def, Subring.smul_def, smul_smul, smul_smul, mul_comm]
      rw [this]
      exact Submodule.smul_mem _ r hx
  refine ⟨hκq, 𝔐.M.htOm_le 𝔐.t.PP.L _ q, hκω, fun s' => ⟨𝔐.M.eigLat_le_htDual 𝔐.t.PP.L _ 𝔐.ρ (𝔐.emb s') q,
    fun e he => ?_⟩⟩
  have hirr : IrreducibleSpace 𝔐.X := by
    rw [irreducibleSpace_def]
    have hcl : closure ({genPt 𝔐.ξ} : Set 𝔐.X) = (⊤ : Set 𝔐.X) :=
      Set.eq_univ_of_forall fun x => specializes_iff_mem_closure.1 (𝔐.all x)
    rw [← hcl]
    exact isIrreducible_singleton.closure
  obtain ⟨d, hd⟩ := GlobalTheory.Models.InhabZOn.exists_dim_triple 𝔐.t
  exact smul_htDual_mem 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) (𝓞 E) 𝔐.ρ (𝔐.emb s') d
    𝔐.tie.gen hd q κ hκω e he

end GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFreeStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sandwich_of_hodge_tate_free : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q), HTFree 𝔐 p → ∃ κ : Ω, IsCp p κ ∧ Sandwich 𝔐 p κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree | exact GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersection
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.compact_datum_intersection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ), (∀ p ∈ S₀ ∪ Dc.SB B, p.Prime) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, 4 ≤ Or.𝔐.R p) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, FullTorsion Or.𝔐.t.G Or.𝔐.ξ (p ^ Or.𝔐.R p)) ∧ ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := by
  first | exact @LevelTowerAlt.component_data_height_identity | exact LevelTowerAlt.component_data_height_identity
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_datum_intersection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ), (∀ p ∈ S₀ ∪ Dc.SB B, p.Prime) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, 4 ≤ Or.𝔐.R p) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, FullTorsion Or.𝔐.t.G Or.𝔐.ξ (p ^ Or.𝔐.R p)) ∧ ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.compact_datum_intersection | exact GlobalTheory.CompanionTheory.Relay.compact_datum_intersection | (intros; apply GlobalTheory.CompanionTheory.Relay.compact_datum_intersection <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeTrivialFlagMod
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeTrivialFlagMod
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem trivFlagMod_rootLines_model : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), HTFree 𝔐 p → Fl.RootLines xdeg e → ∀ τ : CMType H, Num.TrivFlagMod o ((p : o) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => xdeg (τ, i)) :=
  PositivityTheory.HtPt.Ge.triv_flag_mod_of_hodge_tate_free_of_root_lines (fun hF => GlobalTheory.T.pointHT_of_fargues_hodge_tate hF)
    (fun E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq o _ _ ho =>
      GlobalTheory.T.hodge_tate_free_flag_lattice_lower E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho)

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeTrivialFlagModStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_free_trivial_flag_mod : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), HTFree 𝔐 p → Fl.RootLines xdeg e → ∀ τ : CMType H, Num.TrivFlagMod o ((p : o) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => xdeg (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_rootLines_model | exact GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_rootLines_model | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.trivFlagMod_rootLines_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsIsoAppOfIsAbelianScheme
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (f : S' ⟶ S) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by
      have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem isIso_appTop_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (V : S.Opens) [IsAffine V.toScheme] :
    IsIso (A.hom ∣_ V).appTop := by
  let R : Type := Γ(V.toScheme, ⊤)
  let e : V.toScheme ≅ Sp R := V.toScheme.isoSpec
  let f : Sp R ⟶ S := e.inv ≫ V.ι
  have hf : e.hom ≫ f = V.ι := by simp [f]
  obtain ⟨S₀, B, _, φ, -, hfin, hB, hpb⟩ :=
    GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R ((Over.pullback f).obj A) ∅ (isAbelianScheme_pullback A hA f)
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing ℤ S₀
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have w : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = (A.hom ∣_ V ≫ e.hom) ≫ f := by
    rw [Category.assoc, hf]
    exact (isPullback_morphismRestrict A.hom V).flip.w
  have sq : IsPullback (pullback.lift _ _ w) (A.hom ∣_ V) (pullback.snd A.hom f) e.hom := by
    refine IsPullback.of_right (h₁₂ := pullback.fst A.hom f) (v₁₃ := A.hom) (h₂₂ := f) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  exact GlobalTheory.ProperFunctions.isIso_appTop_baseChange (sq.paste_horiz hpb.1)

theorem isIso_app_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ U : S.Opens, IsIso (A.hom.app U) := fun _ A _ hA U ↦
  GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens A.hom (fun V ↦
    have : IsAffine V.1.toScheme := V.2
    isIso_appTop_restrict A hA V.1) U

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalModelPowerFree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalModelPowerFree
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GlobalFib

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem natCast_residueField_iff {Y Z : Scheme.{0}} (f : Y ⟶ Z) (y : Y) (n : ℕ) :
    (n : Z.residueField (f y)) = 0 ↔ (n : Y.residueField y) = 0 := by
  rw [← map_natCast (f.residueFieldMap y).hom n, map_eq_zero]

theorem natCast_mem_of_residueField {Z : Scheme.{0}} {A : Type} [CommRing A] (f : Z ⟶ Sp A) (z : Z) (n : ℕ)
    (h : (n : Z.residueField z) = 0) : (n : A) ∈ (f z).asIdeal := by
  have := (f z).isPrime
  have h₁ : (n : (Sp A).residueField (f z)) = 0 := by
    rw [← map_natCast (f.residueFieldMap z).hom n, map_eq_zero] at h
    exact h
  rw [← Ideal.algebraMap_residueField_eq_zero, map_natCast,
    ← map_natCast (Scheme.Spec.residueFieldIso (CommRingCat.of A) (f z)).hom.hom n, map_eq_zero]
  exact h₁

theorem isNoetherianRing_V (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : IsNoetherianRing (c.V W) := by
  obtain ⟨b, hb, -⟩ := GlobalTheory.GlobalModelGuards.exists_incl c W
  obtain ⟨M, hM⟩ := GlobalTheory.ShFam.Pad.BCEx.exists_isLocalization hp hW b hb
  letI := b.toAlgebra
  exact IsLocalization.isNoetherianRing M (c.V W) inferInstance

theorem not_isUnit_V (c : Coeff l) (W : ValuationSubring ℂ) (x : c.V W) (hx : ((x : c.F) : ℂ) ∈ W.nonunits) :
    ¬ IsUnit x := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvW : ((v : c.F) : ℂ) ∈ W := v.2
  have h1 : ((x : c.F) : ℂ) * ((v : c.F) : ℂ) = 1 := by
    have := congrArg (fun z : c.V W => ((z : c.F) : ℂ)) hv
    simpa using this
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have h2 := (W.valuation_le_one_iff _).2 hvW
  have h3 := congrArg W.valuation h1
  rw [map_mul, map_one] at h3
  exact (mul_lt_one_of_lt_of_le hx h2).ne h3

theorem exists_place_over (c : Coeff l) (q : PrimeSpectrum (𝓞 c.F)) {p : ℕ} (hp : p.Prime)
    (hq : (p : 𝓞 c.F) ∈ q.asIdeal) :
    ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits ∧ ∀ b : 𝓞 c.F →+* c.V W,
      (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → (IsLocalRing.maximalIdeal (c.V W)).comap b = q.asIdeal := by
  have := c.fin
  have : NumberField c.F := {}
  let φ : 𝓞 c.F →+* ℂ := c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)
  have hφ : Function.Injective φ := fun a b h => RingOfIntegers.coe_injective (Subtype.ext h)
  let e : 𝓞 c.F ≃+* φ.range :=
    RingEquiv.ofBijective φ.rangeRestrict ⟨fun a b h => hφ (by have h' := congrArg (fun x : φ.range => (x : ℂ)) h; exact h'), φ.rangeRestrict_surjective⟩
  let I : Ideal φ.range := q.asIdeal.comap (e.symm : φ.range →+* 𝓞 c.F)
  have hI : I ≠ ⊤ := fun h => q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have : (1 : φ.range) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using this))
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmem : ∀ x ∈ q.asIdeal, φ x ∈ W.nonunits := fun x hx =>
    hW ⟨e x, by simpa [I] using hx, rfl⟩
  refine ⟨W, ?_, fun b hb => ?_⟩
  · simpa [φ] using hmem _ hq
  have hne : q.asIdeal ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hq
    exact hp.ne_zero (by exact_mod_cast hq)
  have hmax : q.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal q.isPrime hne
  refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hx => ?_).symm
  refine not_isUnit_V c W (b x) ?_
  have := hmem x hx
  rw [show φ x = (((b x : c.V W) : c.F) : ℂ) by simp [φ, hb]] at this
  exact this

variable {Xo : Moduli D l} {c : Coeff l}

theorem isLocallyNoetherian_X (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsLocallyNoetherian Y.X := by
  have := c.fin
  have : NumberField c.F := {}
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  exact LocallyOfFiniteType.isLocallyNoetherian Y.s

theorem isReduced_X (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsReduced Y.X := by
  have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
    have := (Y.normal x).1
    infer_instance
  exact isReduced_of_isReduced_stalk Y.X

theorem generic_mem_abLocus (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (ξ : Y.X)
    (hξ : ∀ y : Y.X, y ⤳ ξ → y = ξ) : ξ ∈ abLocus Y.t.G := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have := Y.jQ_open
  have := Y.flat
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  let o : Sp c.F := IsLocalRing.closedPoint c.F
  have ho : spMap (algebraMap (𝓞 c.F) c.F) o ⤳ Y.s ξ := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have h1 : algebraMap (𝓞 c.F) c.F a ∈ IsLocalRing.maximalIdeal c.F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h1
    obtain rfl : a = 0 := RingOfIntegers.coe_injective (by simpa using h1)
    exact zero_mem _
  obtain ⟨ξ', h₁, h₂⟩ := Flat.generalizingMap Y.s ho
  obtain rfl := hξ ξ' h₁
  obtain ⟨ζ, hζ⟩ : ξ' ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨o, h₂.symm⟩
  have : IsLocallyNoetherian (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) :) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian (pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := {}
  have hr : ζ ∈ Set.range Y.jQ := by
    refine GlobalTheory.TraitGeneric.mem_of_dense_of_maximal (fun y hy => ?_) Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense
    have : y = ζ := by
      refine (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_
      rw [hζ]
      exact hξ _ (hζ ▸ hy.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
    rw [this]
  rw [← Y.ab_gen] at hr
  rw [← hζ]
  exact hr

theorem global_fibPF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b) → PowFns Ygl.t ∧ ∀ (p : ℕ), p.Prime → ∀ z : Ygl.X, (p : Ygl.X.residueField z) = 0 → FibPF Ygl.t z := by
  intro E _ _ _ H D Xo Y hY l c hg Ygl hdom
  refine ⟨GlobalTheory.T.powFns_of_abelian_generic E H Ygl.X Ygl.t (isReduced_X Ygl) (isLocallyNoetherian_X Ygl)
    (fun z hz => generic_mem_abLocus Ygl z hz), ?_⟩
  intro p hp z hz
  have hq : (p : 𝓞 c.F) ∈ (Ygl.s z).asIdeal := natCast_mem_of_residueField Ygl.s z p hz
  obtain ⟨W, hW, hc⟩ := exists_place_over c (Ygl.s z) hp hq
  obtain ⟨b, hb, -⟩ := GlobalTheory.GlobalModelGuards.exists_incl c W
  have hpt : Ygl.s z = spMap b (IsLocalRing.closedPoint (c.V W)) :=
    PrimeSpectrum.ext (hc b hb).symm
  obtain ⟨z', rfl, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Ygl.s) (g := spMap b) z _ hpt
  obtain ⟨f, t, m₁, m₂, -, -, -⟩ := hdom p W hp hW b hb
  have hN := isNoetherianRing_V c W hp hW
  have hinj : Function.Injective (c.V W).subtype := Subtype.val_injective
  have hz' : (p : ((Y p W hp hW ⟨l, c, hg p hp⟩).X).residueField (f z')) = 0 := by
    exact (natCast_residueField_iff f z' p).2 ((natCast_residueField_iff _ z' p).1 hz)
  have h₁ := GlobalTheory.T.model_fibres_power_free E H D l (Xo l) c (c.V W) (c.V W).subtype (Y p W hp hW ⟨l, c, hg p hp⟩)
    (GlobalTheory.LocM.BaseMdl.dense_j hinj _) (hY p W hp hW _).1 (hY p W hp hW _).2 p hp (f z') hz'
  exact (GlobalTheory.T.fibre_power_free_pullback E H _ _ _ t _ m₁ z').1 ((GlobalTheory.T.fibre_power_free_pullback E H _ _ _ t f m₂ z').2 h₁)

end GlobalTheory.CompanionTheory.Ar.GlobalFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalModelPowerFreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_model_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Ygl : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → Dominates Ygl (Y p W hp hW ⟨l, c, hg p hp⟩) b) → PowFns Ygl.t ∧ ∀ (p : ℕ), p.Prime → ∀ z : Ygl.X, (p : Ygl.X.residueField z) = 0 → FibPF Ygl.t z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GlobalFib.global_fibPF | exact GlobalTheory.CompanionTheory.Ar.GlobalFib.global_fibPF | (intros; apply GlobalTheory.CompanionTheory.Ar.GlobalFib.global_fibPF <;> assumption)
end
end
