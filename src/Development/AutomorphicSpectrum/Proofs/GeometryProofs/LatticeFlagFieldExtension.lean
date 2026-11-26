module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbPull

theorem dual_frame_ext {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {W W' : Type} [AddCommGroup W] [Module Ω W]
    [AddCommGroup W'] [Module Ω' W'] (j : W →+ W') (hj : ∀ (a : Ω) (e : W), j (a • e) = i a • j e)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) (jW : Module.Dual Ω W →+ Module.Dual Ω' W')
    (hjW : ∀ u e, jW u (j e) = i (u e)) {r : ℕ} (b : Fin r → Module.Dual Ω W) (hli : LinearIndependent Ω b)
    (hb : Submodule.span Ω (Set.range b) = ⊤) :
    LinearIndependent Ω' (fun k => jW (b k)) ∧ Submodule.span Ω' (Set.range fun k => jW (b k)) = ⊤ := by
  classical
  let c := Module.Basis.mk hli hb.ge
  have hc : ∀ k, c k = b k := fun k => by simp [c]
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis c
  haveI : Module.Finite Ω W := (Module.finite_dual_iff Ω).1 inferInstance
  let e : Fin r → W := fun l => (Module.evalEquiv Ω W).symm (c.dualBasis l)
  have he : ∀ k l, b k (e l) = if k = l then 1 else 0 := by
    intro k l
    simp only [e]
    rw [Module.apply_evalEquiv_symm_apply, ← hc k, Module.Basis.dualBasis_apply_self]
  have hx : ∀ x : W, x = ∑ k, b k x • e k := by
    intro x
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff Ω _).1
    intro u
    have hu : u ∈ Submodule.span Ω (Set.range b) := by rw [hb]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      set_option synthInstance.maxHeartbeats 100000 in
        simp [he, map_sum]
    | zero => simp
    | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
  have hjx : ∀ x, j x = ∑ k, i (b k x) • j (e k) := by
    intro x
    conv_lhs => rw [hx x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj _ _
  have hext : ∀ v v' : Module.Dual Ω' W', (∀ k, v (j (e k)) = v' (j (e k))) → v = v' := by
    intro v v' h
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨x, rfl⟩
    rw [hjx x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, h]
  have hpair : ∀ k l, jW (b k) (j (e l)) = if k = l then 1 else 0 := by
    intro k l
    rw [hjW, he]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg l
    have := congrArg (fun v : Module.Dual Ω' W' => v (j (e l))) hg
    simpa [hpair] using this
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v (j (e k)) • jW (b k) := by
      apply hext
      intro l
      simp [hpair]
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem isVBOn_dual_pull : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  intro X X' Ω Ω' _ _ ξ ξ' f i V V' _ _ _ _ j jd W W' Lo Lo' T T' r hd _ hj hjd hW hvb hT
  have hmem : ∀ e : W, j e ∈ W' := fun e => by
    rw [hW]
    exact Submodule.subset_span ⟨e, e.2, rfl⟩
  let jr : W →+ W' :=
    { toFun := fun e => ⟨j e, hmem e⟩
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j _ _) }
  have hsm : ∀ (a : Ω) (e : W), jr (a • e) = i a • jr e := fun a e => Subtype.ext (hj.1 a e)
  have hext : IsExtOver i jr := ⟨hsm, fun n b hb => by
    have h1 := hj.2 n (fun k => (b k : V)) (hb.map' W.subtype W.ker_subtype)
    exact LinearIndependent.of_comp W'.subtype h1⟩
  have hs : Submodule.span Ω' (Set.range jr) = ⊤ := by
    have h1 : (Submodule.span Ω' (Set.range jr)).map W'.subtype = W' := by
      rw [Submodule.map_span]
      conv_rhs => rw [hW]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
        exact ⟨e, e.2, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
    have h2 := Submodule.comap_map_eq_of_injective W'.injective_subtype (Submodule.span Ω' (Set.range jr))
    rw [h1, Submodule.comap_subtype_self] at h2
    exact h2.symm
  obtain ⟨jW, hjW⟩ := DualExt.dual_ext Ω Ω' i W W' jr hext hs
  have hcomp : ∀ w, W'.dualRestrict (jd w) = jW (W.dualRestrict w) := by
    intro w
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    rw [hjW]
    exact hjd w e
  have hsemi : ∀ (a : Ω) (u : Module.Dual Ω W), jW (a • u) = i a • jW u := by
    intro a u
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    simp [hjW]
  intro p' hp'
  obtain ⟨hq, hpT, -⟩ := hT p' hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hpT
  obtain ⟨hli', hspan'⟩ := dual_frame_ext i jr hsm hs jW hjW b (hfr _ hpT hU).1 hb
  refine ⟨f ⁻¹ᵁ U, hU, fun k => jW (b k), hspan', fun q' hq' hq'U => ⟨hli', ?_⟩⟩
  obtain ⟨hq2, hqT, hL⟩ := hT q' hq'
  have hfrq := (hfr _ hqT hq'U).2
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : Subsingleton (Module.Dual Ω' W') := by
      rw [← Submodule.subsingleton_iff Ω', ← subsingleton_iff_bot_eq_top]
      rw [← hspan']
      simp
    exact Subsingleton.elim _ _
  · obtain ⟨hq3, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    apply le_antisymm
    · show Submodule.map _ _ ≤ _
      rw [hL hr, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      show W'.dualRestrict (jd w) ∈ _
      rw [hcomp]
      have hin : W.dualRestrict w ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b) := by
        rw [← hfrq]
        exact ⟨w, hw, rfl⟩
      have key : ∀ y ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b),
          jW y ∈ Submodule.span (regAt ξ' q') (Set.range fun k => jW (b k)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [map_add (f := _)]
          exact Submodule.add_mem _ hy hz
        | smul a y _ hy =>
          have : jW (a • y) = (⟨i a, hreg _ a.2⟩ : regAt ξ' q') • jW y := hsemi (a : Ω) y
          rw [this]
          exact Submodule.smul_mem _ _ hy
      exact key _ hin
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hin : b k ∈ (Lo.map W.dualRestrict) ⟨f q'.1, hq2⟩ := by
        rw [hfrq]
        exact Submodule.subset_span ⟨k, rfl⟩
      obtain ⟨w, hw, hwk⟩ := hin
      refine ⟨jd w, ?_, ?_⟩
      · rw [hL hr]
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      · show W'.dualRestrict (jd w) = jW (b k)
        rw [hcomp]
        exact congrArg jW hwk

end GlobalTheory.CompanionTheory.Ar.VbPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_flag_field_extension : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull | exact GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.VbPull.isVBOn_dual_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralAtPrimeInS
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralAtPrimeInS
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem pow_smul_mem_om_of_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (w : Module.Dual Ω 𝔐.Li), (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) → ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • w ∈ (Dc t).om := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS o _ _ ho Dc hfam s t w hw
  have hp : p.Prime := Fact.out
  have hT : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hs0 : mseg y s.1 ≠ 0 := s.2
  have ht0 : mseg y t.1 ≠ 0 := t.2
  have hfA : (mseg y s.1 / mseg y t.1) ∈ chartRing ℤ (mseg y) t.1 := div_mem_chartRing (mseg y) t.1 s.1
  have hle : ∀ a ∈ chartRing ℤ (mseg y) t.1, a ∈ chartRing o (mseg y) t.1 := by
    intro a ha
    have h2 : chartRing ℤ (mseg y) t.1 ≤ (chartRing o (mseg y) t.1).restrictScalars ℤ :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := o))
    exact h2 ha
  have hsm : ∀ a ∈ chartRing o (mseg y) t.1, ∀ e ∈ (Dc t).om, a • e ∈ (Dc t).om := by
    intro a ha e he
    have := (Dc t).om.smul_mem (⟨a, ha⟩ : chartRing o (mseg y) t.1) he
    rwa [Subalgebra.smul_def] at this
  have hinv : ∀ b : ℕ, ¬ p ∣ b → ((b : Ω))⁻¹ ∈ chartRing o (mseg y) t.1 := by
    intro b hb
    obtain ⟨r, hr⟩ := (ho ((b : Ω))⁻¹).2 ⟨1, b, hb, by simp⟩
    rw [← hr]
    exact Subalgebra.algebraMap_mem _ r
  by_contra hcon
  push_neg at hcon
  let I : Ideal (chartRing ℤ (mseg y) t.1) :=
    { carrier := {a | (a : Ω) • w ∈ (Dc t).om}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        rw [Subalgebra.coe_add, add_smul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        simp
      smul_mem' := fun a u hu => by
        show ((a • u : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        rw [smul_eq_mul, Subalgebra.coe_mul, mul_smul]
        exact hsm _ (hle _ a.2) _ hu }
  let T : Submonoid (chartRing ℤ (mseg y) t.1) :=
    { carrier := {u | ∃ b n : ℕ, ¬ p ∣ b ∧ (b : Ω) ≠ 0 ∧ (u : Ω) = (b : Ω) * (mseg y s.1 / mseg y t.1) ^ n}
      one_mem' := ⟨1, 0, hp.not_dvd_one, by simp, by simp⟩
      mul_mem' := by
        rintro u v ⟨b, n, hb, hb0, hu⟩ ⟨b', n', hb', hb0', hv⟩
        refine ⟨b * b', n + n', fun h => (hp.dvd_mul.1 h).elim hb hb', by push_cast; exact mul_ne_zero hb0 hb0', ?_⟩
        rw [Subalgebra.coe_mul, hu, hv]
        push_cast
        ring }
  have hdisj : Disjoint (I : Set (chartRing ℤ (mseg y) t.1)) (T : Set (chartRing ℤ (mseg y) t.1)) := by
    rw [Set.disjoint_left]
    rintro u hu ⟨b, n, hb, hb0, hub⟩
    have hu' : ((b : Ω) * (mseg y s.1 / mseg y t.1) ^ n) • w ∈ (Dc t).om := by rw [← hub]; exact hu
    have h2 := hsm _ (hinv b hb) _ hu'
    rw [smul_smul, ← _root_.mul_assoc, inv_mul_cancel₀ hb0, _root_.one_mul] at h2
    exact hcon n h2
  obtain ⟨P, hP, hIP, hPT⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  obtain ⟨q, hq, hqP⟩ := TieVB.exists_point hT ht0 P hP
  have notP : ∀ u ∈ T, u ∉ P := fun u hu huP => Set.disjoint_left.1 hPT huP hu
  have hfu : unitAt 𝔐.ξ q (mseg y s.1 / mseg y t.1) := by
    by_contra hn
    exact notP ⟨(mseg y s.1 / mseg y t.1), hfA⟩ ⟨1, 1, hp.not_dvd_one, by simp, by simp⟩ ((hqP ⟨(mseg y s.1 / mseg y t.1), hfA⟩).2 hn)
  have hOver : OverZp 𝔐 p q := by
    intro r hr hfib
    by_contra hrp
    have hrp' : ¬ p ∣ r := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm
    by_cases hr0 : (r : Ω) = 0
    · apply hcon 0
      rw [pow_zero, one_smul, hfam.om_iff t w]
      intro q' _ hq'
      exact absurd (hq' r hr (fun hu => hu.1 hr0)) hrp
    have hrT : (r : chartRing ℤ (mseg y) t.1) ∈ T :=
      ⟨r, 0, hrp', hr0, by simp⟩
    have hu := not_not.1 (mt (hqP (r : chartRing ℤ (mseg y) t.1)).2 (notP _ hrT))
    apply hfib
    simpa using hu
  have hqs : InChart 𝔐.ξ (mseg y) s.1 q := by
    refine ⟨hs0, fun c' => ?_⟩
    have he : mseg y c' / mseg y s.1 = mseg y c' / mseg y t.1 * (mseg y s.1 / mseg y t.1)⁻¹ := by
      rw [inv_div]
      field_simp
    rw [he]
    exact mul_mem (hq.2 c') hfu.2.2
  have hwq := hw q hqs hq hOver
  rw [hfam.om_loc t q hq hOver] at hwq
  obtain ⟨s₀, hs₀A, hs₀u, hs₀M⟩ := TieVB.exists_den_span hT hq ((Dc t).om.toAddSubgroup)
    (fun a ha e he => hsm a (hle a ha) e he)
    (show w ∈ Submodule.span _ (((Dc t).om.toAddSubgroup : Set (Module.Dual Ω 𝔐.Li))) from hwq)
  have hI : (⟨s₀, hs₀A⟩ : chartRing ℤ (mseg y) t.1) ∈ I := hs₀M
  exact (hqP ⟨s₀, hs₀A⟩).1 (hIP hI) hs₀u

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentIntegralAtPrimeInSStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_integral_at_prime_in_S : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (w : Module.Dual Ω 𝔐.Li), (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) → ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • w ∈ (Dc t).om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap | exact GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.pow_smul_mem_om_of_overlap <;> assumption)
end
end
