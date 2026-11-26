module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.ChartMonNeZero
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Famproj
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GcChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagFieldExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosed
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.IntEmb

theorem ringOfIntegers_embedding_mem_range
    (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω]
    [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A Ω).range := by
  have hℤ : IsIntegral ℤ (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom ℤ) σ (RingHom.ext_int _ _)
      (NumberField.RingOfIntegers.isIntegral_coe a)
  have hA : IsIntegral A (σ (a : E)) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom A) (RingHom.id Ω) (RingHom.ext_int _ _) hℤ
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp hA
  exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.Ar.IntEmb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldIntegersInIntegrallyClosedStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_integers_in_integrally_closed : ∀ (A Ω : Type) [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [IsIntegrallyClosed A] (E : Type) [Field E] [NumberField E] (σ : E →+* Ω) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A Ω).range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | exact GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range | (intros; apply GlobalTheory.CompanionTheory.Ar.IntEmb.ringOfIntegers_embedding_mem_range <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingMemAfterMonomialScaling
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingMemAfterMonomialScaling
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap

theorem pow_mul_mem_chartRing_mseg : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (s t : ∀ k, J k), mseg y s ≠ 0 → mseg y t ≠ 0 → ∀ a ∈ chartRing o (mseg y) s, ∃ n : ℕ, (mseg y s / mseg y t) ^ n * a ∈ chartRing o (mseg y) t := by
  intro o _ Ω _ _ K _ J y s t hs _ a ha
  exact exists_pow_mul_mem_chartRing (mseg y) s t hs ha

end GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartRingMemAfterMonomialScalingStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ring_mem_after_monomial_scaling : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (s t : ∀ k, J k), mseg y s ≠ 0 → mseg y t ≠ 0 → ∀ a ∈ chartRing o (mseg y) s, ∃ n : ℕ, (mseg y s / mseg y t) ^ n * a ∈ chartRing o (mseg y) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | exact GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.ChartOverlap.pow_mul_mem_chartRing_mseg <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedHomology
theorem UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg :
    ∀ {A K : Type} [inst : CommRing A] [inst_1 : Field K] [inst_2 : Algebra A K] {E : Type} [inst_3 : Field E]
      [inst_4 : NumberField E] {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [inst_5 : AddCommGroup Ω] [inst_6 : _root_.Module K Ω]
      [inst_7 : _root_.Module A Ω] [inst_8 : IsScalarTower A K Ω] (D : GlobalTheory.CompanionTheory.Ar.HT.HTChart A K c p R N Ω) (σ : E →+* K),
      (D.omHT σ).FG := by
  intro A K _ _ _ E _ _ c p R N Ω _ _ _ _ D σ
  have hZ : (LinearMap.range D.h.toIntLinearMap).FG := Submodule.fg_range _
  have hA : (Submodule.span A (Set.range D.h)).FG := by
    obtain ⟨S, hS⟩ := hZ
    refine ⟨S, ?_⟩
    have h1 : Set.range D.h = (Submodule.span ℤ (S : Set Ω) : Set Ω) := by
      rw [hS]; rfl
    rw [h1, Submodule.span_span_of_tower]
  exact (hA.sup (D.om_lat.fg.map _)).map _
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GeTriv
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FrameExpandLoc
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CoefMemDual
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GeFrame
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Ge

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

noncomputable def qL (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem qL_apply (σ : E →+* K) (x : Fin N → A) : qL D σ x = D.q σ x := rfl

theorem frame_expand {σ : E →+* K} {m j k : ℕ}
    {i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)}
    {bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))} {bM : Basis (Fin k) A (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) A} (hex : D.ExactMod σ m i) (hg : D.IsFrame σ m i bW bM g)
    (x : Fin N → A) (t : Fin k → A) (y : Ω) (hy : y ∈ D.omHT σ)
    (e : D.q σ x = ∑ a, t a • (bM a : Ω) + ((p : A) ^ m) • y) :
    ∃ (s : Fin j → A) (z : Fin N → A), x = g.mulVec (Sum.elim s t) + ((p : A) ^ m) • z := by
  obtain ⟨hcol1, hcol2⟩ := hg
  choose x'' hx'' using hcol1
  choose yM hyM hq using hcol2
  have hx1 : ∃ y₁ ∈ D.omHT σ, D.q σ (x - ∑ a, t a • (fun l => g l (Sum.inr a))) = ((p : A) ^ m) • y₁ := by
    refine ⟨y - ∑ a, t a • yM a, ?_, ?_⟩
    · exact Submodule.sub_mem _ hy (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hyM a))
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← qL_apply, map_sub, map_sum]
      simp only [map_smul, qL_apply, hq, e, smul_add, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
      simp only [smul_comm (t _) ((p : A) ^ m)]
      abel
  obtain ⟨w, x', hw⟩ := (hex.2.1 _).1 hx1
  refine ⟨bW.repr w, x' - ∑ b, bW.repr w b • x'' b, ?_⟩
  have hiw : i w = ∑ b, bW.repr w b • i (bW b) := by
    conv_lhs => rw [← bW.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  have hcolL : ∀ b, i (bW b) = (fun l => g l (Sum.inl b)) - ((p : A) ^ m) • x'' b := fun b => by
    rw [hx'' b]
    abel
  have hx : x = ∑ a, t a • (fun l => g l (Sum.inr a)) + i w + ((p : A) ^ m) • x' := by
    rw [add_assoc, ← hw]
    abel
  rw [hx, hiw]
  simp only [hcolL]
  ext l
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
  ring_nf
  have s1 : ∑ x, g l (Sum.inl x) * (bW.repr w) x = ∑ x, (bW.repr w) x * g l (Sum.inl x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s2 : ∑ x, g l (Sum.inr x) * t x = ∑ x, t x * g l (Sum.inr x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s3 : ∑ x, (p : A) ^ m * (bW.repr w) x * x'' x l = ∑ x, (bW.repr w) x * (p : A) ^ m * x'' x l :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [s1, s2, s3]
  ring

end

theorem frame_exists : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (m j k : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) (bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))) (bM : Basis (Fin k) A (D.omHT σ)) (eqv : Fin j ⊕ Fin k ≃ Fin N), (∀ x, D.q σ x ∈ D.omHT σ) → D.ExactMod σ m i → (∃ g, D.IsFrame σ m i bW bM g) ∧ ∀ g, D.IsFrame σ m i bW bM g → ∃ h r : A, (g.submatrix id eqv.symm).det * h = 1 + (p : A) ^ m * r := by
  intro A K _ _ _ _ _ E _ _ c _ p R N _ Ω _ _ _ _ D σ m j k i bW bM eqv hqM hex
  refine ⟨?_, fun g hg => ?_⟩
  · have h3 : ∀ a : Fin k, ∃ x : Fin N → A, ∃ y ∈ D.omHT σ, D.q σ x = (bM a : Ω) + ((p : A) ^ m) • y := by
      intro a
      obtain ⟨x, y', hy', he⟩ := hex.2.2 (bM a) (bM a).2
      refine ⟨x, -y', Submodule.neg_mem _ hy', ?_⟩
      rw [he, smul_neg]
      abel
    choose xs ys hys hxs using h3
    refine ⟨Matrix.of fun l c => Sum.elim (fun a => i (bW a) l) (fun a => xs a l) c, fun a => ⟨0, ?_⟩,
      fun a => ⟨ys a, hys a, ?_⟩⟩
    · funext l
      simp
    · simpa using hxs a
  · have hsurj : ∀ x : Fin N → A, ∃ v : Fin j ⊕ Fin k → A, ∃ z : Fin N → A,
        x = g.mulVec v + ((p : A) ^ m) • z := by
      intro x
      obtain ⟨s, z, hz⟩ := frame_expand D hex hg x (bM.repr ⟨D.q σ x, hqM x⟩) 0 (Submodule.zero_mem _) (by
        rw [smul_zero, add_zero]
        have h5 := congrArg Subtype.val (bM.sum_repr ⟨D.q σ x, hqM x⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h5
        exact h5.symm)
      exact ⟨_, z, hz⟩
    choose v z hvz using fun l : Fin N => hsurj (Pi.single l 1)
    have hprod : g.submatrix id eqv.symm * Matrix.of (fun c l => v l (eqv.symm c)) =
        1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) := by
      ext l l'
      rw [Matrix.mul_apply]
      simp only [Matrix.submatrix_apply, id, Matrix.of_apply]
      have e1 : ∑ c, g l (eqv.symm c) * v l' (eqv.symm c) = (g.mulVec (v l')) l := by
        rw [Matrix.mulVec, dotProduct]
        exact Equiv.sum_comp eqv.symm (fun d => g l d * v l' d)
      rw [e1, eq_sub_of_add_eq (hvz l').symm]
      simp [Matrix.one_apply, Pi.single_apply]
    have hmem : (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A).det - 1 ∈
        Ideal.span {((p : A) ^ m)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]
      have e2 : (Ideal.Quotient.mk (Ideal.span {((p : A) ^ m)})).mapMatrix
          (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A) = 1 := by
        ext a b
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
          map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul, sub_zero,
          Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, Matrix.det_one]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨(Matrix.of (fun c l => v l (eqv.symm c)) : Matrix (Fin N) (Fin N) A).det, r, ?_⟩
    rw [← Matrix.det_mul, hprod]
    linear_combination (-1 : A) * hr

end PositivityTheory.HtPt.Ge
end

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct Filter

namespace PositivityTheory.HtPt.Ge

section Loc
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def loc (B : Subalgebra o Ω) (u : Ω) (hu : u ∈ B) : Subring Ω where
  carrier := {a | ∃ n : ℕ, u ^ n * a ∈ B}
  one_mem' := ⟨0, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [mul_neg]; exact neg_mem h⟩
  mul_mem' := fun ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := mul_mem h h'
    rwa [mul_mul_mul_comm, ← pow_add] at this⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (mul_mem (pow_mem hu n') h) (mul_mem (pow_mem hu n) h')
    convert this using 1
    ring⟩

variable {B : Subalgebra o Ω} {u : Ω} {hu : u ∈ B}

theorem loc_of_mem {a : Ω} (h : a ∈ B) : a ∈ loc B u hu := ⟨0, by simpa using h⟩

theorem loc_ev {a : Ω} (h : a ∈ loc B u hu) : ∀ᶠ n in atTop, u ^ n * a ∈ B := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := mul_mem (pow_mem hu d) h
  convert this using 1
  ring

theorem loc_of_pow {a : Ω} (n : ℕ) (h : u ^ n * a ∈ loc B u hu) : a ∈ loc B u hu := by
  obtain ⟨m, h⟩ := h
  exact ⟨m + n, by rwa [pow_add, mul_assoc]⟩

variable {V : Type} [AddCommGroup V] [Module Ω V]

def locM (M : Submodule B V) (u : Ω) (hu : u ∈ B) : AddSubgroup V where
  carrier := {v | ∃ n : ℕ, u ^ n • v ∈ M}
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := fun ⟨n, h⟩ => ⟨n, by rw [smul_neg]; exact neg_mem h⟩
  add_mem' := fun {a b} ⟨n, h⟩ ⟨n', h'⟩ => ⟨n + n', by
    have := add_mem (M.smul_mem ⟨_, pow_mem hu n'⟩ h) (M.smul_mem ⟨_, pow_mem hu n⟩ h')
    simp only [Subalgebra.smul_def, smul_smul, ← pow_add] at this
    rwa [smul_add, add_comm n' n] at *⟩

theorem locM_smul {M : Submodule B V} {a : Ω} {v : V} (ha : a ∈ loc B u hu) (hv : v ∈ locM M u hu) :
    a • v ∈ locM M u hu := by
  obtain ⟨n, h⟩ := ha
  obtain ⟨n', h'⟩ := hv
  refine ⟨n + n', ?_⟩
  have := M.smul_mem ⟨_, h⟩ h'
  simp only [Subalgebra.smul_def, smul_smul] at this ⊢
  convert this using 2
  ring

theorem locM_ev {M : Submodule B V} {v : V} (h : v ∈ locM M u hu) : ∀ᶠ n in atTop, u ^ n • v ∈ M := by
  obtain ⟨n, h⟩ := h
  filter_upwards [eventually_ge_atTop n] with m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := M.smul_mem ⟨_, pow_mem hu d⟩ h
  simp only [Subalgebra.smul_def, smul_smul] at this
  rwa [add_comm, pow_add]

theorem coef_mem [IsFractionRing B Ω] {P : Type} [AddCommGroup P] [Module B P] (ι : P →ₗ[B] V)
    (hι : Function.Injective ι) {k : ℕ} (b : Basis (Fin k) B P) (T : Fin k → Ω) (n : ℕ) (x : P)
    (e : u ^ n • ∑ a, T a • ι (b a) = ι x) (a : Fin k) : T a ∈ loc B u hu := by
  have h1 : LinearIndependent Ω (fun a => ι (b a)) :=
    (LinearIndependent.iff_fractionRing B Ω).1 (b.linearIndependent.map' ι (LinearMap.ker_eq_bot.2 hι))
  have h2 : ∑ a, (u ^ n * T a - (b.repr x a : Ω)) • ι (b a) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, e]
    have := congrArg ι (b.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Subalgebra.smul_def] at this
    rw [this, sub_self]
  have := Fintype.linearIndependent_iff.1 h1 _ h2 a
  exact ⟨n, by rw [sub_eq_zero.1 this]; exact (b.repr x a).2⟩

theorem coef_mem_dual [IsFractionRing B Ω] (W : Submodule B V) (hW : W.FG) {j : ℕ}
    (b : Basis (Fin j) B (Dual B W)) (φ : Fin j → Dual Ω V) (hφ : ∀ a (z : W), (b a z : Ω) = φ a z)
    (T : Fin j → Ω) (h : ∀ z ∈ W, (∑ a, T a • φ a) z ∈ loc B u hu) (a : Fin j) : T a ∈ loc B u hu := by
  set ψ := ∑ a, T a • φ a with hψ
  obtain ⟨S, hS⟩ := hW
  obtain ⟨n, hn⟩ := ((eventually_all_finset S).2 fun z hz =>
    loc_ev (h z (hS ▸ Submodule.subset_span hz))).exists
  have hn' : ∀ z ∈ W, u ^ n * ψ z ∈ B := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hn x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [Subalgebra.smul_def, map_smul, smul_eq_mul, mul_left_comm]; exact mul_mem c.2 hx
  let x : Dual B W :=
    { toFun := fun z => ⟨_, hn' z z.2⟩
      map_add' := fun z z' => Subtype.ext (by simp [mul_add])
      map_smul' := fun c z => Subtype.ext (by simp [Subalgebra.smul_def, mul_left_comm]) }
  let ι : Dual B W →ₗ[B] (W → Ω) :=
    { toFun := fun f z => (f z : Ω)
      map_add' := fun f g => by ext z; simp
      map_smul' := fun c f => by ext z; simp [Subalgebra.smul_def] }
  refine coef_mem ι (fun f g e => LinearMap.ext fun z => Subtype.ext (congrFun e z)) b T n x ?_ a
  ext z
  simp [ι, x, hψ, hφ]

end Loc

theorem tri {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {n : ℕ} (w f g : Fin n → V) (df dg : Fin n → Ω)
    (hg0 : ∀ a, dg a ≠ 0)
    (hf : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = df a ∧ f a = ∑ a', cf a' • w a')
    (hg : ∀ a, ∃ cf : Fin n → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = dg a ∧ g a = ∑ a', cf a' • w a') :
    ∃ T : Matrix (Fin n) (Fin n) Ω, (∀ a' a, a < a' → T a' a = 0) ∧ (∀ a, T a a = df a / dg a) ∧
      ∀ a, f a = ∑ a', T a' a • g a' := by
  choose cf f1 f2 f3 using hf
  choose cg g1 g2 g3 using hg
  let F : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cf a a'
  let G : Matrix (Fin n) (Fin n) Ω := Matrix.of fun a' a => cg a a'
  have hF : F.BlockTriangular id := fun a' a h => f1 a a' h
  have hG : G.BlockTriangular id := fun a' a h => g1 a a' h
  have hdet : IsUnit G.det := by
    rw [Matrix.det_of_upperTriangular hG, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro a _
    simpa [G, g2] using hg0 a
  haveI := G.invertibleOfIsUnitDet hdet
  have hT : (G⁻¹ * F).BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hG).mul hF
  have e : G * (G⁻¹ * F) = F := Matrix.mul_nonsing_inv_cancel_left _ _ hdet
  refine ⟨G⁻¹ * F, fun a' a h => hT h, fun a => ?_, fun a => ?_⟩
  · have := congrFun (congrFun e a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at this
    · rw [eq_div_iff (hg0 a), ← g2, ← f2, mul_comm]
      exact this
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hG h, zero_mul]
      · rw [hT h, mul_zero]
    · simp
  · simp only [g3, Finset.smul_sum, smul_smul]
    rw [f3, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have := congrFun (congrFun e l) a
    rw [Matrix.mul_apply] at this
    refine Eq.trans ?_ (this.symm.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _))
    rfl

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem omHT_fg (σ : E →+* K) : (D.omHT σ).FG :=
  by apply _root_.UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg <;> assumption

end

end PositivityTheory.HtPt.Ge
end

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct Filter

namespace PositivityTheory.HtPt.Ge

theorem cancel_gram {Ω : Type} [Field Ω] (L : Subring Ω) {N : ℕ} (G H Z : Matrix (Fin N) (Fin N) Ω) (P Q : Ω)
    (hQ : Q ∈ L) (hH : ∀ i j, H i j ∈ L) (hZ : ∀ i j, Z i j ∈ L) (e : G * H = 1 + (P * Q) • Z)
    (r ζ : Fin N → Ω) (hr : ∀ l, r l ∈ L) (hζ : ∀ l, ζ l ∈ L) (h : Matrix.vecMul r G = P • ζ) :
    ∃ z : Fin N → Ω, (∀ l, z l ∈ L) ∧ r = P • z := by
  refine ⟨Matrix.vecMul ζ H - Q • Matrix.vecMul r Z, ?_, ?_⟩
  · intro l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine L.sub_mem ?_ (L.mul_mem hQ ?_)
    · simp only [Matrix.vecMul, dotProduct]
      exact L.sum_mem fun i _ => L.mul_mem (hζ i) (hH i l)
    · simp only [Matrix.vecMul, dotProduct]
      exact L.sum_mem fun i _ => L.mul_mem (hr i) (hZ i l)
  · have h1 : Matrix.vecMul r (G * H) = Matrix.vecMul r 1 + Matrix.vecMul r ((P * Q) • Z) := by
      rw [e, Matrix.vecMul_add]
    rw [← Matrix.vecMul_vecMul, h, Matrix.smul_vecMul, Matrix.vecMul_one, Matrix.vecMul_smul] at h1
    rw [smul_sub, smul_smul, h1]
    abel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {B : Subalgebra o Ω} {u : Ω} {hu : u ∈ B}
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p R N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]

theorem frame_expand_loc (hu0 : u ≠ 0) (D : HTChart B Ω c p R N V) {σ : E →+* Ω} {m j k : ℕ}
    {i : Module.Dual B (D.omHT (σ.comp c.toRingHom)) →ₗ[B] (Fin N → B)}
    {bW : Basis (Fin j) B (Module.Dual B (D.omHT (σ.comp c.toRingHom)))} {bM : Basis (Fin k) B (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) B} (hex : D.ExactMod σ m i) (hg : D.IsFrame σ m i bW bM g)
    (x : Fin N → Ω) (hx : ∀ l, x l ∈ loc B u hu) (t : Fin k → Ω) (ht : ∀ a, t a ∈ loc B u hu)
    (y : V) (hy : y ∈ locM (D.omHT σ) u hu)
    (e : ∑ l, x l • eigProj D.ρΩ σ (D.h (Pi.single l 1)) = ∑ a, t a • (bM a : V) + ((p : Ω) ^ m) • y) :
    ∃ (s : Fin j → Ω) (z : Fin N → Ω), (∀ a, s a ∈ loc B u hu) ∧ (∀ l, z l ∈ loc B u hu) ∧
      ∀ l, x l = ∑ a, (g l (Sum.inl a) : Ω) * s a + ∑ a, (g l (Sum.inr a) : Ω) * t a + (p : Ω) ^ m * z l := by
  have hev : ∀ᶠ n : ℕ in atTop, (∀ l, u ^ n * x l ∈ B) ∧ (∀ a, u ^ n * t a ∈ B) ∧
      u ^ n • y ∈ D.omHT σ :=
    (Filter.eventually_all.2 fun l => loc_ev (hx l)).and
      ((Filter.eventually_all.2 fun a => loc_ev (ht a)).and (locM_ev hy))
  obtain ⟨n, hxn, htn, hyn⟩ := hev.exists
  have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
  let X : Fin N → B := fun l => ⟨u ^ n * x l, hxn l⟩
  let T : Fin k → B := fun a => ⟨u ^ n * t a, htn a⟩
  have hq : D.q σ X = ∑ a, T a • (bM a : V) + ((p : B) ^ m) • (u ^ n • y) := by
    have e' := congrArg (fun v => u ^ n • v) e
    simp only [Finset.smul_sum, smul_add, smul_smul] at e'
    change ∑ l, (u ^ n * x l) • eigProj D.ρΩ σ (D.h (Pi.single l 1)) =
      ∑ a, (u ^ n * t a) • (bM a : V) + (((p : B) ^ m : B) : Ω) • (u ^ n • y)
    rw [e', smul_smul]
    congr 1
    push_cast
    rw [mul_comm]
  obtain ⟨s', z', hsz⟩ := frame_expand D hex hg X T (u ^ n • y) hyn hq
  have hmem : ∀ b : B, (u ^ n)⁻¹ * (b : Ω) ∈ loc B u hu := fun b =>
    loc_of_pow n (by rw [← mul_assoc, mul_inv_cancel₀ hun, one_mul]; exact loc_of_mem b.2)
  refine ⟨fun a => (u ^ n)⁻¹ * s' a, fun l => (u ^ n)⁻¹ * z' l, fun a => hmem _, fun l => hmem _, ?_⟩
  intro l
  have hl := congrArg (fun v : Fin N → B => ((v l : B) : Ω)) hsz
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, X, T] at hl
  push_cast at hl
  apply mul_left_cancel₀ hun
  rw [hl, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · field_simp

private theorem exists_sum_gram_eq_add_prime_pow_mul {C : Subalgebra o Ω} (D : HTChart C Ω c p R N V) {σ : E →+* Ω} {m j k : ℕ} {d : C}
    {i : Module.Dual C (D.omHT (σ.comp c.toRingHom)) →ₗ[C] (Fin N → C)}
    {W : Basis (Fin j) C (Module.Dual C (D.omHT (σ.comp c.toRingHom)))} {M : Basis (Fin k) C (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) C} (hi : D.IsDualMap σ d m i) (hg : D.IsFrame σ m i W M g)
    (a : Fin j) (l' : Fin N) :
    ∃ (hY : eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single l' 1)) ∈ D.omHT (σ.comp c.toRingHom))
      (z : C) (x' : Fin N → C),
      ∑ l, (g l (Sum.inl a) : Ω) * D.gram σ d l l' =
        (W a ⟨_, hY⟩ : Ω) + (p : Ω) ^ m * z + (p : Ω) ^ m * ∑ l, (x' l : Ω) * D.gram σ d l l' := by
  have hY : eigProj D.ρΩ (σ.comp c.toRingHom) (D.h (Pi.single l' 1)) ∈ D.omHT (σ.comp c.toRingHom) :=
    Submodule.mem_map_of_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨x', hx'⟩ := hg.1 a
  obtain ⟨z, hz⟩ := hi (W a) l' ⟨_, hY⟩ rfl
  refine ⟨hY, z, x', ?_⟩
  have hcol : ∀ l, (g l (Sum.inl a) : Ω) = (i (W a) l : Ω) + (p : Ω) ^ m * x' l := fun l => by
    have h1 := congrFun hx' l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    push_cast
    ring
  have hz' : ∑ l, (i (W a) l : Ω) * D.gram σ d l l' = (W a ⟨_, hY⟩ : Ω) + (p : Ω) ^ m * z := by
    have h2 : ∑ l, (i (W a) l : Ω) * D.gram σ d l l' =
        (((W a ⟨_, hY⟩ + (p : C) ^ m * z : C)) : Ω) := hz
    rw [h2]
    push_cast
    ring
  simp only [hcol, add_mul, Finset.sum_add_distrib, hz', Finset.mul_sum, mul_assoc]

theorem overlap [CharZero Ω] [Fact p.Prime] [IsFractionRing B Ω] (hc : ∀ x, c (c x) = x) (hu0 : u ≠ 0)
    {A : Subalgebra o Ω} (hAL : ∀ a ∈ A, a ∈ loc B u hu)
    (DA : HTChart A Ω c p R N V) (DB : HTChart B Ω c p R N V) {σ : E →+* Ω} {m j k : ℕ} (hm : m ≤ R)
    (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ B) (dA : A) (dB : B) (hd : (dA : Ω) = dB) (hdB : GeneratesDiff σ dB)
    (hρ : DA.ρΩ = DB.ρΩ) (he : DA.e = DB.e)
    (hM : ∀ x ∈ DA.omHT σ, ∃ n : ℕ, u ^ n • x ∈ DB.omHT σ)
    (hW : ∀ x ∈ DB.omHT (σ.comp c.toRingHom), ∃ n : ℕ, u⁻¹ ^ n • x ∈ DA.omHT (σ.comp c.toRingHom))
    (hh : ∀ (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ DB.omHT σ',
      u ^ n • eigProj DB.ρΩ σ' (DA.h x - DB.h x) = ((p : Ω) ^ m) • z)
    {iA : Module.Dual A (DA.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)}
    {iB : Module.Dual B (DB.omHT (σ.comp c.toRingHom)) →ₗ[B] (Fin N → B)}
    (hiA : DA.IsDualMap σ dA m iA) (hiB : DB.IsDualMap σ dB m iB) (hex : DB.ExactMod σ m iB)
    {WA : Basis (Fin j) A (Module.Dual A (DA.omHT (σ.comp c.toRingHom)))} {MA : Basis (Fin k) A (DA.omHT σ)}
    {WB : Basis (Fin j) B (Module.Dual B (DB.omHT (σ.comp c.toRingHom)))} {MB : Basis (Fin k) B (DB.omHT σ)}
    {gA : Matrix (Fin N) (Fin j ⊕ Fin k) A} {gB : Matrix (Fin N) (Fin j ⊕ Fin k) B}
    (hgA : DA.IsFrame σ m iA WA MA gA) (hgB : DB.IsFrame σ m iB WB MB gB)
    (φA φB : Fin j → Dual Ω V) (hφA : ∀ a z, (WA a z : Ω) = φA a z) (hφB : ∀ a z, (WB a z : Ω) = φB a z)
    (T : Matrix (Fin j) (Fin j) Ω) (hT : ∀ a, φA a = ∑ a', T a' a • φB a')
    (S : Matrix (Fin k) (Fin k) Ω) (hS : ∀ a, (MA a : V) = ∑ a', S a' a • (MB a' : V)) :
    ∃ (X : Matrix (Fin j) (Fin k) Ω) (Z : Matrix (Fin N) (Fin j ⊕ Fin k) Ω),
      (∀ a b, Matrix.fromBlocks T X 0 S a b ∈ loc B u hu) ∧ (∀ a b, Z a b ∈ loc B u hu) ∧
      gA.map (fun a => (a : Ω)) = gB.map (fun a => (a : Ω)) * Matrix.fromBlocks T X 0 S + ((p : Ω) ^ m) • Z := by
  classical
  have huL : u ∈ loc B u hu := loc_of_mem hu
  have hpow_inv : ∀ (n : ℕ) (a : Ω), u ^ n * a ∈ B → a ∈ loc B u hu := fun n a h =>
    loc_of_pow n (loc_of_mem h)
  have hSmem : ∀ b a, S b a ∈ loc B u hu := by
    intro b a
    obtain ⟨n, hn⟩ := hM _ (MA a).2
    refine coef_mem (DB.omHT σ).subtype Subtype.val_injective MB (fun b => S b a) n ⟨_, hn⟩ ?_ b
    simp only [Submodule.subtype_apply]
    rw [hS a]
  have hφBloc : ∀ b w, w ∈ locM (DB.omHT (σ.comp c.toRingHom)) u hu → φB b w ∈ loc B u hu := by
    intro b w hw
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u ^ n • w ∈ DB.omHT (σ.comp c.toRingHom) := hw
    refine hpow_inv n _ ?_
    rw [← smul_eq_mul, ← map_smul, ← hφB b ⟨_, hn⟩]
    exact (WB b _).2
  have hTmem : ∀ b a, T b a ∈ loc B u hu := by
    intro b a
    refine coef_mem_dual (DB.omHT (σ.comp c.toRingHom)) (omHT_fg _ _) WB φB hφB (fun b => T b a) ?_ b
    intro z hz
    show (∑ b, T b a • φB b) z ∈ loc B u hu
    rw [← hT a]
    obtain ⟨n, hn⟩ := hW z hz
    have h1 : φA a (u⁻¹ ^ n • z) ∈ loc B u hu := by
      rw [← hφA a ⟨_, hn⟩]
      exact hAL _ (WA a _).2
    rw [map_smul, smul_eq_mul] at h1
    have h2 := (loc B u hu).mul_mem (pow_mem huL n) h1
    rwa [← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hu0), one_mul] at h2
  have hφAloc : ∀ a w, w ∈ locM (DB.omHT (σ.comp c.toRingHom)) u hu → φA a w ∈ loc B u hu := by
    intro a w hw
    rw [hT a, LinearMap.sum_apply]
    exact (loc B u hu).sum_mem fun b _ => by
      rw [LinearMap.smul_apply, smul_eq_mul]
      exact (loc B u hu).mul_mem (hTmem b a) (hφBloc b w hw)
  have hdiff : ∀ (σ' : E →+* Ω) (l : Fin N), ∃ w ∈ locM (DB.omHT σ') u hu,
      eigProj DB.ρΩ σ' (DA.h (Pi.single l 1)) = eigProj DB.ρΩ σ' (DB.h (Pi.single l 1)) + ((p : Ω) ^ m) • w := by
    intro σ' l
    obtain ⟨n, z, hz, hze⟩ := hh σ' (Pi.single l 1)
    have hun : u ^ n ≠ 0 := pow_ne_zero n hu0
    refine ⟨(u ^ n)⁻¹ • z, ⟨n, ?_⟩, ?_⟩
    · rwa [smul_smul, mul_inv_cancel₀ hun, one_smul]
    · rw [smul_comm, ← hze, smul_smul, inv_mul_cancel₀ hun, one_smul, map_sub]
      abel
  have hR : ∀ a : Fin k, ∃ (s : Fin j → Ω) (z : Fin N → Ω), (∀ b, s b ∈ loc B u hu) ∧
      (∀ l, z l ∈ loc B u hu) ∧ ∀ l, (gA l (Sum.inr a) : Ω) = ∑ b, (gB l (Sum.inl b) : Ω) * s b +
        ∑ b, (gB l (Sum.inr b) : Ω) * S b a + (p : Ω) ^ m * z l := by
    intro a
    obtain ⟨yA, hyA, hqA⟩ := hgA.2 a
    choose w hw hwe using hdiff σ
    have hyAloc : yA ∈ locM (DB.omHT σ) u hu := hM yA hyA
    refine frame_expand_loc hu0 DB hex hgB (fun l => gA l (Sum.inr a)) (fun l => hAL _ (gA l _).2)
      (fun b => S b a) (fun b => hSmem b a) (yA - ∑ l, (gA l (Sum.inr a) : Ω) • w l) ?_ ?_
    · exact (locM (DB.omHT σ) u hu).sub_mem hyAloc
        ((locM (DB.omHT σ) u hu).sum_mem fun l _ => locM_smul (hAL _ (gA l _).2) (hw l))
    · have hq' : ∑ l, (gA l (Sum.inr a) : Ω) • eigProj DB.ρΩ σ (DA.h (Pi.single l 1)) =
          (MA a : V) + (p : Ω) ^ m • yA := by
        have h1 := hqA
        simp only [HTChart.q, hρ] at h1
        rw [show ((p : Ω) ^ m) • yA = ((p : A) ^ m) • yA by
          change _ = (((p : A) ^ m : A) : Ω) • yA
          push_cast
          rfl]
        exact h1
      simp only [hwe, smul_add, Finset.sum_add_distrib] at hq'
      rw [← hS a, smul_sub, Finset.smul_sum]
      simp only [smul_comm ((p : Ω) ^ m)]
      rw [← add_sub_assoc, ← hq']
      abel
  have hinj : Function.Injective (algebraMap B Ω) := Subtype.val_injective
  obtain ⟨G, H, Zg, -, hG, hGH, -⟩ := PositivityTheory.HtPt.Ga.gram_unit B Ω hinj E c hc p R N V DB σ dB
    (fun a => ⟨⟨_, hσ a⟩, rfl⟩) hdB
  have hgram : ∀ l l', DA.gram σ dA l l' = DB.gram σ dB l l' := by
    intro l l'
    simp only [HTChart.gram, he]
    rw [show algebraMap A Ω dA = algebraMap B Ω dB from hd]
  have hΓ : ∀ l l', DB.gram σ dB l l' ∈ loc B u hu := fun l l' => by
    rw [← hG]
    exact loc_of_mem (G l l').2
  have hGH' : G.map (algebraMap B Ω) * H.map (algebraMap B Ω) =
      1 + ((p : Ω) ^ m * (p : Ω) ^ (R - m)) • Zg.map (algebraMap B Ω) := by
    rw [← pow_add, Nat.add_sub_cancel' hm, ← Matrix.map_mul, hGH]
    ext i l
    simp [Matrix.one_apply, apply_ite]
  choose hYA zA xA hA using fun a l' => exists_sum_gram_eq_add_prime_pow_mul DA hiA hgA a l'
  choose hYB zB xB hB using fun b l' => exists_sum_gram_eq_add_prime_pow_mul DB hiB hgB b l'
  choose wc hwc hwce using hdiff (σ.comp c.toRingHom)
  have hL : ∀ a : Fin j, ∃ z : Fin N → Ω, (∀ l, z l ∈ loc B u hu) ∧
      ∀ l, (gA l (Sum.inl a) : Ω) = ∑ b, (gB l (Sum.inl b) : Ω) * T b a + (p : Ω) ^ m * z l := by
    intro a
    let v : Fin N → Ω := fun l => (gA l (Sum.inl a) : Ω) - ∑ b, (gB l (Sum.inl b) : Ω) * T b a
    let ζ : Fin N → Ω := fun l' => φA a (wc l') + zA a l' + ∑ l, (xA a l' l : Ω) * DB.gram σ dB l l' -
      ∑ b, T b a * (zB b l' + ∑ l, (xB b l' l : Ω) * DB.gram σ dB l l')
    have hvmem : ∀ l, v l ∈ loc B u hu := fun l =>
      (loc B u hu).sub_mem (hAL _ (gA l _).2)
        ((loc B u hu).sum_mem fun b _ => (loc B u hu).mul_mem (loc_of_mem (gB l _).2) (hTmem b a))
    have hζmem : ∀ l', ζ l' ∈ loc B u hu := by
      intro l'
      refine (loc B u hu).sub_mem ((loc B u hu).add_mem ((loc B u hu).add_mem (hφAloc a _ (hwc l'))
        (hAL _ (zA a l').2)) ((loc B u hu).sum_mem fun l _ =>
          (loc B u hu).mul_mem (hAL _ (xA a l' l).2) (hΓ l l'))) ?_
      exact (loc B u hu).sum_mem fun b _ => (loc B u hu).mul_mem (hTmem b a)
        ((loc B u hu).add_mem (loc_of_mem (zB b l').2) ((loc B u hu).sum_mem fun l _ =>
          (loc B u hu).mul_mem (loc_of_mem (xB b l' l).2) (hΓ l l')))
    have hvec : Matrix.vecMul v (G.map (algebraMap B Ω)) = ((p : Ω) ^ m) • ζ := by
      funext l'
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hG, Pi.smul_apply, smul_eq_mul]
      have eA := hA a l'
      simp only [hgram] at eA
      rw [hφA a] at eA
      have hYeq : ((⟨_, hYA a l'⟩ : DA.omHT (σ.comp c.toRingHom)) : V) =
          eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1)) + ((p : Ω) ^ m) • wc l' := by
        rw [← hwce l', ← hρ]
      rw [hYeq, map_add (f := _), map_smul, smul_eq_mul] at eA
      have eB : ∀ b, ∑ l, (gB l (Sum.inl b) : Ω) * DB.gram σ dB l l' =
          φB b (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) + (p : Ω) ^ m * zB b l' +
            (p : Ω) ^ m * ∑ l, (xB b l' l : Ω) * DB.gram σ dB l l' := by
        intro b
        rw [hB b l', hφB b]
      have hφAY : φA a (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) =
          ∑ b, T b a * φB b (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) := by
        rw [hT a, LinearMap.sum_apply]
        rfl
      have hsplit : ∑ l, v l * DB.gram σ dB l l' = ∑ l, (gA l (Sum.inl a) : Ω) * DB.gram σ dB l l' -
          ∑ b, T b a * ∑ l, (gB l (Sum.inl b) : Ω) * DB.gram σ dB l l' := by
        simp only [v, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
      have hsum : ∑ b, T b a * ∑ l, (gB l (Sum.inl b) : Ω) * DB.gram σ dB l l' =
          ∑ b, T b a * φB b (eigProj DB.ρΩ (σ.comp c.toRingHom) (DB.h (Pi.single l' 1))) +
            (p : Ω) ^ m * ∑ b, T b a * (zB b l' + ∑ l, (xB b l' l : Ω) * DB.gram σ dB l l') := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by rw [eB b]; ring
      rw [hsplit, hsum, eA, hφAY]
      simp only [ζ]
      ring
    obtain ⟨z, hz, hvz⟩ := cancel_gram (loc B u hu) (G.map (algebraMap B Ω)) (H.map (algebraMap B Ω))
      (Zg.map (algebraMap B Ω)) ((p : Ω) ^ m) ((p : Ω) ^ (R - m)) (pow_mem (natCast_mem _ p) _)
      (fun i l => loc_of_mem (H i l).2) (fun i l => loc_of_mem (Zg i l).2) hGH' v ζ hvmem hζmem hvec
    refine ⟨z, hz, fun l => ?_⟩
    have h1 := congrFun hvz l
    simp only [v, Pi.smul_apply, smul_eq_mul] at h1
    linear_combination h1
  choose sR zR hsR hzR hRe using hR
  choose zL hzL hLe using hL
  refine ⟨Matrix.of fun b a => sR a b, Matrix.of fun l c => Sum.elim (fun a => zL a l) (fun a => zR a l) c,
    ?_, ?_, ?_⟩
  · rintro (a | a) (b | b)
    · simpa using hTmem a b
    · simpa using hsR b a
    · simpa using (loc B u hu).zero_mem
    · simpa using hSmem a b
  · rintro l (a | a)
    · simpa using hzL a l
    · simpa using hzR a l
  · ext l (a | a)
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, hLe a l]
    · simp [Matrix.mul_apply, Fintype.sum_sum_type, hRe a l]

end PositivityTheory.HtPt.Ge
end

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Ge

theorem chartMon_ne_zero {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {s : ∀ k, J k} (hs : mseg y s ≠ 0) (a : K → ℤ) : chartMon y s a ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hs k hk)

theorem trivflag_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [CharZero Ω] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R m j k : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module Ω V] (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω c p R (j + k) V) (σ : E →+* Ω) (d : Ω) (dd : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, chartRing o (mseg y) s.1) (i : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)) →ₗ[chartRing o (mseg y) s.1] (Fin (j + k) → chartRing o (mseg y) s.1)) (bW : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin j) (chartRing o (mseg y) s.1) (Module.Dual (chartRing o (mseg y) s.1) ((Dc s).omHT (σ.comp c.toRingHom)))) (bM : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, Module.Basis (Fin k) (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) (wW : Fin j → Module.Dual Ω V) (wM : Fin k → V) (b : Fin (j + k) → K → ℤ), (∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, IsFractionRing (chartRing o (mseg y) s.1) Ω) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) (a : 𝓞 E), σ' (a : E) ∈ chartRing o (mseg y) s.1) → (∀ s, (dd s : Ω) = d ∧ GeneratesDiff σ (dd s)) → (∀ s t, (Dc s).ρΩ = (Dc t).ρΩ ∧ (Dc s).e = (Dc t).e) → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω), ∀ x ∈ (Dc s).omHT σ', ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).omHT σ') → (∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ (Dc t).omHT σ', (mseg y s.1 / mseg y t.1) ^ n • eigProj (Dc t).ρΩ σ' ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ m) • z) → (∀ s, (Dc s).IsDualMap σ (dd s) m (i s) ∧ (Dc s).ExactMod σ m (i s) ∧ ∀ x, (Dc s).q σ x ∈ (Dc s).omHT σ) → m ≤ R → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin j → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.castAdd k a)) ∧ ∀ z : (Dc s).omHT (σ.comp c.toRingHom), ((bW s a z : chartRing o (mseg y) s.1) : Ω) = ∑ a', cf a' * wW a' z) → (∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) a, ∃ cf : Fin k → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = chartMon y s.1 (b (Fin.natAdd j a)) ∧ ((bM s a : (Dc s).omHT σ) : V) = ∑ a', cf a' • wM a') → Num.TrivFlagMod o ((p : o) ^ m) y (j + k) b := by
  intro o _ Ω _ _ K _ J _ y _ E _ _ c hc p R m j k _ V _ _ Dc σ d dd i bW bM wW wM b hfr hint hdd hρe hM hh hi hm
    hW hMb
  classical
  have hfe := fun s => frame_exists _ Ω Subtype.val_injective E c hc p R (j + k) V (Dc s) σ m j k (i s) (bW s) (bM s)
    finSumFinEquiv (hi s).2.2 (hi s).2.1
  choose g hg using fun s => (hfe s).1
  choose cf cf1 cf2 cf3 using hW
  have hϖ : algebraMap o Ω ((p : o) ^ m) = (p : Ω) ^ m := by simp
  refine ⟨fun s => if h : mseg y s ≠ 0 then
    ((g ⟨s, h⟩).map (fun a => (a : Ω))).submatrix id finSumFinEquiv.symm else 0, fun s hs => ?_,
    fun s t hs ht => ?_⟩
  · simp only [dif_pos hs]
    refine ⟨fun a a' => (g ⟨s, hs⟩ _ _).2, ?_⟩
    obtain ⟨h, r, e⟩ := (hfe ⟨s, hs⟩).2 _ (hg ⟨s, hs⟩)
    refine ⟨h, h.2, r, r.2, ?_⟩
    have := congrArg (chartRing o (mseg y) s).val e
    rw [map_mul, AlgHom.map_det] at this
    rw [hϖ, Matrix.submatrix_map]
    simpa using this
  · simp only [dif_pos hs, dif_pos ht, hϖ]
    haveI := hfr ⟨t, ht⟩
    have hu := div_mem_chartRing (o := o) (mseg y) t s
    have hu0 : mseg y s / mseg y t ≠ 0 := div_ne_zero hs ht
    have hAL : ∀ a ∈ chartRing o (mseg y) s, a ∈ loc _ _ hu := fun a ha =>
      exists_pow_mul_mem_chartRing (mseg y) s t hs ha
    obtain ⟨T, T1, T2, T3⟩ := tri wW (fun a => ∑ a', cf ⟨s, hs⟩ a a' • wW a') (fun a => ∑ a', cf ⟨t, ht⟩ a a' • wW a')
      (fun a => chartMon y s (b (Fin.castAdd k a))) (fun a => chartMon y t (b (Fin.castAdd k a)))
      (fun a => chartMon_ne_zero ht _) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩) (fun a => ⟨_, cf1 _ a, cf2 _ a, rfl⟩)
    obtain ⟨S, S1, S2, S3⟩ := tri wM (fun a => (bM ⟨s, hs⟩ a : V)) (fun a => (bM ⟨t, ht⟩ a : V))
      (fun a => chartMon y s (b (Fin.natAdd j a))) (fun a => chartMon y t (b (Fin.natAdd j a)))
      (fun a => chartMon_ne_zero ht _) (hMb ⟨s, hs⟩) (hMb ⟨t, ht⟩)
    obtain ⟨X, Z, hU, hZ, e⟩ := overlap (hu := hu) hc hu0 hAL (Dc ⟨s, hs⟩) (Dc ⟨t, ht⟩) hm (hint ⟨t, ht⟩ σ)
      (dd ⟨s, hs⟩) (dd ⟨t, ht⟩) ((hdd _).1.trans (hdd _).1.symm) (hdd _).2 (hρe _ _).1 (hρe _ _).2
      (hM ⟨s, hs⟩ ⟨t, ht⟩ σ) (by rw [inv_div]; exact hM ⟨t, ht⟩ ⟨s, hs⟩ _) (hh ⟨s, hs⟩ ⟨t, ht⟩)
      (hi _).1 (hi _).1 (hi _).2.1 (hg _) (hg _) _ _
      (fun a z => by rw [cf3]; simp) (fun a z => by rw [cf3]; simp) T T3 S S3
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := (((Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hU a a')).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hZ a a'))).and (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun a' =>
      loc_ev (hAL _ (g ⟨s, hs⟩ a a').2))).exists
    refine ⟨n, (mseg y s / mseg y t) ^ n •
      (Matrix.fromBlocks T X 0 S).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      (mseg y s / mseg y t) ^ n • Z.submatrix id finSumFinEquiv.symm, fun a a' => h1 _ _, fun a a' => h2 _ _,
      fun a a' h => ?_, fun a => ?_, fun a a' => h3 _ _, ?_⟩
    · rw [Matrix.smul_apply, Matrix.submatrix_apply]
      refine smul_eq_zero_of_right _ ?_
      induction a using Fin.addCases with
      | left a =>
        induction a' using Fin.addCases with
        | left a' => simpa using T1 a a' h
        | right a' =>
          have : j + (a' : ℕ) < a := h
          omega
      | right a =>
        induction a' using Fin.addCases with
        | left a' => simp
        | right a' => simpa using S1 a a' (by simpa using h)
    · rw [Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
      congr 1
      induction a using Fin.addCases with
      | left a => simpa using T2 a
      | right a => simpa using S2 a
    · rw [Matrix.mul_smul, smul_comm, ← smul_add, Matrix.submatrix_mul_equiv, e]
      rfl

end PositivityTheory.HtPt.Ge
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FinrankDualEqOfProjective
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Ge

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  classical
  haveI := Module.finitePresentation_of_projective A M
  let S := nonZeroDivisors A
  let F := Localization S
  let f := LocalizedModule.mkLinearMap S M
  let g := Algebra.linearMap A F
  have e1 : finrank A (Module.Dual A M) = finrank A (LocalizedModule S M →ₗ[F] F) :=
    (IsLocalizedModule.finrank_eq S (IsLocalizedModule.mapExtendScalars S f g F) le_rfl).symm
  rw [e1, ← IsLocalization.finrank_eq F S le_rfl, Subspace.dual_finrank_eq,
    IsLocalization.finrank_eq F S le_rfl, IsLocalizedModule.finrank_eq S f le_rfl]

theorem ringOfIntegers_mem_range (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {E : Type} [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

def qLin {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem chart_sequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hκ htest hproj'
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right κ _) hκ
  have h1 := PositivityTheory.HtPt.Gc.chart_ii A K E c hc p R N Ω D κ hκR hproj' htest
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hint : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hr⟩ :=
    PositivityTheory.HtPt.Ga.dual_map A K hinj E c hc p R N Ω D κ σ d m hint hd hκ h1.2 hP2
  obtain ⟨-, -, hsurj⟩ := PositivityTheory.HtPt.Ga.q_surj A K hinj E c hc p R N Ω D κ σ m (hint σ) hκ h1.2
  have hcz := PositivityTheory.HtPt.Gd.chart_comp_zero A K E c hc p R N Ω D κ σ d d' m i hκ hd hd' h1.2
    hP1 hP2 htest hi
  refine ⟨i, hi, hr i hi, ?_, hsurj⟩
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu⟩ := hu
      refine ⟨0, (↑u⁻¹ : A) ^ m • x, ?_⟩
      rw [map_zero, zero_add, smul_smul, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D σ)
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) :=
        Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D _)
      let q' : (Fin N → A) →ₗ[A] D.omHT σ :=
        (qLin D σ).codRestrict (D.omHT σ) (PositivityTheory.HtPt.Ga.q_mem D σ)
      have hrank : finrank A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) +
          finrank A (D.omHT σ) = N := by
        rw [finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom)), add_comm]
        exact PositivityTheory.HtPt.Gb.chart_rank A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 htest
      obtain ⟨rr, hrr⟩ := hr i hi
      obtain ⟨w, x', hx⟩ := PositivityTheory.HtPt.Gd.split_exact A
        (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m) i rr q' hrank hrr
        (fun z => by
          obtain ⟨x0, y', hy', h⟩ := hsurj z.1 z.2
          exact ⟨x0, ⟨y', hy'⟩, Subtype.ext h⟩)
        (fun w => by
          obtain ⟨y0, hy0, h0⟩ := hcz w
          exact ⟨⟨y0, hy0⟩, Subtype.ext h0⟩)
        x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      exact ⟨w, x', hx⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y0, hy0, h0⟩ := hcz w
    refine ⟨y0 + D.q σ x', (D.omHT σ).add_mem hy0 (PositivityTheory.HtPt.Ga.q_mem D σ x'), ?_⟩
    have hq : ∀ z, D.q σ z = qLin D σ z := fun _ => rfl
    rw [hq, map_add (f := _), map_smul, ← hq, ← hq, h0, smul_add]
    all_goals rfl

end PositivityTheory.HtPt.Ge
end
end

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Ge

theorem triv_flag_mod_of_hodge_tate_free_of_root_lines (hb : FarguesHodgeTate → PointHT)
    (hl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), ∃ (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc ∧ ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (κ : chartRing o (mseg y) s.1), PointHT → IsCp p (κ : Ω) → (Dc s).HasTestPoints κ) :
    FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), HTFree 𝔐 p → Fl.RootLines xdeg e → ∀ τ : CMType H, Num.TrivFlagMod o ((p : o) ^ (𝔐.R p - 2)) y (D.p + D.q) (fun i => xdeg (τ, i)) := by
  intro hF E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq o _ _ ho Fl xdeg e hfree hroot τ
  have hgen := Hcptgen.hcpt_generic E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho
  haveI : CharZero Ω := hgen.1
  have hA := hgen.2.2.2.2.2.2
  obtain ⟨Dc, hfam, htest⟩ := hl E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho
  obtain ⟨hproj, hdiff, κ, hκ, hκA⟩ := Famproj.family_proj E H D l Xo c O β Y S Ω K J y 𝔐 p hpS hpq o ho Dc hfam hfree
  have hPHT : PointHT := hb hF
  have hR : 4 ≤ 𝔐.R p := 𝔐.R_ge p hpS
  have hc : ∀ x : E, cmConj E (cmConj E x) = x := fun x => by simp
  let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F (c.conj τ.1))
  have hσ : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
  obtain ⟨d, hd⟩ := hdiff σ
  obtain ⟨d', hd'⟩ := hdiff (σ.comp (cmConj E).toRingHom)
  obtain ⟨wW, wM, hb⟩ := Flagb.chart_flag_bases E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho Dc Fl xdeg e τ σ d hfam hfree hroot hσ hd
  choose dd hdd using hd
  choose dd' hdd' using hd'
  choose bW bM hbW hbM using hb
  have hρe : ∀ s t, (Dc s).ρΩ = (Dc t).ρΩ ∧ (Dc s).e = (Dc t).e := by
    intro s t
    refine ⟨?_, hfam.e_eq s t⟩
    ext a w : 2
    rw [hfam.act s, hfam.act t]
  have hint : ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) (a : 𝓞 E), σ' (a : E) ∈ chartRing o (mseg y) s.1 := by
    intro s σ' a
    obtain ⟨hN, hIC, hFR, -⟩ := hA s.1 s.2
    obtain ⟨b, hb⟩ := GlobalTheory.T.number_field_integers_in_integrally_closed (chartRing o (mseg y) s.1) Ω E σ' a
    rw [← hb]; exact b.2
  have hcs : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ i, (Dc s).IsDualMap σ (dd s) (𝔐.R p - 2) i ∧ (Dc s).ExactMod σ (𝔐.R p - 2) i ∧ (∀ x, (Dc s).q σ x ∈ (Dc s).omHT σ) ∧ ∀ x ∈ (Dc s).om, ((p : Ω) ^ 2) • x ∈ (Dc s).om' := by
    intro s
    obtain ⟨hN, hIC, hFR, -⟩ := hA s.1 s.2
    let κs : chartRing o (mseg y) s.1 := ⟨κ, hκA s⟩
    have hk2 : κs ∣ (p : chartRing o (mseg y) s.1) ^ 2 := GlobalTheory.T.cp_element_divides_prime_sq (chartRing o (mseg y) s.1) Ω p κs hκ
    have hkR : κs * (p : chartRing o (mseg y) s.1) ^ (𝔐.R p - 2) ∣ (p : chartRing o (mseg y) s.1) ^ (𝔐.R p) := by
      have : (p : chartRing o (mseg y) s.1) ^ (𝔐.R p) = (p : chartRing o (mseg y) s.1) ^ 2 * (p : chartRing o (mseg y) s.1) ^ (𝔐.R p - 2) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; exact mul_dvd_mul_right hk2 _
    have hcs := chart_sequence (chartRing o (mseg y) s.1) Ω E (cmConj E) hc p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) (Dc s) κs (𝔐.R p - 2) hkR (htest s κs hPHT hκ) (hproj s).1
    obtain ⟨i, hi1, hi2⟩ := hcs.2 σ (dd s) (dd' s) (hdd s).2 (hdd' s).2 ((hproj s).2 σ) ((hproj s).2 _)
    have hq := Ga.q_surj (chartRing o (mseg y) s.1) Ω Subtype.val_injective E (cmConj E) hc p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) (Dc s) κs σ (𝔐.R p - 2) (fun a => ⟨⟨_, hint s σ a⟩, rfl⟩) hkR hcs.1.2
    refine ⟨i, hi1, hi2, hq.1, ?_⟩
    intro x hx
    obtain ⟨r, hr⟩ := hk2
    have h1 := (Dc s).om'.smul_mem r (hcs.1.2 x hx)
    have h2 : r • κs • x = ((p : Ω) ^ 2) • x := by
      clear hgen hA hbW hbM hcs hq hi1 hi2 h1 htest hproj
      rw [smul_smul, mul_comm r, ← hr, ← algebraMap_smul Ω]
      simp
    rwa [h2] at h1
  choose i hi using hcs
  have hom : ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}), ∀ x ∈ (Dc s).om, ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • x ∈ (Dc t).om :=
    fun s t x hx => GlobalTheory.T.hodge_component_integral_at_prime_in_S E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho Dc hfam s t x
      (fun q hs _ hz => (hfam.om_iff s x).1 hx q hs hz)
  have hh : ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (x : Fin (D.p + D.q) → 𝓞 E), ∃ n : ℕ, ∃ w ∈ (Dc t).om, (mseg y s.1 / mseg y t.1) ^ n • ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ (𝔐.R p)) • w := by
    intro s t x
    have hp0 : ((p : Ω) ^ (𝔐.R p)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    obtain ⟨n, hn⟩ := GlobalTheory.T.hodge_component_integral_at_prime_in_S E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho Dc hfam s t (((p : Ω) ^ (𝔐.R p))⁻¹ • ((Dc s).h x - (Dc t).h x)) (by
      intro q hs ht hz
      obtain ⟨w, hw, he⟩ := hfam.glue s t q hs ht hz x
      rw [he, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul Ω, smul_smul, Nat.cast_pow, inv_mul_cancel₀ hp0, one_smul]
      exact hw)
    refine ⟨n, _, hn, ?_⟩
    rw [smul_comm ((p : Ω) ^ (𝔐.R p)) ((mseg y s.1 / mseg y t.1) ^ n), smul_smul ((p : Ω) ^ (𝔐.R p)) ((p : Ω) ^ (𝔐.R p))⁻¹, mul_inv_cancel₀ hp0, one_smul]
  have hovl1 := GlobalTheory.T.hodge_chart_transition_integral o Ω K J y E (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) Dc hom hh (fun s t => (hρe s t).1) (fun s t a ha => GlobalTheory.T.chart_ring_mem_after_monomial_scaling o Ω K J y s.1 t.1 s.2 t.2 a ha)
  have hovl2 : ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (σ' : E →+* Ω) x, ∃ n : ℕ, ∃ z ∈ (Dc t).omHT σ', (mseg y s.1 / mseg y t.1) ^ n • eigProj (Dc t).ρΩ σ' ((Dc s).h x - (Dc t).h x) = ((p : Ω) ^ (𝔐.R p - 2)) • z := by
    intro s t σ' x
    obtain ⟨n, w, hw, he⟩ := hh s t x
    refine ⟨n, eigProj (Dc t).ρΩ σ' (((p : Ω) ^ 2) • w), ⟨_, (hi t).2.2.2 w hw, rfl⟩, ?_⟩
    rw [← LinearMap.map_smul, he, ← LinearMap.map_smul, smul_smul, ← pow_add]
    congr 3
    omega
  exact trivflag_charts o Ω K J y E (cmConj E) hc p (𝔐.R p) (𝔐.R p - 2) D.p D.q (Module.Dual Ω 𝔐.Li) Dc σ d dd i bW bM wW wM (fun i => xdeg (τ, i)) (fun s => (hA s.1 s.2).2.2.1) hint (fun s => hdd s) hρe hovl1 hovl2 (fun s => ⟨(hi s).1, (hi s).2.1, (hi s).2.2.1⟩) (Nat.sub_le _ _) (fun s a => hbW s a) (fun s a => hbM s a)

end PositivityTheory.HtPt.Ge
