module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagHeight

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEigenOpDiscr
open GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich.Sep

open NumberField Matrix

private theorem exists_discr_dual_basis_of_discr_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] (E : Type) [Field E]
    [NumberField E] (ω : Module.Basis ι ℤ (𝓞 E)) (hd : Algebra.discr ℤ ω ≠ 0) :
    ∃ b : ι → 𝓞 E, ∑ i, ω i * b i = ((Algebra.discr ℤ ω : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∀ i, x * b i = ∑ j, ((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j := by
  obtain ⟨T, hT⟩ : ∃ T, T = Algebra.traceMatrix ℤ ω := ⟨_, rfl⟩
  have hTsymm : ∀ j k, T j k = T k j := fun j k => by
    simp only [hT, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [mul_comm]
  have hAT : T.adjugate * T = Algebra.discr ℤ ω • (1 : Matrix ι ι ℤ) := by
    rw [Matrix.adjugate_mul, Algebra.discr_def, hT]

  have e1 : ∀ (c : ℤ) (y : 𝓞 E), Algebra.trace ℤ (𝓞 E) ((c : 𝓞 E) * y) =
      c * Algebra.trace ℤ (𝓞 E) y := by
    intro c y
    rw [← zsmul_eq_mul, map_zsmul, smul_eq_mul]
  have htrω : ∀ z : 𝓞 E, ∀ k, Algebra.trace ℤ (𝓞 E) (z * ω k) = ∑ j, ω.repr z j * T j k := by
    intro z k
    conv_lhs => rw [← ω.sum_repr z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_zsmul, smul_eq_mul, hT, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]

  obtain ⟨b, hb⟩ : ∃ b : ι → 𝓞 E, b = fun i => ∑ k, (T.adjugate i k : 𝓞 E) * ω k := ⟨_, rfl⟩
  have hDB : ∀ z : 𝓞 E, ∀ i, Algebra.trace ℤ (𝓞 E) (z * b i) = Algebra.discr ℤ ω * ω.repr z i := by
    intro z i
    calc Algebra.trace ℤ (𝓞 E) (z * b i)
        = ∑ k, T.adjugate i k * Algebra.trace ℤ (𝓞 E) (z * ω k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [hb, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_left_comm, e1]
      _ = ∑ k, T.adjugate i k * ∑ j, ω.repr z j * T j k := by simp only [htrω]
      _ = ∑ j, ω.repr z j * (T.adjugate * T) i j := by
          simp only [Matrix.mul_apply, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [hTsymm j k]
          ring
      _ = Algebra.discr ℤ ω * ω.repr z i := by
          rw [hAT]
          simp [Matrix.smul_apply, Matrix.one_apply]
          try ring
  have hnd : ∀ s : 𝓞 E, (∀ l, Algebra.trace ℤ (𝓞 E) (s * ω l) = 0) → s = 0 := by
    intro s hs
    have hb0 : ∀ i, Algebra.trace ℤ (𝓞 E) (s * b i) = 0 := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hb, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [mul_left_comm, e1, hs, mul_zero]
    have hr : ∀ i, ω.repr s i = 0 := fun i => by
      have h := hDB s i
      rw [hb0 i] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hd
    rw [← ω.sum_repr s]
    simp [hr]
  have htr : ∀ y : 𝓞 E, Algebra.trace ℤ (𝓞 E) y = ∑ i, ω.repr (y * ω i) i := by
    intro y
    rw [Algebra.trace_eq_matrix_trace ω, Matrix.trace]
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  refine ⟨b, ?_, ?_⟩
  · apply sub_eq_zero.mp
    apply hnd
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, map_sub, Finset.sum_mul, map_sum, e1, htr (ω l)]
    have h : ∀ i, Algebra.trace ℤ (𝓞 E) (ω i * b i * ω l) =
        Algebra.discr ℤ ω * ω.repr (ω l * ω i) i := fun i => by
      rw [mul_right_comm, hDB, mul_comm (ω i)]
    simp only [h, Finset.mul_sum, sub_self]
  · intro x i
    apply sub_eq_zero.mp
    apply hnd
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    have h1 : Algebra.trace ℤ (𝓞 E) (x * b i * ω l) = Algebra.discr ℤ ω * ω.repr (x * ω l) i := by
      rw [mul_right_comm, hDB]
    have h2 : ∀ j, Algebra.trace ℤ (𝓞 E) (((ω.repr (x * ω j) i : ℤ) : 𝓞 E) * b j * ω l) =
        ω.repr (x * ω j) i * (Algebra.discr ℤ ω * ω.repr (ω l) j) := fun j => by
      rw [mul_assoc, e1, mul_comm (b j), hDB]
    simp only [h1, h2, ω.repr_self, Finsupp.single_apply]
    simp
    try ring

theorem exists_sep_element (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∑ i, a i * b i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ x : 𝓞 E, ∃ m : Matrix (Fin n) (Fin n) ℤ, (∀ i, x * a i = ∑ j, (m i j : 𝓞 E) * a j) ∧
        ∀ i, x * b i = ∑ j, (m j i : 𝓞 E) * b j := by
  classical
  let ω := (RingOfIntegers.basis E).reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E)))
  have hdisc : Algebra.discr ℤ ω = discr E := by
    simp only [ω, Module.Basis.coe_reindex]
    rw [Algebra.discr_reindex]
  obtain ⟨b, hsum, hb⟩ := exists_discr_dual_basis_of_discr_ne_zero E ω (by rw [hdisc]; exact discr_ne_zero E)
  refine ⟨_, ω, b, by rw [← hdisc]; exact hsum, fun x =>
    ⟨fun i j => ω.repr (x * ω i) j, fun i => ?_, fun i => hb x i⟩⟩
  conv_lhs => rw [← ω.sum_repr (x * ω i)]
  simp [zsmul_eq_mul]

theorem exists_eigen_op_discr (E : Type) [Field E] [NumberField E] :
    ∃ (n : ℕ) (a b : Fin n → 𝓞 E), ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]
      (ρ : 𝓞 E →+* Module.End R V) (σ : 𝓞 E →+* R),
      (∀ v, ∑ i, σ (b i) • ρ (a i) v ∈ eigSp ρ σ) ∧
        ∀ v ∈ eigSp ρ σ, ∑ i, σ (b i) • ρ (a i) v = ((discr E : ℤ) : R) • v := by
  obtain ⟨n, a, b, hsum, hm⟩ := exists_sep_element E
  refine ⟨n, a, b, fun R _ V _ _ ρ σ => ⟨fun v => ?_, fun v hv => ?_⟩⟩
  · rw [eigSp, Submodule.mem_iInf]
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply]
    obtain ⟨m, hma, hmb⟩ := hm x
    have L : ∀ i, ρ x (ρ (a i) v) = ∑ j, (m i j : R) • ρ (a j) v := fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Module.End.mul_apply, ← map_mul, hma i, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_intCast, Module.End.mul_apply, Module.End.intCast_apply,
        Int.cast_smul_eq_zsmul]
    have Rr : ∀ j, σ x * σ (b j) = ∑ i, (m i j : R) * σ (b i) := fun j => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, hmb j, map_sum]
      simp [map_mul, map_intCast]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    simp only [map_smul, L, Finset.smul_sum, smul_smul, Rr, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  · have hv' : ∀ x, ρ x v = σ x • v := by
      intro x
      rw [eigSp, Submodule.mem_iInf] at hv
      have h := hv x
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
      simpa using h
    simp only [hv', smul_smul, ← Finset.sum_smul]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_intCast σ, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Sandwich.Sep
end
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}


set_option backward.isDefEq.respectTransparency false in
theorem lat_act_of_model_rf (𝔐 : HodgeCpt Y SS y) (q : Cpt 𝔐.ξ) (x : 𝓞 E) (e : 𝔐.Li) (he : e ∈ 𝔐.M.lat q) :
    𝔐.ρ x e ∈ 𝔐.M.lat q := by
  have := 𝔐.t.act.hom x
  rw [GlobalTheory.CompanionTheory.Ar.LieModel.mem_lat_iff] at he ⊢
  obtain ⟨v, hv⟩ := he
  obtain ⟨ht, hpt⟩ := (GlobalTheory.CompanionTheory.Ar.LieModel.extends_iff _ _ _ _).mp hv
  refine ⟨v ≫ 𝔐.t.act.act x, (GlobalTheory.CompanionTheory.Ar.LieModel.extends_iff _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · rw [GlobalTheory.CompanionTheory.Ar.LieTangent.isTanAt_iff] at ht ⊢
    rw [← Category.assoc, ht, CategoryTheory.MonObj.one_comp]
  · rw [𝔐.act x e, hpt, Category.assoc]

end Act


set_option backward.isDefEq.respectTransparency false in
theorem isUnit_int_of_inFibre_rf {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z)
    {p : ℕ} (hp : p.Prime) (hf : InFibre ξ p ⟨centre z, h⟩) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : IsUnit (d : R) := by
  by_contra hnd
  unfold GlobalTheory.CompanionTheory.Ar.InFibre GlobalTheory.CompanionTheory.Ar.unitAt GlobalTheory.CompanionTheory.Ar.regAt at hf
  have key : ∀ {S : Type} [CommRing S] [IsLocalRing S], IsCoprime (p : ℤ) d →
      ¬ IsUnit (p : S) → ¬ IsUnit (d : S) → False := by
    intro S _ _ hpd hp' hd'
    obtain ⟨a, b, hab⟩ := hpd
    have h1 : (a : S) * (p : S) + (b : S) * (d : S) = 1 := by
      have := congrArg (Int.cast : ℤ → S) hab
      push_cast at this
      exact this
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h' | h'
    · exact hp' (isUnit_of_mul_isUnit_right h')
    · exact hd' (isUnit_of_mul_isUnit_right h')
  refine key (S := X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z))
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hd) ?_ ?_
  · rintro ⟨u, hu⟩
    apply hf
    have hgp : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (p : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z)) = (p : Ω) :=
      map_natCast _ p
    have hmul : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (↑u⁻¹ : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z)) * (p : Ω) = 1 := by
      rw [← hgp, ← map_mul, ← hu, Units.inv_mul, map_one]
    refine ⟨right_ne_zero_of_mul_eq_one hmul, RingHom.mem_range.mpr ⟨_, hgp⟩, RingHom.mem_range.mpr ⟨(↑u⁻¹ : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z)), ?_⟩⟩
    exact eq_inv_of_mul_eq_one_left hmul
  · intro hu
    exact hnd (by simpa using hu.map (Scheme.stalkClosedPointTo z).hom)

theorem fib_eq_lieEig_rf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hgood la T io e y evT zT t hint zV hread
    hpS hdisc EC _ _ _ _ MC ρC hact s σ hσ
  have hp : p.Prime := Fact.out
  have hgen : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hsm : Smooth Or.𝔐.t.G.hom := Or.𝔐.t.semi.smooth
  have h₀ : genPt Or.𝔐.ξ ⤳ centre zV := Or.𝔐.all _
  have h₁ : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  have hF : InFibre Or.𝔐.ξ p ⟨centre zV, h₀⟩ :=
    GlobalTheory.T.root_origin_frame_nonarchimedean E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hgood la T io e y evT zT t hint zV hread
  have hV : Or.𝔐.V s ⟨centre zV, h₀⟩ = Or.𝔐.dR s ⟨centre zV, h₀⟩ :=
    Lat.patch_of_not SS _ _ fun r hr hfr =>
      Lat.not_inFibre_of_coprime _ ((Nat.coprime_primes hp (Or.𝔐.S_prime r hr)).2
        fun hne => hpS (hne ▸ hr)) hF hfr
  obtain ⟨ev', hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring Or.𝔐.X Or.𝔐.t.G RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M T.Fr (gen T zV) h₁ EC MC
    hgen hsm

  have hσ' : ∀ a, ValAt Or.𝔐.ξ (gen T zV) (Or.𝔐.emb s a) (algebraMap T.V T.Fr (σ a)) := fun a =>
    TopFibre.valAt_comp (algebraMap T.V T.Fr) (hσ a) h₁
  have P0 : Or.𝔐.M.ValAt (gen T zV) 0 (MC.pt 0) :=
    (hev1 _ _).2 ⟨zero_mem _, map_zero ev'⟩
  have P1 : ∀ (a : 𝓞 E) {e w}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) →
      Or.𝔐.M.ValAt (gen T zV) (Or.𝔐.ρ a e) (MC.pt (ρC a w)) := fun a e w h => by
    haveI := Or.𝔐.t.act.hom a
    have h1 := Flat.CPoint.valAt_of_isDiffOf (Or.𝔐.t.act.act a) (Or.𝔐.ρ a) (Or.𝔐.act a) h
    rwa [← hact a w] at h1
  have P2 : ∀ {a : RM.Ω} {r : T.Fr} {e w}, ValAt Or.𝔐.ξ (gen T zV) a r → Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) →
      Or.𝔐.M.ValAt (gen T zV) (a • e) (MC.pt (r • w)) := fun {a r e w} ha h => by
    obtain ⟨he, rfl⟩ := (hev1 _ _).1 h
    have ha' : a ∈ regAt Or.𝔐.ξ ⟨centre (gen T zV), h₁⟩ := by
      obtain ⟨_, s', e1, -⟩ := ha
      exact ⟨s', e1⟩
    exact (hev1 _ _).2 ⟨(Or.𝔐.M.lat _).smul_mem ⟨a, ha'⟩ he, hev2 ⟨a, ha'⟩ r ⟨e, he⟩ ha⟩
  have P3 : ∀ {e e' w w'}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) → Or.𝔐.M.ValAt (gen T zV) e' (MC.pt w') →
      Or.𝔐.M.ValAt (gen T zV) (e + e') (MC.pt (w + w')) := fun {e e' w w'} h h' => by
    obtain ⟨he, rfl⟩ := (hev1 _ _).1 h
    obtain ⟨he', rfl⟩ := (hev1 _ _).1 h'
    exact (hev1 _ _).2 ⟨add_mem he he', map_add ev' ⟨e, he⟩ ⟨e', he'⟩⟩
  have Pu : ∀ {e w w'}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) → Or.𝔐.M.ValAt (gen T zV) e (MC.pt w') → w = w' :=
    fun {e w w'} h h' => by
      obtain ⟨he, rfl⟩ := (hev1 _ _).1 h
      obtain ⟨he', rfl⟩ := (hev1 _ _).1 h'
      rfl
  obtain ⟨n, a, b, hop⟩ := GlobalTheory.CompanionTheory.Ar.Sandwich.Sep.exists_eigen_op_discr E

  let Tc : EC →ₗ[T.Fr] EC := ∑ i, algebraMap T.V T.Fr (σ (b i)) • ρC (a i)
  have hTc : ∀ w, Tc w = ∑ i, ((algebraMap T.V T.Fr).comp σ) (b i) • ρC (a i) w := fun w => by
    simp [Tc, LinearMap.sum_apply]
  have Pt : ∀ {e w}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) →
      Or.𝔐.M.ValAt (gen T zV) (∑ i, Or.𝔐.emb s (b i) • Or.𝔐.ρ (a i) e) (MC.pt (Tc w)) := fun {e w} h => by
    rw [hTc]
    have : ∀ S : Finset (Fin n), Or.𝔐.M.ValAt (gen T zV) (∑ i ∈ S, Or.𝔐.emb s (b i) • Or.𝔐.ρ (a i) e)
        (MC.pt (∑ i ∈ S, ((algebraMap T.V T.Fr).comp σ) (b i) • ρC (a i) w)) := fun S => by
      classical
      induction S using Finset.induction_on with
      | empty => simpa using P0
      | insert i S hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        exact P3 (P2 (hσ' _) (P1 _ h)) ih
    exact this _
  have hD : IsUnit ((discr E : ℤ) : T.V) :=
    isUnit_int_of_inFibre_rf (ξ := Or.𝔐.ξ) zV h₀ hp hF hdisc
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro w ⟨h, e', he, hw⟩
    have he' : e' ∈ Or.𝔐.dR s ⟨centre zV, h₀⟩ := hV ▸ he
    refine ⟨Submodule.subset_span ⟨h, e', he'.1, hw⟩, ?_⟩
    have heig : ∀ x, Or.𝔐.ρ x e' = Or.𝔐.emb s x • e' := fun x => by
      have := (Submodule.mem_iInf _).1 he'.2 x
      simpa [sub_eq_zero] using this
    refine (Submodule.mem_iInf _).2 fun x => ?_
    have h1 := P1 x hw
    rw [heig x] at h1
    have h2 := Pu h1 (P2 (hσ' x) hw)
    simp [sub_eq_zero, h2]
  · rintro w ⟨hw1, hw2⟩
    have key : ∀ u ∈ Or.𝔐.M.fibAt Or.𝔐.M.lat zV MC, Tc u ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC := fun u hu => by
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨h, e', he, hv⟩ := hu
        refine Submodule.subset_span ⟨h, _, ?_, Pt hv⟩
        show _ ∈ Or.𝔐.V s ⟨centre zV, h₀⟩
        rw [hV]
        refine ⟨Submodule.sum_mem _ fun i _ => ?_, (hop RM.Ω Or.𝔐.Li Or.𝔐.ρ (Or.𝔐.emb s)).1 e'⟩
        have hreg : Or.𝔐.emb s (b i) ∈ regAt Or.𝔐.ξ ⟨centre zV, h₀⟩ := by
          obtain ⟨_, s', e1, -⟩ := hσ (b i)
          exact ⟨s', e1⟩
        exact (Or.𝔐.M.lat _).smul_mem ⟨_, hreg⟩ (lat_act_of_model_rf Or.𝔐 _ _ _ he)
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add (f := _)]
        exact add_mem hu hv
      | smul r u _ hu =>
        rw [LinearMap.map_smul_of_tower]
        exact Submodule.smul_mem _ r hu
    have hT : Tc w = ((discr E : ℤ) : T.Fr) • w := by
      rw [hTc]
      exact (hop T.Fr EC ρC ((algebraMap T.V T.Fr).comp σ)).2 w hw2
    obtain ⟨u, hu⟩ := hD.exists_left_inv
    have e1 : w = u • Tc w := by
      rw [hT, ← map_intCast (algebraMap T.V T.Fr), algebraMap_smul, smul_smul, hu, one_smul]
    rw [e1]
    exact Submodule.smul_mem _ u (key w hw1)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.PositivityTheory.UnitarySelfGeneration.root_origin_frame_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.fib_eq_lieEig_rf

end
