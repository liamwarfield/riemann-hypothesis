module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelAdaptedBasisIsModelWithSeries
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeight
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPosIsGreatestNormMulVecOnKer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormVanishesOfTorsionTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqZeroOfPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.LatChar

theorem eq_zero_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = 0) : f = 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  refine (basicOpen_eq_bot_iff f).1 ?_
  by_contra hne
  have hne' : ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => hne (SetLike.coe_injective e)
  obtain ⟨y, hy, hc⟩ := nonempty_inter_closedPoints hne' (X.basicOpen f).isOpen.isLocallyClosed
  have hb : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ X.basicOpen f := fun q _ => by
    show pointOfClosedPoint π y hc q ∈ X.basicOpen f
    rw [pointOfClosedPoint_apply π y hc q]
    exact hy
  have hU : ⊤ ≤ (pointOfClosedPoint π y hc) ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le f))
  exact ((CrdCalc.isUnit_valR_iff _ U hU f).2 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem lin_eq_zero {k : Type} [Field k] [IsAlgClosed k] (Φ : FibPre k) [Smooth Φ.G.hom] {N : ℕ}
    {q : QuadraticMap ℤ Φ.E.X ℝ} {J : Type} [Fintype J] {cls : J → Φ.E.X} {F : J → (Φ.H 1).Sec}
    (hG : Φ.Good N q cls F) (a : J → k) (h : ∀ v ∈ cone Φ.G.hom (Φ.H 1) F, ∑ i, a i * v i = 0) : a = 0 := by
  have : IsReduced Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced Φ.G.hom
  refine GlobalTheory.ZH.WtLin.linIndep k Φ N q J cls F hG a fun l => ?_
  refine eq_zero_of_points Φ.G.hom _ _ fun x hx hU => ?_
  have h1 := h _ ⟨x, hx, l, 1, hU, fun _ => rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CrdCalc.valR_eq x _ hU, map_sum, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, Units.val_one, _root_.one_mul]
  exact congrArg (· * _) (GlobalTheory.Points.valR_constFn_of_section Φ.G.hom x hx _ hU (a i))

theorem mem_span_iff {p : ℕ} [Fact p.Prime] {J A : Type} [Fintype J] [Nonempty J] (B : Matrix J J (PadicAlgCl p))
    (hB : B.det ≠ 0) (T : Set A) (v : A → J → PadicAlgCl p) (κ : ℝ) (hκ : 0 < κ)
    (hle : ∀ a ∈ T, ∀ i, ‖B.mulVec (v a) i‖ ≤ κ)
    (hdet : ∀ c : J → OO p, (∀ a ∈ T, ‖∑ i, (c i : PadicAlgCl p) * B.mulVec (v a) i‖ < κ) →
      ∀ i, ‖(c i : PadicAlgCl p)‖ < 1) (e : J → PadicAlgCl p) :
    e ∈ Submodule.span (OO p) (Set.range B) ↔ ∀ a ∈ T, ‖e ⬝ᵥ v a‖ ≤ κ := by
  have key : ∀ (c : J → PadicAlgCl p) (w : J → PadicAlgCl p),
      (B.vecMul c) ⬝ᵥ w = ∑ i, c i * B.mulVec w i := fun c w => (Matrix.dotProduct_mulVec c B w).symm
  have hvec : ∀ c : J → OO p, ∑ i, c i • B i = B.vecMul fun i => (c i : PadicAlgCl p) := fun c => by
    ext j
    rw [Finset.sum_apply]
    rfl
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => B i) _).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ a ha
    rw [hvec, key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hκ.le fun i _ => ?_
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 (c i).2)).trans (hle a ha i)
  · intro h
    obtain ⟨c, rfl⟩ : ∃ c, B.vecMul c = e := ⟨B⁻¹.vecMul e, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB), Matrix.vecMul_one]⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun i => ‖c i‖
    by_cases h1 : ‖c i₀‖ ≤ 1
    · exact ⟨fun i => ⟨c i, (mem_OO_iff _).2 ((hi₀ i).trans h1)⟩, hvec _⟩
    exfalso
    rw [not_le] at h1
    have h0 : 0 < ‖c i₀‖ := one_pos.trans h1
    have h0' : c i₀ ≠ 0 := norm_pos_iff.1 h0
    have := hdet (fun i => ⟨c i / c i₀, (mem_OO_iff _).2 (by
      rw [norm_div]; exact (div_le_one h0).2 (hi₀ i))⟩) (fun a ha => by
        have h2 := h a ha
        rw [key] at h2
        have e : ∑ i, c i / c i₀ * B.mulVec (v a) i = (∑ i, c i * B.mulVec (v a) i) / c i₀ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        show ‖∑ i, c i / c i₀ * B.mulVec (v a) i‖ < κ
        rw [e, norm_div, div_lt_iff₀ h0]
        exact h2.trans_lt (lt_mul_of_one_lt_right hκ h1)) i₀
    simp [div_self h0'] at this

theorem mem_lattice_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)) (κ : ℝ), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → u.Link σ b → b.det ≠ 0 → 0 < κ → (∀ a ∈ l.yy.ker, IsGreatest (Set.range fun i => ‖(b.map (algebraMap _ (PadicAlgCl p))).mulVec (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i‖) κ) → ∀ e : S.J → PadicAlgCl p, e ∈ Submodule.span (OO p) (Set.range (b.map (algebraMap _ (PadicAlgCl p)))) ↔ ∀ a ∈ l.yy.ker, ‖e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩)‖ ≤ κ := by
  intro L o Ω _ _ _ _ S ρ p _ y₀ u l σ cls md b κ hBig hy hL hb hκ hmax e
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(GlobalTheory.T.uniformisedTest_dimensions_and_split_fibre L o Ω S ρ p y₀ u).2.2.2.1, hBig.1, hBig.2.1⟩
  obtain ⟨hN, htor, -⟩ := GlobalTheory.T.specialFibre_torsion_eq_reductions L o Ω S ρ p y₀ u l σ cls md hy
  have pb : IsPullback md.r md.Φ.G.hom u.G.hom (rPt p ≫ spMap u.j) := md.cart.1
  have hs : Smooth u.G.hom := md.smooth.smooth
  have : Smooth md.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  refine mem_span_iff _ ?_ (l.yy.ker : Set S.Gam) (fun a i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) κ hκ
    (fun a ha i => (hmax a ha).2 ⟨i, rfl⟩) (fun c hc => ?_) e
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hb
  have hev : ∀ v : S.J → kb p, MvPolynomial.eval v (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) *
      MvPolynomial.X i) = ∑ i, IsLocalRing.residue (OO p) (c i) * v i := fun v => by simp
  have hz := GlobalTheory.T.form_vanishes_of_torsion_torusExtension L.1 L.2.1 (kb p) md.Φ S.g S.N (S.r * S.N) _ S.J _ md.F md.pol hB md.good md.dim hN 1
    (∑ i, MvPolynomial.C (IsLocalRing.residue (OO p) (c i)) * MvPolynomial.X i)
    (Nat.mul_pos (pow_pos (by have := hB.four; omega) _) (Nat.factorial_pos _))
    (MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X _ i).C_mul _) ?_
  · have h0 := lin_eq_zero md.Φ md.good (fun i => IsLocalRing.residue (OO p) (c i)) fun v hv =>
      (hev v).symm.trans (hz v hv)
    intro i
    exact (not_isUnit_OO_iff _).1 fun hu => (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu (congrFun h0 i)
  intro x hx
  obtain ⟨a, ha, z, a', hz, hg, hA, hr⟩ := htor x hx
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists md.isLB σ z
  obtain ⟨⟨i₀, -, hi₀⟩, x', hx', hc'⟩ := GlobalTheory.T.exists_unit_weightZero_integral_coords L.1 L.2.1 p u.V u.j u.G S.g S.N (S.r * S.N) _ l.q _ S.J σ cls
    md hB z w hz hw
  have hxx : x'.left = x.left := pb.hom_ext (hx'.trans hr) ((Over.w x').trans (Over.w x).symm)
  refine ⟨_, hxx ▸ hc', ?_⟩
  have h1 := hL a' _ (hA ▸ (GlobalTheory.T.torsionValues_coords_operator_permute L o Ω S ρ).1 _ y₀ a)
  have h2 := CrdCalc.crd_map (OO p).subtype hw
  rw [show spMap (OO p).subtype ≫ z = u.toG a' from hg] at h2
  obtain ⟨t, ht⟩ := CrdCalc.crd_unique h2 h1
  have hn : κ ≤ ‖(t : PadicAlgCl p)‖ := by
    obtain ⟨i, hi⟩ := (hmax a ha).1
    rw [← hi]
    beta_reduce
    rw [ht i, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 (w i).2)
  have h3 := hc a ha
  have e3 : ∑ i, (c i : PadicAlgCl p) * (b.map (algebraMap _ (PadicAlgCl p))).mulVec
      (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) i = t * ((∑ i, c i * w i : OO p) : PadicAlgCl p) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, c i * w i : OO p) : PadicAlgCl p) = (OO p).subtype (∑ i, c i * w i) from rfl, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht i, map_mul, mul_left_comm]
    rfl
  rw [e3, norm_mul] at h3
  have h4 : ‖((∑ i, c i * w i : OO p) : PadicAlgCl p)‖ < 1 := by
    by_contra h5
    exact absurd h3 (not_lt.2 (hn.trans (le_mul_of_one_le_right (norm_nonneg _) (not_lt.1 h5))))
  rw [hev]
  have h5 : IsLocalRing.residue (OO p) (∑ i, c i * w i) = 0 := by
    by_contra h6
    exact (not_isUnit_OO_iff _).2 h4 ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h6)
  simpa using h5

end GlobalTheory.ZH.LatChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceIrreducibleResidue
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.WeightIrred

open ThetaReal GlobalGen

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem matrix_mul_of_comp {A M J : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype J] (φ : o →+* A)
    (s : J → M) (uniq : ∀ c c' : J → o, ∑ l, φ (c l) • s l = ∑ l, φ (c' l) • s l → c = c')
    {u₁ u₂ u₃ : M ≃ₗ[A] M} {m₁ m₂ m₃ : Matrix J J o} (h₁ : ∀ i, u₁ (s i) = ∑ l, φ (m₁ l i) • s l)
    (h₂ : ∀ i, u₂ (s i) = ∑ l, φ (m₂ l i) • s l) (h₃ : ∀ i, u₃ (s i) = ∑ l, φ (m₃ l i) • s l) {x : o}
    (h : ∀ i, u₁ (u₂ (s i)) = φ x • u₃ (s i)) : m₁ * m₂ = x • m₃ := by
  ext l i
  have key := h i
  refine congrFun (uniq (fun l => (m₁ * m₂) l i) (fun l => (x • m₃) l i) ?_) l
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h₂, h₃, map_sum, Finset.smul_sum] at key
  simp only [map_smul, h₁, Finset.smul_sum, smul_smul] at key
  rw [Finset.sum_comm] at key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.smul_apply, smul_eq_mul]
  refine Eq.trans ?_ key
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem pt_pow (ρ : S.Real) (a : S.Gam) : ρ.pt (S.r • a) ^ S.N = 1 := by
  obtain ⟨h0, hsm⟩ := pt_nsmul ρ.pt ρ.pt_add
  rw [← hsm, smul_smul, mul_comm S.N S.r, nsmul_self, h0]

theorem weil_level (hL : Laws) [hA : ArithBase o Ω] (ρ : S.Real) (a b : S.Gam) (c : (S.R)ˣ)
    (hc : (c : S.R) = algebraMap o S.R (S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val))) :
    WeilIs ρ.P.A ρ.P.L S.N (ρ.pt (S.r • a)) (ρ.pt (S.r • b)) (unitOn c) := by
  have := hA.ded
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have : IsLocallyNoetherian (Sp S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of S.R)))
  let φ : o →+* Γ((baseOver (Sp S.R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom.comp (algebraMap o S.R)
  obtain ⟨h0, hsm⟩ := pt_nsmul ρ.pt ρ.pt_add
  have h₁ := ρ.weil a (S.r • b) c (by rw [eStd_nsmul, hc])
  have h₂ := (hL.weil _ ρ.P S.N (baseOver (Sp S.R))).2.2.2 S.r (ρ.pt a) (ρ.pt (S.r • b)) (unitOn c)
    (by rw [mul_comm, ← map_natCast φ]; exact S.unit.map φ)
    (by rw [← hsm, mul_comm S.N S.r, nsmul_self, h0]) (pt_pow ρ b)
  rw [hsm S.r a]
  refine h₂.1 ?_
  rw [← Nat.cast_mul, mul_comm S.N S.r]
  exact h₁

theorem rho_mul_rho (hL : Laws) [hA : ArithBase o Ω] (ρ : S.Real) (a b : S.Gam) :
    S.ρ a * S.ρ b =
      S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val * ((S.N + 1) / 2)) • S.ρ (a + b) := by
  have := ρ.P.isAb.comm
  let φ : o →+* Γ((baseOver (Sp S.R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom.comp (algebraMap o S.R)
  have hφ : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).1.comp
      fun b b' h => hA.inj (congrArg Subtype.val h)
  obtain ⟨u, hu, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns _ ρ.P S.N (baseOver (Sp S.R))
  have hodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have act : ∀ a v, IsActOf ρ.P.A ρ.P.L S.N (ρ.U a) (SecM.toSec ρ.P.A v) (SecM.toSec ρ.P.A (u (ρ.U a) v)) :=
    fun a v => (hu _ _ _).2 rfl
  obtain ⟨c, hc⟩ : IsUnit (algebraMap o S.R (S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val))) :=
    ((S.prim.isUnit (pow_ne_zero _ (NeZero.ne (S.r * S.N)))).pow _).map _
  have weil := weil_level hL ρ a b c hc
  have hc' : (unitOn c).val = φ (S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val)) :=
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom hc
  let s : S.J → SecM ρ.P.A ρ.P.L S.N (baseOver (Sp S.R)) := fun i => SecM.ofSec ρ.P.A (ρ.s i)
  have hs : ∀ a i, u (ρ.U a) (s i) = ∑ l, φ (S.ρ a l i) • s l := fun a i =>
    (sum_iff _ s fun l => φ (S.ρ a l i)).1 (ρ.U_act a i _ (act a (s i)))
  refine matrix_mul_of_comp φ s (fun c c' h => ?_) (hs a) (hs b) (hs (a + b)) fun i => ?_
  · have := (ρ.s_basis (SecM.toSec ρ.P.A (∑ l, φ (c l) • s l))).unique
      ((sum_iff _ s fun l => φ (c l)).2 rfl) ((sum_iff _ s fun l => φ (c' l)).2 h)
    exact funext fun l => hφ (congrFun this l)
  · have := act_act hL.globalFns ρ.P.isAb ρ.P.isLB hodd (pt_pow ρ b) (ρ.U_sym a) (ρ.U_sym b)
      (by rw [← ρ.pt_add, ← smul_add, add_comm]; exact ρ.U_sym (a + b)) weil (act b (s i)) (act a _)
      (act (a + b) (s i))
    refine this.trans (congrArg (· • _) ?_)
    rw [pow_mul S.ζ (_ * _), map_pow φ, ← hc']
    exact Units.val_pow_eq_pow_val _ _

theorem exists_perp {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (x : S.Gam)
    (h : ∀ t : T, S.r • eStd S.g _ t x = 0) : ∃ b : S.Gam, x - S.N • b ∈ S.perp T := by
  obtain ⟨-, d, ⟨E⟩⟩ := hT
  choose a ha using fun t : T => ZModPerp.exists_eq_nsmul_zmod (mul_comm S.N S.r) _ (h t)
  obtain ⟨b, hb⟩ := Weights.exists_eStd_eq (T.subtype.comp E.symm.toAddMonoidHom)
    (Subtype.val_injective.comp E.symm.injective) (fun i => a (E.symm (Pi.single i 1)))
  have h3 := Weights.addHom_ext_single ((Weights.eLeft S.g _ x).comp (T.subtype.comp E.symm.toAddMonoidHom))
    (S.N • (Weights.eLeft S.g _ b).comp (T.subtype.comp E.symm.toAddMonoidHom)) fun i => by
      exact (ha _).trans (congrArg (S.N • ·) (hb i).symm)
  refine ⟨b, fun t ht => ?_⟩
  have h5 : eStd S.g _ t x = S.N • eStd S.g _ t b := by
    simpa [Weights.eLeft_apply] using DFunLike.congr_fun h3 (E ⟨t, ht⟩)
  rw [← Weights.eLeft_apply, map_sub, map_nsmul, Weights.eLeft_apply, Weights.eLeft_apply, Weights.eStd_swap, h5,
    Weights.eStd_swap _ _ t b]
  simp

theorem chi_smul_rho_mul_proj {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (c : T →+ ZMod S.N) (s : T) :
    chi S (c s) • (S.ρ s * S.proj T c) = S.proj T c := by
  have := Fintype.ofFinite T
  rw [proj_eq, mul_smul_comm, smul_comm, Finset.mul_sum, Finset.smul_sum,
    ← Equiv.sum_comp (Equiv.addLeft s) fun t : T => chi S (c t) • S.ρ t]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm, smul_smul, ρ_mul_ρ hT, ← chi_add, ← map_add (f := _)]
  rfl

theorem rho_comm (hodd : Odd S.N) (hmul : ∀ a b, S.ρ a * S.ρ b =
      S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val * ((S.N + 1) / 2)) • S.ρ (a + b)) (a b : S.Gam) :
    S.ρ a * S.ρ b = (S.ζ ^ (S.r * S.N)) ^ (S.r • eStd S.g _ a b).val • (S.ρ b * S.ρ a) := by
  have hω : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
    S.prim.pow (pow_pos (NeZero.pos _) 2) (sq _)
  rw [hmul, hmul b a, add_comm b a, smul_smul, _root_.mul_assoc, _root_.mul_assoc (S.r * S.N), pow_mul S.ζ (S.r * S.N),
    pow_mul S.ζ (S.r * S.N) (_ * _), ← pow_add]
  congr 1
  rw [pow_eq_pow_mod _ hω.pow_eq_one, pow_eq_pow_mod (_ + _) hω.pow_eq_one]
  congr 1
  refine (ZMod.natCast_eq_natCast_iff' _ _ _).1 ?_
  obtain ⟨m, hm⟩ := hodd
  have h1 : (S.N + 1) / 2 = m + 1 := by omega
  have h2 : ((S.r : ZMod (S.r * S.N)) * (2 * m + 1)) = 0 := by
    have := ZMod.natCast_self (S.r * S.N)
    rw [Nat.cast_mul] at this
    rw [← this]
    congr 1
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (S.r * S.N)) hm.symm
  rw [h1, Weights.eStd_swap _ _ a b]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul, Nat.cast_one]
  linear_combination (eStd S.g _ a b) * h2

theorem irred_of_comm [IsDomain o] (hc : Fintype.card S.J = S.N ^ S.g)
    (hcomm : ∀ a b, S.ρ a * S.ρ b = (S.ζ ^ (S.r * S.N)) ^ (S.r • eStd S.g _ a b).val • (S.ρ b * S.ρ a))
    {F : Type} [Field F] (y : o →+* F) {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (c : T →+ ZMod S.N)
    (W : Submodule F (S.J → F)) (hW : ∀ v ∈ W, ((S.proj T c).map y).mulVec v = v)
    (hst : ∀ h ∈ S.perp T, ∀ v ∈ W, ((S.ρ h).map y).mulVec v ∈ W) :
    W = ⊥ ∨ ∀ v, ((S.proj T c).map y).mulVec v = v → v ∈ W := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let Λ : Matrix S.J S.J o →+* Module.End F (S.J → F) :=
    (Matrix.toLinAlgEquiv' (R := F) (n := S.J)).toRingEquiv.toRingHom.comp y.mapMatrix
  have hΛ : ∀ M v, Λ M v = (M.map y).mulVec v := fun M v => Matrix.toLinAlgEquiv'_apply _ _
  have hΛs : ∀ (x : o) M, Λ (x • M) = y x • Λ M := fun x M => LinearMap.ext fun v => by
    rw [LinearMap.smul_apply, hΛ, hΛ, ← Matrix.smul_mulVec]
    congr 1
    ext i j
    simp
  simp only [← hΛ] at hW hst ⊢
  have hω : IsPrimitiveRoot (y (S.ζ ^ (S.r * S.N))) (S.r * S.N) := by
    have hω : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
      S.prim.pow (pow_pos (NeZero.pos _) 2) (sq _)
    have : NeZero ((S.r * S.N : ℕ) : F) := ⟨by simpa only [map_natCast] using (S.unit.map y).ne_zero⟩
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic _ y]
    exact (hω.isRoot_cyclotomic (NeZero.pos _)).map y
  have hζ : y S.ζ ≠ 0 := ((S.prim.isUnit (pow_ne_zero _ (NeZero.ne (S.r * S.N)))).map y).ne_zero
  let ψ : ZMod (S.r * S.N) → F := fun x => y (S.ζ ^ (S.r * S.N)) ^ x.val
  have ψinj : Function.Injective ψ := fun x x' h =>
    ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)
  have ψadd : ∀ x x', ψ (x + x') = ψ x * ψ x' := fun x x' => by
    simp only [ψ]
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hω.pow_eq_one).symm
  have ψ0 : ψ 0 = 1 := by simp [ψ]
  have comm : ∀ a b v, Λ (S.ρ a) (Λ (S.ρ b) v) = ψ (S.r • eStd S.g _ a b) • Λ (S.ρ b) (Λ (S.ρ a) v) :=
    fun a b v => by
      have := LinearMap.congr_fun (congrArg Λ (hcomm a b)) v
      rwa [hΛs, map_mul, map_mul, map_pow] at this
  have mul : ∀ a b, ∃ k : F, k ≠ 0 ∧ ∀ v, Λ (S.ρ a) (Λ (S.ρ b) v) = k • Λ (S.ρ (a + b)) v := fun a b => by
    obtain ⟨k, hk⟩ := S.ρ_mul a b
    refine ⟨y S.ζ ^ k, pow_ne_zero _ hζ, fun v => ?_⟩
    have := LinearMap.congr_fun (congrArg Λ hk) v
    rwa [hΛs, map_mul, map_pow] at this
  have inj : ∀ a, Function.Injective (Λ (S.ρ a)) := fun a v v' h => by
    obtain ⟨k, hk, h'⟩ := mul (-a) a
    rw [neg_add_cancel, S.ρ_one 0 (smul_zero _), map_one] at h'
    exact smul_right_injective _ hk ((h' v).symm.trans ((congrArg _ h).trans (h' v')))

  let σ : (Fin S.g ⊕ Fin S.g → ZMod S.N) → S.Gam := fun a i => ((a i).val : ZMod (S.r * S.N))
  have hli : LinearIndependent F fun a => Λ (S.ρ (σ a)) := by
    refine linearIndependent_of_comm_smul _ (fun a b => ψ (S.r • eStd S.g _ (σ a) (σ b))) (fun a => inj _)
      (fun a b v => comm _ _ v) fun a a' h => funext fun i => ?_
    have h1 : (1 : ZMod S.N).val = 1 := by
      have : Fact (1 < S.N) := ⟨S.N_ge⟩
      exact ZMod.val_one _
    have h2 : ∀ j, σ (Pi.single j 1) = Pi.single j 1 := fun j => funext fun l => by
      by_cases hl : l = j
      · subst hl; simp only [σ, Pi.single_eq_same, h1, Nat.cast_one]
      · simp [σ, hl]
    have h3 : S.r • σ a i = S.r • σ a' i := by
      rcases i with i | i
      · have := ψinj (congrFun h (Pi.single (.inr i) 1))
        rw [h2] at this
        simpa [eStd, Pi.single_apply] using this
      · have := ψinj (congrFun h (Pi.single (.inl i) 1))
        rw [h2] at this
        simpa [eStd, Pi.single_apply] using this
    simp only [σ, nsmul_eq_mul, ← Nat.cast_mul] at h3
    have h4 := Nat.ModEq.mul_left_cancel' (by have := S.r_pos; omega) ((ZMod.natCast_eq_natCast_iff _ _ _).1 h3)
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h4
    exact h4
  have hspan : Submodule.span F (Set.range fun a => Λ (S.ρ (σ a))) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, Module.finrank_fintype_fun_eq_card, hc, ← pow_add]
    simp

  have := Fintype.ofFinite T
  have hu : ∀ t : T, y (chi S (c t)) • Λ (S.ρ t) u = u := fun t => by
    have := LinearMap.congr_fun (congrArg Λ (chi_smul_rho_mul_proj hT c t)) u
    rwa [hΛs, map_mul, LinearMap.smul_apply, Module.End.mul_apply, hW u huW] at this
  have hP : ∀ a, Λ (S.proj T c) (Λ (S.ρ a) u) ∈ W := fun a => by
    have e : Λ (S.proj T c) (Λ (S.ρ a) u) = y (Ring.inverse (Nat.card T : o)) •
        (∑ t : T, ψ (S.r • eStd S.g _ t a)) • Λ (S.ρ a) u := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [proj_eq, hΛs, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hΛs, LinearMap.smul_apply, comm, smul_comm, ← map_smul, hu]
    rw [e]
    refine W.smul_mem _ ?_
    by_cases h : ∀ t : T, S.r • eStd S.g _ t a = 0
    · obtain ⟨b, hb⟩ := exists_perp hT a h
      obtain ⟨k, hk, h'⟩ := mul (a - S.N • b) (S.N • b)
      rw [sub_add_cancel, S.ρ_one (S.N • b) (by rw [smul_smul, nsmul_self]), map_one] at h'
      refine W.smul_mem _ ((W.smul_mem_iff hk).1 ?_)
      rw [← h']
      exact hst _ hb u huW
    · obtain ⟨t, ht⟩ := not_forall.1 h
      rw [sum_eq_zero_of_mul (fun t : T => ψ (S.r • eStd S.g _ t a)) (a := t) (fun s t => ?_)
        (fun h => ht (ψinj (h.trans ψ0.symm))), zero_smul]
      · exact W.zero_mem
      · rw [← ψadd, ← smul_add]
        exact congrArg (fun x => ψ (S.r • x)) ((Weights.eLeft S.g _ a).map_add s t)
  intro v hv
  obtain ⟨f, hf⟩ : ∃ f : (S.J → F) →ₗ[F] (S.J → F), f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => Λ (S.ρ (σ a))))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hv, ← hf, ← hd, LinearMap.sum_apply, map_sum]
  refine W.sum_mem fun a _ => ?_
  rw [LinearMap.smul_apply, map_smul]
  exact W.smul_mem _ (hP _)

end GlobalTheory.WeightIrred

namespace GlobalTheory


open WeightIrred in
theorem weightSpace_irreducible_residue : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y : o →+* OO p) (T : AddSubgroup S.Gam), S.IsoFree T → ∀ (c : T →+ ZMod S.N) (W : Submodule (kb p) (S.J → kb p)), (∀ v ∈ W, ((S.proj T c).map fun a => IsLocalRing.residue (OO p) (y a)).mulVec v = v) → (∀ h ∈ S.perp T, ∀ v ∈ W, ((S.ρ h).map fun a => IsLocalRing.residue (OO p) (y a)).mulVec v ∈ W) → W = ⊥ ∨ ∀ v, ((S.proj T c).map fun a => IsLocalRing.residue (OO p) (y a)).mulVec v = v → v ∈ W := by
  intro hL o Ω _ _ _ hA S ρ p _ y T hT c W hW hst
  have : IsDomain o := hA.inj.isDomain _
  exact WeightIrred.irred_of_comm ρ.card
    (WeightIrred.rho_comm (by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow) (WeightIrred.rho_mul_rho hL.1 ρ))
    ((IsLocalRing.residue (OO p)).comp y) hT c W hW hst

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormMulLeOfIrreducible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.TestSpan

section Abstract

variable {p : ℕ} [Fact p.Prime] {J : Type} [Fintype J]

theorem norm_sum_lt {I : Type} [Fintype I] (f : I → PadicAlgCl p) {ε : ℝ} (hε : 0 < ε) (h : ∀ i, ‖f i‖ < ε) :
    ‖∑ i, f i‖ < ε := by
  refine Finset.sum_induction f (fun x => ‖x‖ < ε) (fun a b ha hb => ?_) (by simpa using hε) fun i _ => h i
  exact (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem map_mulVec' {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Matrix J J R) (w : J → R) :
    (A.map f).mulVec (fun j => f (w j)) = fun j => f (A.mulVec w j) := by
  funext j
  simp [Matrix.mulVec, dotProduct]

theorem norm_mul_le_of_irreducible {I : Type} (P : Matrix J J (OO p)) (hP : P * P = P) (s : Set I)
    (A : I → Matrix J J (OO p)) (hcomm : ∀ h ∈ s, P * A h = A h * P)
    (hirr : ∀ W : Submodule (kb p) (J → kb p),
      (∀ v ∈ W, (P.map (IsLocalRing.residue (OO p))).mulVec v = v) →
      (∀ h ∈ s, ∀ v ∈ W, ((A h).map (IsLocalRing.residue (OO p))).mulVec v ∈ W) →
      W = ⊥ ∨ ∀ v, (P.map (IsLocalRing.residue (OO p))).mulVec v = v → v ∈ W)
    (M : Submodule (OO p) (J → PadicAlgCl p))
    (hM : ∀ h ∈ s, ∀ e ∈ M, ((A h).map (OO p).subtype).mulVec e ∈ M)
    (x : J → PadicAlgCl p) (δ ε : ℝ) (hε : 0 < ε) (hx : ∀ e ∈ M, ‖e ⬝ᵥ x‖ ≤ δ)
    (hle : ∀ i, ‖∑ j, (P j i : PadicAlgCl p) * x j‖ ≤ ε) (i₁ : J) (hge : ε ≤ ‖∑ j, (P j i₁ : PadicAlgCl p) * x j‖)
    (v : J → PadicAlgCl p) (hv : v ∈ M) (hPv : (P.map (OO p).subtype).mulVec v = v) (j : J) :
    ‖v j‖ * ε ≤ δ := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) ⟨j, Finset.mem_univ _⟩
  refine (mul_le_mul_of_nonneg_right (hi₀ j (Finset.mem_univ _)) hε.le).trans ?_
  by_cases h0 : v i₀ = 0
  · simpa [h0] using hx 0 M.zero_mem
  have hpos : 0 < ‖v i₀‖ := norm_pos_iff.2 h0
  let r := IsLocalRing.residue (OO p)
  let W : Submodule (kb p) (J → kb p) :=
    { carrier := {z | ∃ w : J → OO p, P.mulVec w = w ∧ v i₀ • (fun j => (w j : PadicAlgCl p)) ∈ M ∧
        z = fun j => r (w j)}
      add_mem' := by
        rintro _ _ ⟨w, h1, h2, rfl⟩ ⟨w', h1', h2', rfl⟩
        refine ⟨w + w', by rw [Matrix.mulVec_add, h1, h1'], ?_, funext fun j => by simp⟩
        convert M.add_mem h2 h2' using 1
        funext j
        simp [mul_add]
      zero_mem' := ⟨0, by simp, by
        convert M.zero_mem using 1
        funext j
        simp, funext fun j => by simp⟩
      smul_mem' := by
        rintro c _ ⟨w, h1, h2, rfl⟩
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨a • w, by rw [Matrix.mulVec_smul, h1], ?_, funext fun j => by simp [r]⟩
        convert M.smul_mem a h2 using 1
        funext j
        change v i₀ * ((a : PadicAlgCl p) * w j) = (a : PadicAlgCl p) * (v i₀ * w j)
        ring }
  have hW := hirr W (by
      rintro _ ⟨w, h1, -, rfl⟩
      rw [map_mulVec', h1])
    (by
      rintro h hh _ ⟨w, h1, h2, rfl⟩
      refine ⟨(A h).mulVec w, ?_, ?_, map_mulVec' _ _ _⟩
      · rw [Matrix.mulVec_mulVec, hcomm h hh, ← Matrix.mulVec_mulVec, h1]
      · have h3 := hM h hh _ h2
        rw [Matrix.mulVec_smul] at h3
        have h4 := map_mulVec' (OO p).subtype (A h) w
        simp only [ValuationSubring.coe_subtype] at h4 h3
        rwa [h4] at h3)
  let w₀ : J → OO p := fun j => ⟨v j / v i₀, (mem_OO_iff _).2 (by
    rw [norm_div, div_le_one hpos]
    exact hi₀ j (Finset.mem_univ _))⟩
  have hw₀ : v i₀ • (fun j => (w₀ j : PadicAlgCl p)) = v := by
    funext j
    change v i₀ * (v j / v i₀) = v j
    field_simp
  have hmem : (fun j => r (w₀ j)) ∈ W := by
    refine ⟨w₀, ?_, hw₀.symm ▸ hv, rfl⟩
    have h4 := map_mulVec' (OO p).subtype P w₀
    simp only [ValuationSubring.coe_subtype] at h4 hPv
    rw [← hw₀, Matrix.mulVec_smul, h4] at hPv
    funext j
    exact Subtype.ext (mul_left_cancel₀ h0 (congrFun hPv j))
  rcases hW with hW | hW
  · rw [hW, Submodule.mem_bot] at hmem
    have h1 : w₀ i₀ = 1 := Subtype.ext (div_self h0)
    have h2 := congrFun hmem i₀
    simp [h1] at h2
  have hcol : P.mulVec (fun j => P j i₁) = fun j => P j i₁ := by
    funext j
    exact congrFun (congrFun hP j) i₁
  obtain ⟨w, h1, h2, h3⟩ := hW (fun j => r (P j i₁)) (by rw [map_mulVec', hcol])
  have hz : ∀ j, ‖((P j i₁ - w j : OO p) : PadicAlgCl p)‖ < 1 := fun j => by
    rw [← not_isUnit_OO_iff, ← IsLocalRing.residue_ne_zero_iff_isUnit, not_not, map_sub]
    exact sub_eq_zero.2 (congrFun h3 j)
  have hfix : ∀ j, (P j i₁ - w j : OO p) = ∑ i, P j i * (P i i₁ - w i) := fun j => by
    have h5 := congrFun hcol j
    have h6 := congrFun h1 j
    simp only [Matrix.mulVec, dotProduct] at h5 h6
    simp only [mul_sub, Finset.sum_sub_distrib, h5, h6]
  have hsum : ∑ j, ((P j i₁ - w j : OO p) : PadicAlgCl p) * x j =
      ∑ i, ((P i i₁ - w i : OO p) : PadicAlgCl p) * ∑ j, (P j i : PadicAlgCl p) * x j := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfix j, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulMemClass.coe_mul]
    ring
  have hlt : ‖∑ j, ((P j i₁ - w j : OO p) : PadicAlgCl p) * x j‖ < ε := by
    rw [hsum]
    refine norm_sum_lt _ hε fun i => ?_
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hle i) (norm_nonneg _)).trans_lt (by nlinarith [hz i])
  have hdec : ∑ j, (P j i₁ : PadicAlgCl p) * x j =
      ∑ j, ((P j i₁ - w j : OO p) : PadicAlgCl p) * x j + ∑ j, (w j : PadicAlgCl p) * x j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hw : ε ≤ ‖∑ j, (w j : PadicAlgCl p) * x j‖ := by
    rw [hdec] at hge
    have := hge.trans (IsUltrametricDist.norm_add_le_max _ _)
    rcases le_max_iff.1 this with h | h
    · exact absurd h (not_le.2 hlt)
    · exact h
  have h7 := hx _ h2
  rw [smul_dotProduct, smul_eq_mul, norm_mul] at h7
  exact (mul_le_mul_of_nonneg_left hw hpos.le).trans h7

end Abstract

section System

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem proj_mul_comm (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (h : S.Gam) (hh : h ∈ S.perp T) :
    S.proj T c * S.ρ h = S.ρ h * S.proj T c := by
  have := Fintype.ofFinite T
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : eStd S.g _ h t = 0 := hh t t.2
  rw [mul_smul_comm, smul_mul_assoc, S.ρ_add _ _ (by rw [Weights.eStd_swap, h1, neg_zero, smul_zero]),
    S.ρ_add _ _ (by rw [h1, smul_zero]), add_comm]

variable {p : ℕ} [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p)

def bdd (H : AddSubgroup S.Gam) (δ : ℝ) (hδ : 0 ≤ δ) : Submodule (OO p) (S.J → PadicAlgCl p) where
  carrier := {e | ∀ a ∈ H, ‖e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩)‖ ≤ δ}
  add_mem' := fun {e e'} he he' a ha => by
    rw [add_dotProduct]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (he a ha) (he' a ha))
  zero_mem' := fun a _ => by simpa using hδ
  smul_mem' := fun c e he a ha => by
    change ‖((c : PadicAlgCl p) • e) ⬝ᵥ _‖ ≤ δ
    rw [smul_dotProduct, smul_eq_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_right ((mem_OO_iff _).1 c.2) (norm_nonneg _)).trans (by simpa using he a ha)

theorem bdd_stable (φ : o →+* OO p) (hφ : ∀ a, (φ a : PadicAlgCl p) = y₀ (algebraMap o S.R a))
    (hev : ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n =
      algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i)
    (H : AddSubgroup S.Gam) (δ : ℝ) (hδ : 0 ≤ δ) (h : S.Gam) (hh : h ∈ H) (e : S.J → PadicAlgCl p)
    (he : e ∈ bdd y₀ H δ hδ) : (((S.ρ h).map φ).map (OO p).subtype).mulVec e ∈ bdd y₀ H δ hδ := by
  intro a ha
  obtain ⟨k, hk⟩ := hev h a
  have h1 : ∀ i, ∑ n, (φ (S.ρ h n i) : PadicAlgCl p) * y₀ ⟨S.ev a n, S.ev_mem a n⟩ =
      (φ (S.ζ ^ k) : PadicAlgCl p) * y₀ ⟨S.ev (a + S.r • h) i, S.ev_mem _ i⟩ := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hφ, ← map_mul, ← map_sum]
    congr 1
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    exact hk i
  have h2 : (((S.ρ h).map φ).map (OO p).subtype).mulVec e ⬝ᵥ (fun i => y₀ ⟨S.ev a i, S.ev_mem a i⟩) =
      (φ (S.ζ ^ k) • e) ⬝ᵥ (fun i => y₀ ⟨S.ev (a + S.r • h) i, S.ev_mem _ i⟩) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = ((φ (S.ζ ^ k) : PadicAlgCl p) * e i) * _
    rw [mul_right_comm, ← h1 i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    change (φ (S.ρ h n i) : PadicAlgCl p) * e i * _ = _
    ring
  rw [h2]
  exact (bdd y₀ H δ hδ).smul_mem _ he _ (H.add_mem ha (H.nsmul_mem hh _))

theorem proj_stable (φ : o →+* OO p) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (M : Submodule (OO p) (S.J → PadicAlgCl p))
    (hM : ∀ t ∈ T, ∀ e ∈ M, (((S.ρ t).map φ).map (OO p).subtype).mulVec e ∈ M) (e : S.J → PadicAlgCl p)
    (he : e ∈ M) : (((S.proj T c).map φ).map (OO p).subtype).mulVec e ∈ M := by
  have := Fintype.ofFinite T
  have h1 : (((S.proj T c).map φ).map (OO p).subtype).mulVec e =
      ∑ t : T, φ (Ring.inverse (Nat.card T : o) * S.ζN ^ (-(c t)).val) •
        (((S.ρ t).map φ).map (OO p).subtype).mulVec e := by
    funext j
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype, Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      Finset.mul_sum, map_sum, Finset.sum_mul, Pi.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    change _ = (OO p).subtype _ * _
    simp only [map_mul]
    ring
  rw [h1]
  exact M.sum_mem fun t _ => M.smul_mem _ (hM t t.2 e he)

variable {y₀} (τ : S.Test p y₀)

theorem exists_le_norm (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {α : τ.X}
    (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) : ∃ t ∈ S.perp τ.yy.ker, ∃ i, τ.δ * Real.exp (-(τ.q α / S.N)) ≤
      ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ := by
  by_contra! h0
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  have := Fintype.ofFinite (S.perp τ.yy.ker)
  have h1 : (⟨_, hk⟩ : S.R) = ∑ t : S.perp τ.yy.ker, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj _ (τ.wt α) j k.1) * ⟨S.ev t j, S.ev_mem t j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum] at h
  refine (norm_sum_lt _ (mul_pos τ.δ_pos (Real.exp_pos _)) fun t => ?_).ne h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, norm_mul, map_sum]
  simp only [map_mul]
  exact (mul_le_mul_of_nonneg_right (hint _) (norm_nonneg _)).trans_lt (by simpa using h0 t t.2 k.1)

theorem E_eq_bdd [ArithBase o Ω] (φ : o →+* OO p) (hφ : ∀ a, (φ a : PadicAlgCl p) = y₀ (algebraMap o S.R a))
    (hev : ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n =
      algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i)
    (hirr : ∀ (c : S.perp τ.yy.ker →+ ZMod S.N) (W : Submodule (kb p) (S.J → kb p)),
      (∀ v ∈ W, ((S.proj _ c).map fun a => IsLocalRing.residue (OO p) (φ a)).mulVec v = v) →
      (∀ h ∈ S.perp (S.perp τ.yy.ker), ∀ v ∈ W,
        ((S.ρ h).map fun a => IsLocalRing.residue (OO p) (φ a)).mulVec v ∈ W) →
      W = ⊥ ∨ ∀ v, ((S.proj _ c).map fun a => IsLocalRing.residue (OO p) (φ a)).mulVec v = v → v ∈ W) :
    τ.E = bdd y₀ τ.yy.ker τ.δ τ.δ_pos.le := by
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => hφ a ▸ (mem_OO_iff _).1 (φ a).2
  have : IsDomain o := (ArithBase.inj (o := o) (Ω := Ω)).isDomain
  have := FreeNear.finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := FreeNear.proj_orthogonal S _ τ.isoFree
  have hpp := TestBasis.perp_perp S τ.yy.ker
  have hTH : S.perp τ.yy.ker ≤ τ.yy.ker := τ.isoFree.1.trans hpp.le
  refine le_antisymm (Submodule.span_le.2 ?_) fun e he => ?_
  · rintro _ ⟨α, l, i, hα, hl, rfl⟩ a ha
    have h1 := τ.le α hα a ha i
    simp only [dotProduct, _root_.mul_assoc, ← Finset.mul_sum, norm_mul]
    refine (mul_le_mul hl h1 (norm_nonneg _) (Real.exp_pos _).le).trans (le_of_eq ?_)
    rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, _root_.mul_one]
  have hst := bdd_stable y₀ φ hφ hev τ.yy.ker τ.δ τ.δ_pos.le
  let ψ : o →+* PadicAlgCl p := (OO p).subtype.comp φ
  have he' : e = ∑ c : S.perp τ.yy.ker →+ ZMod S.N, (ψ.mapMatrix (S.proj _ c)).mulVec e := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Matrix.sum_mulVec, ← map_sum, hsum, map_one, Matrix.one_mulVec]
  rw [he']
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨α, hα, rfl⟩ := (test_weights o Ω S p y₀ τ).1 c
  have hPP : S.proj _ (τ.wt α) * S.proj _ (τ.wt α) = S.proj _ (τ.wt α) := by rw [hmul, if_pos rfl]
  have hfix : (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec ((ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e) =
      (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e := by
    rw [Matrix.mulVec_mulVec, ← map_mul, hPP]
  have hv : (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e ∈ bdd y₀ τ.yy.ker τ.δ τ.δ_pos.le :=
    proj_stable φ _ _ _ (fun t ht => hst t (hTH ht)) e he
  generalize (ψ.mapMatrix (S.proj _ (τ.wt α))).mulVec e = v at hfix hv
  obtain ⟨t, ht, i₁, hi₁⟩ := exists_le_norm τ hint hα
  have key := norm_mul_le_of_irreducible (φ.mapMatrix (S.proj _ (τ.wt α))) (by rw [← map_mul, hPP])
    (S.perp (S.perp τ.yy.ker) : Set S.Gam) (fun h => φ.mapMatrix (S.ρ h))
    (fun h hh => by rw [← map_mul, ← map_mul, proj_mul_comm _ _ h hh]) (hirr _)
    (bdd y₀ τ.yy.ker τ.δ τ.δ_pos.le) (fun h hh => hst h (hpp.le hh))
    (fun j => y₀ ⟨S.ev t j, S.ev_mem t j⟩) τ.δ (τ.δ * Real.exp (-(τ.q α / S.N)))
    (mul_pos τ.δ_pos (Real.exp_pos _)) (fun e he => he t (hTH ht))
    (fun i => by simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, hφ] using τ.le α hα t (hTH ht) i) i₁
    (by simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, hφ] using hi₁) v hv hfix
  have hv' : v = ∑ i, fun j => v i * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) := by
    funext j
    rw [Finset.sum_apply, ← congrFun hfix j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hφ, _root_.mul_comm]
    rfl
  rw [hv']
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨α, v i, i, hα, ?_, rfl⟩
  have h1 := key i
  rw [mul_left_comm, mul_le_iff_le_one_right τ.δ_pos, Real.exp_neg, ← div_eq_mul_inv,
    div_le_one (Real.exp_pos _)] at h1
  exact h1

end System

end GlobalTheory.ZH.TestSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH


open TestSpan in
theorem testLattice_eq_span_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l τ σ cls md b hbig hint hmt hlink hdet
  obtain ⟨κ, hκ, hfr⟩ := FrameNorm.exists_pos_isGreatest_norm_mulVec_on_ker hLL o Ω S ρ p y₀ u l σ cls md b hbig hint hlink
  have hΛ := LatChar.mem_lattice_iff hLL o Ω S ρ p y₀ u l σ cls md b κ hbig hint hlink hdet hκ hfr
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  have hE := E_eq_bdd τ φ (fun _ => rfl) (EvCrd.ev_crd_act hLL o Ω S ρ).2
    (GlobalTheory.weightSpace_irreducible_residue hLL o Ω S ρ p φ _ τ.isoFree)
  have hker : ∀ a, a ∈ l.yy.ker ↔ a ∈ τ.yy.ker := fun a => by
    obtain ⟨e, -, he⟩ := hmt
    have h1 := he a 0
    rw [map_zero] at h1
    exact h1.symm
  obtain ⟨x, hx⟩ := τ.δ_max.1
  obtain ⟨i, hi⟩ := (hfr 0 (zero_mem _)).1
  let em := algebraMap (FractionRing u.V) (PadicAlgCl p)
  have hy : ∀ a, y₀ a = em (u.yK a) := fun a => (DFunLike.congr_fun u.fac a).symm
  let d : FractionRing u.V := u.yK ⟨S.th x, S.th_mem x⟩
  let k : FractionRing u.V := b.mulVec (fun i => u.yK ⟨S.ev 0 i, S.ev_mem 0 i⟩) i
  have hd : ‖em d‖ = τ.δ := (congrArg norm (hy _)).symm.trans hx
  have hk : ‖em k‖ = κ := by
    refine Eq.trans ?_ hi
    simp only [hy]
    exact congrArg norm (congrFun (map_mulVec' em b _) i).symm
  have hc : ‖em (d / k)‖ = τ.δ / κ := by rw [map_div₀, norm_div, hd, hk]
  have hc0 : em (d / k) ≠ 0 := norm_pos_iff.1 (hc ▸ div_pos τ.δ_pos hκ)
  refine ⟨d / k, fun h => hc0 (by rw [h, map_zero]), ?_⟩
  generalize d / k = c at hc hc0
  let m : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p) :=
    (LinearMap.lsmul (PadicAlgCl p) (S.J → PadicAlgCl p) (em c)).restrictScalars (OO p)
  have hm : ∀ e, m e = em c • e := fun _ => rfl
  have hr : Set.range ((c • b).map em) = m '' Set.range (b.map em) := by
    have h1 : ∀ i, (c • b).map em i = m (b.map em i) := fun i => by
      rw [hm]
      funext j
      simp only [Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (h1 i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, h1 i⟩
  clear_value m
  rw [hE]
  refine Eq.trans ?_ (congrArg (Submodule.span (OO p)) hr).symm
  rw [Submodule.span_image]
  ext e
  constructor
  · intro he
    refine ⟨(em c)⁻¹ • e, (hΛ _).2 fun a ha => ?_, by rw [hm, smul_inv_smul₀ hc0]⟩
    rw [smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, hc, inv_div, div_mul_eq_mul_div, div_le_iff₀ τ.δ_pos]
    exact mul_le_mul_of_nonneg_left (he a ((hker a).1 ha)) hκ.le
  · rintro ⟨e, he, rfl⟩ a ha
    rw [hm, smul_dotProduct, smul_eq_mul, norm_mul, hc, div_mul_eq_mul_div, div_le_iff₀ hκ]
    exact mul_le_mul_of_nonneg_left ((hΛ _).1 he a ((hker a).2 ha)) τ.δ_pos.le

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestLatticeEqSpanModelSectionsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testLattice_eq_span_model_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  first | exact @GlobalTheory.ZH.testLattice_eq_span_sections | exact GlobalTheory.ZH.testLattice_eq_span_sections | (intros; apply GlobalTheory.ZH.testLattice_eq_span_sections <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGeometricTestOfHasUniformisedTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.GeoExist

theorem link_smul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
    [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (σ : S.J → (u.H S.N).Sec)
    (b : Matrix S.J S.J (FractionRing u.V)) (h : u.Link σ b) (c : FractionRing u.V) (hc : c ≠ 0) :
    u.Link σ (c • b) := by
  intro a v hv
  have hc' : algebraMap (FractionRing u.V) (PadicAlgCl p) c ≠ 0 := (map_ne_zero _).2 hc
  have h₁ := CrdCalc.crd_smul (Units.mk0 _ hc') (h a v hv)
  convert h₁ using 1
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]

theorem hasGeo_of_hasU : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  intro hL hT o Ω _ _ _ _ S ρ hB hU p _ y₀ hy Fs
  obtain ⟨u, l, τ, hm, hF⟩ := hU p y₀ hy Fs
  obtain ⟨σ, cls, f, hb⟩ := GlobalTheory.T.exists_adapted_basis_sections_mod_k hL o Ω S ρ p y₀ u l S.N (le_trans one_le_two S.N_ge) S.J ρ.card
  obtain ⟨md⟩ := GlobalTheory.T.uniformisedModel_adaptedBasis_is_modelWithSeries hL hT o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨b, hd, hl⟩ := GlobalTheory.T.exists_invertible_adaptedBasis_link_matrix hL o Ω S ρ p y₀ u l σ cls f hb
  obtain ⟨c, hc, hs⟩ := GlobalTheory.T.testLattice_eq_span_model_sections hL o Ω S ρ p y₀ u l τ σ cls md b hB hy hm hl hd
  have hl' := link_smul u σ b hl c hc
  exact ⟨⟨u, l, τ, hm, σ, cls, md, c • b, hl', hs,
    GlobalTheory.T.adaptedBasis_rows_have_class_weight hL hT o Ω S ρ p y₀ u l σ cls f hb (c • b) hl'⟩, hF⟩

end GlobalTheory.ZH.GeoExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGeometricTestOfHasUniformisedTestStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGeometricTest_of_hasUniformisedTest : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ρ.HasU → ρ.HasGeo := by
  first | exact @GlobalTheory.ZH.GeoExist.hasGeo_of_hasU | exact GlobalTheory.ZH.GeoExist.hasGeo_of_hasU | (intros; apply GlobalTheory.ZH.GeoExist.hasGeo_of_hasU <;> assumption)
end
