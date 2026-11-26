module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ChainLevelPtOfSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamily
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecPtsIsFibAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToCompClm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointsFramesEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecPtsNonempty
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts.Special

theorem exists_lift {Z Z' : Scheme.{0}} (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ∃ x' : Z' ⟶ W.toScheme, x' ≫ W.ι = x := by
  refine ⟨IsOpenImmersion.lift W.ι x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h (x := p) trivial

theorem le_comp {Z Z' Z'' : Scheme.{0}} (g : Z'' ⟶ Z') (x : Z' ⟶ Z) (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    ⊤ ≤ (g ≫ x) ⁻¹ᵁ W := fun p _ => h (x := g p) trivial

theorem le_powOver {S Z' : Scheme.{0}} (G : Over S) (L : LB G.left) (U : S.Opens) (N : ℕ)
    (x : Z' ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι) (h : ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ (Out.powOver G L U N).U (fun _ => j) :=
  fun p _ => Set.mem_iInter.2 fun _ => h (x := p) trivial

theorem exists_chart {Z : Scheme.{0}} {K : Type} [Field K] (L : LB Z) (hL : L.IsLB) (x : Sp K ⟶ Z) :
    ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have h : x (default : PrimeSpectrum K) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨j, fun p _ => ?_⟩
  obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
  exact hj

theorem exists_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (hL : L.IsLB)
    {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (y : Sp R ⟶ S) (x : Sp K ⟶ G.left) (hx : x ≫ G.hom = spMap f ≫ y) (τ : L.ι → K) (hτ : IsFrm L x τ)
    (U : S.Opens) (hU : IsAffineOpen U) (hyU : ⊤ ≤ y ⁻¹ᵁ U) {n : ℕ} (b : Fin n → LB.Sec (Out.powOver G L U 4))
    (hb : AmpleSpan.EmbedsBy (G.hom ∣_ U) b) (cf : Fin n → R) (hcf : ∃ i, IsUnit (cf i))
    (hv : ∀ i (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U).ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U 4).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * τ j ^ 4)
    (U' : S.Opens) (hyU' : ⊤ ≤ y ⁻¹ᵁ U') (b' : LB.Sec (Out.powOver G L U' 5)) (cf' : R) (hcf' : IsUnit cf')
    (hv' : ∀ (x' : Sp K ⟶ (G.hom ⁻¹ᵁ U').toScheme) (j : L.ι), x' ≫ (G.hom ⁻¹ᵁ U').ι = x → ⊤ ≤ x ⁻¹ᵁ L.U j →
      valR x' ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j)) = f cf' * τ j ^ 5) :
    ∃ (z : Sp R ⟶ G.left) (σ : L.ι → R), z ≫ G.hom = y ∧ spMap f ≫ z = x ∧ IsFrm L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ L.U j → f (σ j) = τ j := by
  classical
  have hxU : ⊤ ≤ x ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hx]
    exact le_comp _ _ _ hyU
  obtain ⟨x₁, hx₁⟩ := exists_lift x _ hxU
  obtain ⟨j₀, hj₀⟩ := exists_chart L hL x
  obtain ⟨u₀, hu₀⟩ := (hτ.1 j₀ hj₀).pow 4
  obtain ⟨z₁, ⟨hz₁, hz₂, hz₃⟩, -⟩ := GlobalTheory.T.existsUnique_lift_coords_localSubring S G L U 4 n b R K f y x₁ cf j₀ u₀ hL hU hb hf hyU
    (by rw [← Category.assoc, hx₁, hx]) (by rw [hx₁]; exact hj₀)
    (fun i => by rw [hu₀]; exact hv i x₁ j₀ hx₁ hj₀) hcf
  have hz : spMap f ≫ z₁ ≫ (G.hom ⁻¹ᵁ U).ι = x := by rw [← Category.assoc, hz₂, hx₁]
  have hzy : (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ≫ G.hom = y := by rw [Category.assoc, hz₁]
  have hzU' : ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ (G.hom ⁻¹ᵁ U') := by
    rw [← Scheme.Hom.comp_preimage, hzy]
    exact hyU'
  obtain ⟨z₂, hz₄⟩ := exists_lift _ _ hzU'
  have key : ∀ j, ⊤ ≤ (z₁ ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ r : R, IsUnit r ∧ f r = τ j := by
    intro j hj
    have hxj : ⊤ ≤ x ⁻¹ᵁ L.U j := by rw [← hz]; exact le_comp _ _ _ hj
    obtain ⟨u, hu⟩ := hz₃ j hj
    obtain ⟨i, hi⟩ := hcf
    have h4 : f u = τ j ^ 4 := by
      have e := hv i x₁ j hx₁ hxj
      rw [← hz₂, HolHom.valR_spMap _ _ _ (le_powOver G L U 4 z₁ j hj), hu, map_mul] at e
      exact mul_left_cancel₀ (hi.map f).ne_zero e
    have e := hv' (spMap f ≫ z₂) j (by rw [Category.assoc, hz₄, hz]) hxj
    rw [HolHom.valR_spMap _ _ _ (le_powOver G L U' 5 z₂ j (by rw [hz₄]; exact hj))] at e
    obtain ⟨c, rfl⟩ := hcf'
    set a := valR z₂ ((Out.powOver G L U' 5).U (fun _ => j)) (b'.f (fun _ => j))
    have hc : f (↑c⁻¹ : R) * f c = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hu' : f (↑u⁻¹ : R) * f u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hr : f (↑c⁻¹ * ↑u⁻¹ * a) = τ j := by
      rw [map_mul, map_mul, e]
      rw [h4] at hu'
      linear_combination (f (↑u⁻¹ : R) * τ j ^ 5) * hc + τ j * hu'
    refine ⟨_, ?_, hr⟩
    have : (↑c⁻¹ * ↑u⁻¹ * a) ^ 4 = (u : R) := hf (by rw [map_pow, hr, h4])
    exact (isUnit_pow_iff (by norm_num : 4 ≠ 0)).1 (this ▸ u.isUnit)
  choose! σ hσ using key
  refine ⟨z₁ ≫ (G.hom ⁻¹ᵁ U).ι, σ, hzy, hz, ⟨fun j hj => (hσ j hj).1, fun j j' hj => hf ?_⟩,
    fun j hj => (hσ j hj).2⟩
  have h1 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_left : L.U j ⊓ L.U j' ≤ _))
  have h2 := hj.trans (Scheme.Hom.preimage_mono _ (inf_le_right : L.U j ⊓ L.U j' ≤ _))
  rw [map_mul, (hσ j h1).2, (hσ j' h2).2, ← HolHom.valR_spMap _ _ _ hj, hz]
  exact hτ.2 j j' (by rw [← hz]; exact le_comp _ _ _ hj)

theorem germs_local (Γ : Germs) (w : ℂ) : IsLocalRing (Γ.R w) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    by_cases h : Γ.ev w a = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, h, map_one, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)

theorem specPts_nonempty : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (k : Type) [CommRing k] (s₀ : S ⟶ Sp k) [LocallyOfFiniteType s₀] (b₀ : k →+* ℂ), y ≫ s₀ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp b₀) → AnFin A → Φ.Rational → Nonempty (SpecPts Φ Γ) := by
  intro h1 h2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ k _ s₀ _ b₀ hy hA hΦ
  classical
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_projCoords_convergent_coefficients h1 h2 E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨C'⟩ := GlobalTheory.T.nonempty_projCoords_convergent_coefficients h1 h2 E H D l B bb S s o A y Φ hA hΦ 5 (by norm_num)
  haveI := o.proper
  obtain ⟨x₀, hx₀⟩ := hΦ.1 0
  have hy₀ : spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) ≫ x₀ ≫ o.t.G.hom = y := by
    rw [← Category.assoc, hx₀]
    exact Over.w (Φ.x 0)
  set y₀ := x₀ ≫ o.t.G.hom
  have hin : ∀ U : S.Opens, ⊤ ≤ y ⁻¹ᵁ U → ⊤ ≤ y₀ ⁻¹ᵁ U := by
    intro U hU p _
    rw [← hy₀] at hU
    obtain rfl : p = spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (default : PrimeSpectrum ℂ⸨X⸩) :=
      Subsingleton.elim (α := PrimeSpectrum Conv.convLaurent) _ _
    exact hU (x := (default : PrimeSpectrum ℂ⸨X⸩)) trivial
  have hs₀ : y₀ ≫ s₀ = spMap ((algebraMap ℂ Conv.convLaurent).comp b₀) := by
    refine HolHom.point_ext (isAffineOpen_top _) le_top le_top fun g => Subtype.ext ?_
    have e1 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩) (y₀ ≫ s₀) ⊤ le_top g
    have e2 := HolHom.valR_spMap (algebraMap Conv.convLaurent ℂ⸨X⸩)
      (spMap ((algebraMap ℂ Conv.convLaurent).comp b₀)) ⊤ le_top g
    rw [← Category.assoc, hy₀, hy] at e1
    rw [← spMap_comp] at e2
    exact e1.symm.trans e2
  obtain ⟨T₁, hT₁, y₁, hy₁U, hy₁, -⟩ :=
    Conv.exists_halfRing_point s₀ b₀ y₀ hs₀ C.aff (hin _ C.mem) (max C.T C'.T)
  obtain ⟨T, hT, hU'⟩ := Conv.exists_le_preimage_inclusion y₁ (U := C'.U) (by rw [hy₁]; exact hin _ C'.mem)
  set yT := spMap (Subalgebra.inclusion (Conv.halfRing_mono hT) : Conv.halfRing T₁ →+* Conv.halfRing T) ≫ y₁ with hyT
  have hU : ⊤ ≤ yT ⁻¹ᵁ C.U := le_comp _ _ _ hy₁U
  have hgen : spMap (Conv.halfRing T).val.toRingHom ≫ yT = y := by
    rw [← hy₀, ← hy₁, hyT, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    rfl
  have hC : C.T ≤ T := ((le_max_left _ _).trans hT₁).trans hT
  have hC' : C'.T ≤ T := ((le_max_right _ _).trans hT₁).trans hT
  have key : ∀ (w : ℂ) (hw : T < w.im) (v : A.V), ∃ (z : Sp (Γ.R w) ⟶ o.t.G.left) (σ : o.t.PP.L.ι → Γ.R w),
      z ≫ o.t.G.hom = spMap (Subalgebra.inclusion (Γ.le T w hw)).toRingHom ≫ yT ∧
      spMap (Γ.R w).val.toRingHom ≫ z = (Φ.x v).left ∧ IsFrm o.t.PP.L z σ ∧
      ∀ j, ⊤ ≤ z ⁻¹ᵁ o.t.PP.L.U j → (Γ.R w).val.toRingHom (σ j) = Φ.τ v j := by
    intro w hw v
    haveI := germs_local Γ w
    have hw₁ := hC.trans_lt hw
    have hw₂ := hC'.trans_lt hw
    obtain ⟨i, hi⟩ := C.bpf w hw₁ v
    obtain ⟨i', hi'⟩ := C'.bpf w hw₂ v
    refine exists_ext o.t.G o.t.PP.L o.t.PP.isLB (Γ.R w).val.toRingHom Subtype.val_injective _ (Φ.x v).left ?_
      (Φ.τ v) (Φ.frm v) C.U C.aff (le_comp _ _ _ hU) C.b C.emb
      (fun i => Subalgebra.inclusion (Γ.le _ w hw₁) (C.cf i v)) ⟨i, Γ.unit w _ (by rw [Γ.ev_eq]; exact hi)⟩
      (fun i x' j => C.val i v x' j) C'.U (le_comp _ _ _ hU') (C'.b i')
      (Subalgebra.inclusion (Γ.le _ w hw₂) (C'.cf i' v)) (Γ.unit w _ (by rw [Γ.ev_eq]; exact hi'))
      (fun x' j => C'.val i' v x' j)
    rw [← Category.assoc, ← spMap_comp]
    exact (Over.w (Φ.x v)).trans hgen.symm
  choose z σ hz1 hz2 hz3 hz4 using key
  have hpi : ∀ (w : ℂ) (hw : T < w.im) (v : A.V),
      (spMap (Γ.ev w).toRingHom ≫ z w hw v) ≫ o.t.G.hom = Conv.halfCurve yT w := by
    intro w hw v
    rw [Category.assoc, hz1, ← Category.assoc, ← spMap_comp, Conv.halfCurve_eq yT hw]
    congr 2
    exact RingHom.ext fun r => Γ.ev_eq T w hw r
  exact ⟨{
    T := T
    yT := yT
    yT_gen := hgen
    xt := fun w hw v => Over.homMk (z w hw v) (hz1 w hw v)
    xt_gen := hz2
    τt := fun w v => if hw : T < w.im then σ w hw v else fun _ => 1
    τt_frm := fun w hw v => by rw [dite_eq_left hw]; exact hz3 w hw v
    τt_gen := fun w hw v j hj => by rw [dite_eq_left hw]; exact hz4 w hw v j hj
    yw := Conv.halfCurve yT
    yw_eq := fun w hw => Conv.halfCurve_eq yT hw
    pi := fun w v => if hw : T < w.im then Over.homMk (spMap (Γ.ev w).toRingHom ≫ z w hw v) (hpi w hw v) else 1
    pi_eq := fun w hw v => by rw [dite_eq_left hw]; rfl }⟩

end GlobalTheory.ArcPts.Special
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfRationalPoints
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecLevel

theorem eq_zero_of_rational_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → valR x U f = 0) : f = 0 := by
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
  exact ((Points.le_preimage_basicOpen_iff _ hU f).1 hb).ne_zero (h _ (pointOfClosedPoint_comp π y hc) hU)

theorem fib_fst {R : Type} [CommRing R] {S : Scheme.{0}} {G : Over S} {y : Sp R ⟶ S} (x : Over.mk y ⟶ G) :
    fib x ≫ pullback.fst G.hom y = x.left := pullback.lift_fst _ _ _

theorem sec_eq_zero {S : Scheme.{0}} (P : Out.PolAV S) {k : Type} [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (m : ℕ)
    (u : SecP P.L (pullback.fst P.A.hom y) m)
    (h : ∀ (x : Over.mk y ⟶ P.A) j, ⊤ ≤ x.left ⁻¹ᵁ P.L.U j → ArcPts.sval u (fib x) j = 0) (i) : u.f i = 0 := by
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (pullback P.A.hom y) :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom).geometrically_isIntegral y _ _
      (IsPullback.of_hasPullback P.A.hom y)
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine eq_zero_of_rational_points (pullback.snd P.A.hom y) _ _ fun x hx hU => ?_
  let a : Over.mk y ⟶ P.A := Over.homMk (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
    exact Category.id_comp _)
  have e : fib a = x := by
    apply pullback.hom_ext
    · exact fib_fst a
    · rw [hx]
      exact pullback.lift_snd _ _ _
  have := h a j fun p hp => Set.mem_iInter.1 (hU hp) 0
  rw [e] at this
  exact this

theorem pow_mem_Theta {O : Type} [CommRing O] [StarRing O] (A : AnArc O) {th : (Fin A.gB → ℂ) → ℂ}
    (h : th ∈ A.Theta 1 0) (n : ℕ) : th ^ (n + 1) ∈ A.Theta (n + 1) 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa [pow_succ] using A.mul_mem_Theta ih h

theorem map_nsmul_eq_pow {V M : Type} [AddGroup V] [Group M] (x : V → M) (h : ∀ v v', x (v + v') = x v * x v')
    (n : ℕ) (v : V) : x (n • v) = x v ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, SpecGroup.map_zero_eq_one x h]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem left_toUnit_comp {S : Scheme.{0}} {G T T' : Over S} (ξ : 𝟙_ (Over S) ⟶ G) (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom) : (toUnit T' ≫ ξ).left = r ≫ (toUnit T ≫ ξ).left := by
  rw [Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc, hr]

theorem exists_germ_shift {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (Γ : Germs) (k : ℕ) [NeZero k] :
    ∃ T₀ : ℝ, ∀ w : ℂ, T₀ < w.im → ∀ la : A.La, (∀ α, (k : ℤ) ∣ A.be la.y α) → ∀ α, ∀ th ∈ A.Theta k α, ∀ z,
      ∃ F : Γ.R w, IsFShift A k α th la z F ∧ Γ.ev w F = A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) := by
  obtain ⟨T₀, h₀⟩ := exists_formal_convergence O A
  refine ⟨T₀, fun w hw la hla α th hth z => ?_⟩
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  obtain ⟨hm, hev⟩ := ((h₀ T₀ le_rfl k).1 _ _ (A.shift_mem_Theta hth la)).1 z
  refine ⟨Subalgebra.inclusion (Γ.le T₀ w hw)
    (⟨_, Conv.single_mem_halfRing T₀ (A.be la.y α / k) (Complex.exp (A.lin la z))⟩ * ⟨_, hm⟩),
    ⟨⟨NeZero.ne k, hla α⟩, fun n => ?_⟩, ?_⟩
  · rw [Subalgebra.coe_inclusion, MulMemClass.coe_mul,
      ← A.FSumShift_eq k la (Int.mul_ediv_cancel' (hla α)).symm, AnArc.coeff_FSumShift]
    refine (finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_).symm
    rw [AnArc.mem_level, eq_sub_iff_add_eq]
  · rw [Γ.ev_eq T₀ w hw, map_mul, hev w hw, Conv.ev_single hw, ← AnArc.e_mul_intCast]
    obtain ⟨m, hm⟩ := hla α
    rw [A.Sum_add_Pw_div, hm, Int.mul_ediv_cancel_left _ (NeZero.ne (k : ℤ))]
    congr 3
    push_cast
    field_simp

theorem level_on_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (k : ℕ) [NeZero k], ∃ T' ≥ Ψ.T, ∀ w : ℂ, T' < w.im → Function.Surjective (Ψ.pi w) → (∀ la, Ψ.pi w (A.Pw w la) = 1) → ∀ (ξ : 𝟙_ (Over S) ⟶ o.t.G) (la : A.La), ξ ^ k = 1 → Φ.LevelPt k (toUnit _ ≫ ξ) la → toUnit _ ≫ ξ = Ψ.pi w ((k : ℂ)⁻¹ • A.Pw w la) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hR k _
  obtain ⟨T₁, hT₁, hsec⟩ := GlobalTheory.T.thetaSections_extend_germRings_and_span_fibres hL hL2 E H D l B bb S s o A y Φ Γ Ψ hA hR k
  obtain ⟨T₂, hsh⟩ := exists_germ_shift A Γ k
  obtain ⟨T₃, hT₃⟩ := A.exists_isConvLine
  refine ⟨max T₁ (max T₂ T₃), hT₁.trans (le_max_left _ _), fun w hw' surj per ξ la hξ hlev => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ : T₁ < w.im ∧ T₂ < w.im ∧ T₃ < w.im := by simpa using hw'
  have hw : Ψ.T < w.im := lt_of_le_of_lt hT₁ h₁
  obtain ⟨σt, hσt, σ₀, hσ₀, hval, hspan⟩ := hsec w hw h₁
  have hk : k ≠ 0 := NeZero.ne k
  obtain ⟨θ, hθ, hθ0⟩ := hA.2
  have hθk : θ ^ k ∈ A.Theta k 0 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact pow_mem_Theta A hθ n
  have hθk0 : θ ^ k ≠ 0 := fun e => hθ0 (funext fun z => pow_eq_zero_iff hk |>.1 (congrFun e z))
  have hv : ∀ α, ∀ th ∈ A.Theta k α, ∀ v j, ⊤ ≤ (Ψ.pi w v).left ⁻¹ᵁ o.t.PP.L.U j →
      ArcPts.sval (σ₀ α th) (fib (Ψ.pi w v)) j = A.Sum k α th w v * Ψ.fr w j v ^ k := fun α th hth v j hj =>
    hval α th hth v j (by rw [fib_fst]; exact hj)
  refine LevelUnique.torsion_eq_of_same_ratios hL hL2 E H D l B bb S s o ℂ (Ψ.yw w) A.V (Ψ.pi w) k _ _
    (fun _ => True) (σ₀ 0 (θ ^ k)) (Nat.one_le_iff_ne_zero.2 hk) ?_ ?_ (fun m _ u hu => ?_) ?_
    (fun _ _ _ _ => trivial) fun v _ t₁ t₂ j j' hj hj' => ?_
  · rw [← MonObj.comp_pow, hξ, MonObj.comp_one]
  · rw [← map_nsmul_eq_pow _ (SpecGroup.pi_add Ψ hw), ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hk), one_smul, per]
  · refine sec_eq_zero (objPolAV o) (Ψ.yw w) m u fun x j hj => ?_
    obtain ⟨v, rfl⟩ := surj x
    exact hu v j hj
  · obtain ⟨v, hv0⟩ := A.exists_Sum_ne_zero hk 0 hθk0 fun z => AnArc.summable_term hT₃ hk hθk h₃ (0, z)
    obtain ⟨j, hj⟩ := exists_chart o.t.PP.isLB ((Ψ.pi w v).left (default : PrimeSpectrum ℂ))
    have hj' := (HolHom.le_preimage_iff (Ψ.pi w v).left _).2 hj
    refine ⟨fun _ => j, fun e => ?_⟩
    have h0 : ArcPts.sval (σ₀ 0 (θ ^ k)) (fib (Ψ.pi w v)) j = 0 := by
      rw [ArcPts.sval, e]
      refine Points.valR_zero _ _ fun p hp => Set.mem_iInter.2 fun _ => ?_
      have := hj' hp
      rw [← fib_fst] at this
      exact this
    rw [hv 0 _ hθk v j hj'] at h0
    exact mul_ne_zero hv0 (pow_ne_zero _ ((SpecGroup.pi_frm Ψ hw v).1 j hj').ne_zero) h0
  · have e₀ : (Ψ.pi w v * (toUnit _ ≫ ξ)).left =
        spMap (Γ.ev w).toRingHom ≫ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left :=
      SpecGroup.left_mul_of_comp (T' := Over.mk (Ψ.yw w)) _ (SpecGroup.ev_base Ψ hw) (Ψ.pi_eq w hw v)
        (left_toUnit_comp ξ _ (SpecGroup.ev_base Ψ hw))
    have e₁ : (Φ.x v * (toUnit _ ≫ ξ)).left =
        spMap (Γ.R w).val.toRingHom ≫ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left :=
      SpecGroup.left_mul_of_comp (T' := Over.mk y) _ (SpecGroup.val_base Ψ hw) (Ψ.xt_gen w hw v).symm
        (left_toUnit_comp ξ _ (SpecGroup.val_base Ψ hw))
    have ht : ⊤ ≤ (Ψ.xt w hw v * (toUnit _ ≫ ξ)).left ⁻¹ᵁ o.t.PP.L.U j :=
      SpecGroup.le_preimage_of_unit (Γ.ev w).toRingHom (Γ.unit w) _ _ (e₀ ▸ hj)
    have hg : ⊤ ≤ (Φ.x v * (toUnit _ ≫ ξ)).left ⁻¹ᵁ o.t.PP.L.U j := by
      rw [e₁]
      exact fun p _ => ht (x := spMap (Γ.R w).val.toRingHom p) trivial
    have key : ∀ α α', ∀ th ∈ A.Theta k α, ∀ th' ∈ A.Theta k α',
        ArcPts.sval (σ₀ α th) (fib (Ψ.pi w v * (toUnit _ ≫ ξ))) j * A.Sum k α' th' w (v + (k : ℂ)⁻¹ • A.Pw w la) =
        ArcPts.sval (σ₀ α' th') (fib (Ψ.pi w v * (toUnit _ ≫ ξ))) j * A.Sum k α th w (v + (k : ℂ)⁻¹ • A.Pw w la) := by
      intro α α' th hth th' hth'
      obtain ⟨F, hF, hFe⟩ := hsh w h₂ la hlev.dvd α th hth v
      obtain ⟨F', hF', hFe'⟩ := hsh w h₂ la hlev.dvd α' th' hth' v
      have h := hlev.2.2 α α' th hth th' hth' v F F' j hF hF' hg
      rw [← hσt α th hth _ _ j e₁.symm ht, ← hσt α' th' hth' _ _ j e₁.symm ht, ← MulMemClass.coe_mul,
        ← MulMemClass.coe_mul, Subtype.val_inj] at h
      rw [hσ₀ α th _ _ j e₀ hj, hσ₀ α' th' _ _ j e₀ hj, ← hFe, ← hFe', ← map_mul, ← map_mul, h]
    obtain ⟨n₁, r₁, α₁, θ₁, m₁, s₁⟩ := hspan t₁
    obtain ⟨n₂, r₂, α₂, θ₂, m₂, s₂⟩ := hspan t₂
    rw [← SpecGroup.pi_add Ψ hw] at hj' ⊢
    rw [s₁ _ j hj, s₂ _ j hj, s₁ _ j' hj', s₂ _ j' hj', Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hv _ _ (m₁ b) _ j' hj', hv _ _ (m₂ a) _ j' hj']
    linear_combination (r₁ b * r₂ a * Ψ.fr w j' (v + (k : ℂ)⁻¹ • A.Pw w la) ^ k) * key _ _ _ (m₁ b) _ (m₂ a)

end GlobalTheory.SpecLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmpCongrOfExEq
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FamilyUnifComponentConst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory

theorem isHolTo_comp_fin_one {X : Scheme.{0}} {B : Set ℂ} {y : ℂ → (Sp ℂ ⟶ X)} (h : IsHolTo B y) :
    IsHolTo {b : Fin 1 → ℂ | b 0 ∈ B} (fun b => y (b 0)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun b : Fin 1 → ℂ => b 0) := continuous_apply (0 : Fin 1)
  refine ⟨h1.preimage hc, ?_⟩
  have hd : Differentiable ℂ (fun b : Fin 1 → ℂ => b 0) := differentiable_apply (0 : Fin 1)
  exact h2.comp hd.differentiableOn (fun b hb => hb)

theorem familyUnif_component_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)), IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ) → ∃ i, ∀ w : ℂ, T < w.im → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w := by
  intro E _ _ _ H _ D l Xo σ g ty Fu T yw hhol hσ
  classical
  set B : Set (Fin 1 → ℂ) := {b | T < (b 0).im} with hB
  have hBo : IsOpen B := isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))
  have hBc : IsPreconnected B := by
    have hc : Convex ℝ B := by
      have := (convex_halfSpace_im_gt T).is_linear_preimage
        (f := fun b : Fin 1 → ℂ => b 0) ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      exact this
    exact hc.isPreconnected
  have hy : IsHolTo B (fun b => yw (b 0)) := isHolTo_comp_fin_one hhol
  have hex : ∀ b : Fin 1 → ℂ, ∃ i : Fin Fu.n, b ∈ B → ∃ P, IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw (b 0) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨i, P, h⟩ := Fu.onto _ (hσ (b 0) hb)
      exact ⟨i, fun _ => ⟨P, h⟩⟩
    · exact ⟨⟨0, Fu.n_pos⟩, fun h => absurd h hb⟩
  choose c hc using hex
  have hcont : ContinuousOn c B := by
    intro b₀ hb₀
    obtain ⟨B', i, P, ho, hm, hsub, hP, hu⟩ := Fu.lift 1 B _ hBo (fun b hb => hσ (b 0) hb) hy b₀ hb₀
    have key : ∀ b ∈ B', c b = i := by
      intro b hb
      obtain ⟨Q, hQ, hQu⟩ := hc b (hsub hb)
      exact Fu.disj _ _ Q (P b) hQ (hP.1 b hb) (hQu.trans (hu b hb).symm)
    have hev : c =ᶠ[nhds b₀] fun _ => i := Filter.eventually_of_mem (ho.mem_nhds hm) key
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have h0 : (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I) ∈ B := by
    simp [hB]
  refine ⟨c (fun _ : Fin 1 => ((T + 1 : ℝ) : ℂ) * Complex.I), fun w hw => ?_⟩
  have hwB : (fun _ : Fin 1 => w) ∈ B := hw
  rw [hBc.constant hcont h0 hwB]
  exact hc _ hwB

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FibreComparison
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem fibre_comparison : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) , (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → ∃ T₀ : ℝ, ∀ (w : ℂ) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr, T₀ < w.im → IsPeriod (Fu.Di i) ty P → Fu.u i P = y₀ → IsFibAt A Xo.univ.t lin cst w y₀ π fr → Function.Surjective π ∧ ∃ (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La), (∀ v, (Fu.ex i P (h v)).left = (π v).left) ∧ (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧ ∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k := by
  intro _ _ E _ _ _ H _ D l Xo σ g ty Fu A lin cst halt hdim
  refine ⟨0, fun w i P y₀ π fr _ hP hy hF => ?_⟩
  subst hy
  have hrk : Module.finrank ℤ A.La = 2 * g := by
    rw [A.finrank_La, ← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex, hdim]
  obtain ⟨h, gam, h1, h2, h3, -, h5⟩ := fibre_hom_eq_exponential Fu i hP hdim hrk A.EF A.EF_bijective (A.Pw w) π
    hF.add hF.hol hF.per fr hF.fr_hol (fun j v hv => ((hF.frm v).1 j hv).ne_zero)
    (fun j j' v hv => (hF.frm v).2 j j' hv) (lin w) (cst w) (fun a j v hv => hF.fac a v j hv) (halt w)
  obtain ⟨h6, gamO, h7⟩ := h5 (fun e => A.actV e) hF.act (A.Pw_smul w)
  refine ⟨fun y => ?_, h.toContinuousLinearEquiv, gamO.symm, fun v => ?_, fun u => ?_, fun u v => ?_, h6⟩
  · obtain ⟨z, rfl⟩ := Fu.ex_onto i P hP y
    exact ⟨h.symm z, by rw [h1, h.apply_symm_apply]⟩
  · rw [h1]; rfl
  · change P u = h _
    rw [h2, ← h7, gamO.apply_symm_apply]
  · rw [← h3, ← h7, ← h7, gamO.apply_symm_apply, gamO.apply_symm_apply]

end GlobalTheory
end
end

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem cmp_congr_of_ex_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (hk : 0 < k) (a b : (Fu.Di i).La)
    (hab : Fu.ex i P ((k : ℂ)⁻¹ • P a) = Fu.ex i P ((k : ℂ)⁻¹ • P b)) : ∃ e, a = b + k • e := by
  have h1 : Fu.ex i P ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) = 1 := by
    have h2 := Fu.ex_add i P hP ((k : ℂ)⁻¹ • P a - (k : ℂ)⁻¹ • P b) ((k : ℂ)⁻¹ • P b)
    rw [sub_add_cancel, hab] at h2
    exact mul_eq_right.1 h2.symm
  obtain ⟨e, he⟩ := (Fu.ex_ker i P hP _).1 h1
  refine ⟨e, hP.2.1 ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [map_add (f := _), map_nsmul, he, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub, smul_inv_smul₀ hk', smul_inv_smul₀ hk']
  abel

theorem cmp_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (A : AnArc (𝓞 E)) (w : ℂ) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (y₀ : Sp ℂ ⟶ Xo.X) (hy : Fu.u i P = y₀)
    (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La)
    (hex : ∀ v, (Fu.ex i P (h v)).left = (π v).left) (hPg : ∀ u, P u = h (A.Pw w (gam u)))
    (k : ℕ) (hk : 0 < k) (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (a : (Fu.Di i).La) (la : A.La)
    (h1 : toUnit _ ≫ x = Fu.ex i P ((k : ℂ)⁻¹ • P a)) (h2 : toUnit _ ≫ x = π ((k : ℂ)⁻¹ • A.Pw w la)) :
    ∃ e, gam a = la + k • e := by
  subst hy
  have h3 : ∀ v, Fu.ex i P (h v) = π v := fun v => Over.OverMorphism.ext (hex v)
  obtain ⟨e, he⟩ := cmp_congr_of_ex_eq Fu i P hP k hk a (gam.symm la) (by
    rw [← h1, h2, ← h3, map_smul, hPg (gam.symm la), gam.apply_symm_apply])
  exact ⟨gam e, by rw [he, map_add (f := _), map_nsmul, gam.apply_symm_apply]⟩

theorem exists_cmp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (A : AnArc (𝓞 E)) (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ) (T : ℝ) (yw : ℂ → (Sp ℂ ⟶ Xo.X)) (π : ∀ w, A.V → (Over.mk (yw w) ⟶ Xo.univ.t.G)) (fr : ℂ → Xo.univ.t.PP.L.ι → A.V → ℂ) (laA laM : D.La → A.La), (inferInstance : StarRing (𝓞 E)) = H.starRing → (∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la') → Module.finrank ℂ A.V = g → IsHolTo {w : ℂ | T < w.im} yw → (∀ w : ℂ, T < w.im → yw w ≫ Xo.s = spMap σ ∧ IsFibAt A Xo.univ.t lin cst w (yw w) (π w) (fr w) ∧ (Function.Surjective (π w) → (∀ v, toUnit _ ≫ Xo.univ.etaA v = π w ((l.A : ℂ)⁻¹ • A.Pw w (laA v))) ∧ ∀ v ∈ idealPart D l, toUnit _ ≫ Xo.univ.eta v = π w ((l.M : ℂ)⁻¹ • A.Pw w (laM v)))) → ∃ K : Cmp Fu A yw π laA laM, T ≤ K.T := by
  intro hL hL2 E _ _ _ H _ D l Xo σ g ty Fu A lin cst T yw π fr laA laM hstar hlin hrk hhol hw
  obtain ⟨i, hi⟩ := GlobalTheory.familyUnif_component_const E H D l Xo σ g ty Fu T yw hhol fun w h => (hw w h).1
  obtain ⟨T₀, hT₀⟩ := GlobalTheory.fibre_comparison hL hL2 E H D l Xo σ g ty Fu A lin cst hlin hrk
  obtain ⟨T₁, hT₁⟩ := A.exists_BwMat_posDef
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le

  have key : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      ∃ (P : (Fu.Di i).La →+ (Fin g → ℂ)) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La),
        IsPeriod (Fu.Di i) ty P ∧ Fu.u i P = yw w ∧ (∀ v, (Fu.ex i P (h v)).left = (π w v).left) ∧
        (∀ u, P u = h (A.Pw w (gam u))) ∧ (∀ u v, A.EF (gam u) (gam v) = (Fu.Di i).EF u v) ∧
        (∀ (e : 𝓞 E) v k, h (A.actV e v) k = ty k (e : E) * h v k) ∧
        (∀ v, ∃ e, gam (Fu.t i v) = laA v + l.A • e) ∧
        ∀ v ∈ idealPart D l, ∃ e, gam (Fu.t i v) = laM v + l.M • e := by
    intro w hwT
    have h1 : T < w.im := lt_of_le_of_lt (le_max_left _ _) hwT
    have h2 : T₀ < w.im := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hwT
    obtain ⟨P, hP, hu⟩ := hi w h1
    obtain ⟨-, hfib, hlev⟩ := hw w h1
    obtain ⟨hs, h, gam, hex, hPg, hEF, hact⟩ := hT₀ w i P (yw w) (π w) (fr w) h2 hP hu hfib
    obtain ⟨hA, hMM⟩ := hlev hs
    exact ⟨P, h, gam, hP, hu, hex, hPg, hEF, hact,
      fun v => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.A l.A_pos _ _ _ (Fu.ex_etaA i P hP v) (hA v),
      fun v hv => cmp_level Fu A w i P hP _ hu (π w) h gam hex hPg l.M hM _ _ _ (Fu.ex_eta i P hP v hv) (hMM v hv)⟩
  obtain ⟨-, h₁, gam₁, -, -, -, -, hEF₁, hact₁, hA₁, hM₁⟩ :=
    key (((max T (max T₀ T₁) + 1 : ℝ) : ℂ) * Complex.I) (by simp)
  let Pw : ℂ → ((Fu.Di i).La →+ (Fin g → ℂ)) := fun w =>
    (h₁.toLinearEquiv.toLinearMap.toAddMonoidHom.comp (A.Pw w)).comp gam₁.toLinearMap.toAddMonoidHom
  have hPw : ∀ w u, Pw w u = h₁ (A.Pw w (gam₁ u)) := fun _ _ => rfl
  have hper : ∀ w : ℂ, max T (max T₀ T₁) < w.im → IsPeriod (Fu.Di i) ty (Pw w) := fun w hwT =>
    A.isPeriod (hT₁ w (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hwT)) (Fu.Di i) ty
      h₁.toLinearEquiv hact₁ gam₁.toAddEquiv (fun a x => gam₁.map_smul a x) hEF₁ (Pw w) (hPw w)
  have hmod : ∀ (gam : (Fu.Di i).La ≃ₗ[𝓞 E] A.La) (k : ℕ) (a : (Fu.Di i).La) (la : A.La),
      (∃ e, gam a = la + k • e) → (∃ e, gam₁ a = la + k • e) → ∃ e, (gam.trans gam₁.symm) a = a + k • e := by
    rintro gam k a la ⟨e, he⟩ ⟨e₁, he₁⟩
    refine ⟨gam₁.symm (e - e₁), gam₁.injective ?_⟩
    rw [LinearEquiv.trans_apply, gam₁.apply_symm_apply, map_add (f := _), map_nsmul, gam₁.apply_symm_apply, he, he₁, smul_sub]
    abel
  have hrig : ∀ w : ℂ, max T (max T₀ T₁) < w.im →
      Fu.u i (Pw w) = yw w ∧ ∀ v, (Fu.ex i (Pw w) (h₁ v)).left = (π w v).left := by
    intro w hwT
    obtain ⟨P, h, gam, hP, hu, hex, hPg, hEF, -, hA, hMM⟩ := key w hwT
    obtain ⟨r1, r2⟩ := GlobalTheory.T.exp_eq_of_isometry_matching_markings E H D l Xo σ g ty Fu i P (Pw w) (gam.trans gam₁.symm)
      (h.symm.trans h₁).toLinearEquiv hstar hP (hper w hwT)
      (fun u v => by
        rw [← hEF₁, LinearEquiv.trans_apply, LinearEquiv.trans_apply, gam₁.apply_symm_apply, gam₁.apply_symm_apply, hEF])
      (fun v hv => hmod gam _ _ _ (hMM v hv) (hM₁ v hv)) (fun v => hmod gam _ _ _ (hA v) (hA₁ v))
      (fun u => by rw [hPw, hPg]; simp)
    refine ⟨r1.symm.trans hu, fun v => ?_⟩
    have := r2 (h v)
    rw [hex] at this
    rw [← this]
    simp
  exact ⟨⟨i, max T (max T₀ T₁), gam₁, h₁, hEF₁, hact₁, Pw, hPw, hper, fun w hwT => (hrig w hwT).1,
    fun w hwT => (hrig w hwT).2, hA₁, hM₁⟩, le_max_left _ _⟩

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CardQkOfTateIsoQ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.ArcPts
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

theorem card_qk_pre (hL : Out.Laws) (hL2 : Out.Laws2) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (D₀ : Out.DegPre R) (hB : D₀.TauBimult) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (k : ℕ) (hk : (k : F) ≠ 0) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ (2 * (D₀.rank + D₀.P.g)) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk Nat.cast_zero
  have h₁ := (GlobalTheory.GtCount.card_gtTors hL hL2 R D₀ F k hk).1
  simp only [GlobalTheory.GtCount.gtTors_iff] at h₁
  open ReciprocityTheory.ChartRestriction.G.Out in
  have hc : Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) =
      k ^ D₀.rank * Nat.card {g : GtPtF D₀ F // k • g = 0} := by
    open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR in
      let iota : D₀.X →+ GtPtF D₀ F := AddMonoidHom.mk' (fun x => (exists_iota (F := F) hB x).choose) fun x x' => by
        obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x).choose_spec
        obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB x').choose_spec
        obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := F) hB (x + x')).choose_spec
        refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
        have C : IsCub (th D₀ (T := TF (R := R) F) y J) := isCub_cubV D₀.cub hJ
        rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
        exact tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
      have hi (x : D₀.X) : GtPtF.IsIota x (iota x) := (exists_iota (F := F) hB x).choose_spec
      have he (x : D₀.X) (g : GtPtF D₀ F) : GtPtF.IsIota x g ↔ g = iota x :=
        ⟨fun h => isIota_unique h (hi x), fun h => h ▸ hi x⟩
      let qkMk (y : D₀.X) (g : GtPtF D₀ F) (h : k • g = iota y) : QkPt D₀ F k :=
        ⟨y, g, k • g, (isNsmul_iff_eq _ _ _).2 rfl, (he _ _).2 h⟩
      have qk_nsmul (p : QkPt D₀ F k) : k • p.g = iota p.y := by
        obtain ⟨h, h₁, h₂⟩ := p.eq
        exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((he _ _).1 h₂)
      have equiv_iff (p p' : QkPt D₀ F k) : QkPt.Equiv D₀ F p p' ↔ ∃ z : D₀.X, p'.y = p.y + k • z ∧ p'.g = p.g + iota z :=
        exists_congr fun z => and_congr Iff.rfl
          ⟨fun ⟨_, h₁, h₂⟩ => ((isAdd_iff_eq _ _ _).1 h₂).trans (congrArg (p.g + ·) ((he _ _).1 h₁)),
           fun h => ⟨_, hi z, (isAdd_iff_eq _ _ _).2 h⟩⟩
      have hd : ∀ y : D₀.X, ∃ g : GtPtF D₀ F, k • g = iota y :=
        fun y => exists_nsmul_eq hL.mulN (Or.inl inferInstance) hk0 _
      choose r hr using hd
      let K : AddSubgroup D₀.X := (nsmulAddMonoidHom k : D₀.X →+ D₀.X).range
      have hK : Nat.card (D₀.X ⧸ K) = k ^ D₀.rank := AddSubgroup.index_range_nsmul D₀.X k
      let f : (D₀.X ⧸ K) × {g : GtPtF D₀ F // k • g = 0} → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x =>
        Quot.mk _ (qkMk x.1.out (r x.1.out + x.2.1) (by rw [nsmul_add, hr, x.2.2, add_zero]))
      rw [← hK, ← Nat.card_prod]
      refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
      · rintro ⟨c, t⟩ ⟨c', t'⟩ h
        obtain ⟨z, hy, hg⟩ := (equiv_iff _ _).1 ((equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact h))
        change c'.out = c.out + k • z at hy
        change r c'.out + t'.1 = r c.out + t.1 + iota z at hg
        obtain rfl : c = c' := by
          rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
          exact ⟨z, by rw [hy, neg_add_cancel_left]; rfl⟩
        have hz : z = 0 := by
          have h0 : (k : ℤ) • z = 0 := by rw [natCast_zsmul]; exact left_eq_add.1 hy
          exact (smul_eq_zero.1 h0).resolve_left (by exact_mod_cast hk0)
        rw [hz, map_zero, add_zero, add_right_inj] at hg
        exact Prod.ext rfl (Subtype.ext hg.symm)
      · rintro ⟨p⟩
        obtain ⟨z, hz⟩ : -p.y + (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out ∈ K := by
          rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
        have hy : (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out = p.y + k • z := by
          rw [show k • z = _ from hz, add_neg_cancel_left]
        refine ⟨⟨QuotientAddGroup.mk p.y, p.g + iota z - r (QuotientAddGroup.mk p.y : D₀.X ⧸ K).out, ?_⟩,
          (Quot.sound ((equiv_iff _ _).2 ⟨z, hy, ?_⟩)).symm⟩
        · rw [nsmul_sub, hr, hy, nsmul_add, qk_nsmul, map_add (f := _), map_nsmul, sub_self]
        · exact add_sub_cancel _ _
  rw [hc, h₁, ← pow_add]
  congr 1
  ring

theorem card_qk_of_tateIsoQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {R : Type} [CommRing R] [IsDomain R] {D₀ : Out.DegPre R} [Module (𝓞 E) D₀.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hB : D₀.TauBimult) (I : TateIsoQ D D₀ oa F) (k : ℕ) (hk : 0 < k) :
    Nat.card (Quot (Out.QkPt.Equiv D₀ F (k := k))) = k ^ Module.finrank ℤ D.La := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have := datum_free_int D
  let K : AddSubgroup D.La := (nsmulAddMonoidHom k : D.La →+ D.La).range
  have hK : Nat.card (D.La ⧸ K) = k ^ Module.finrank ℤ D.La := AddSubgroup.index_range_nsmul D.La k
  have hE := equiv_equivalence (D := D₀) (F := F) (k := k) hB
  let f : D.La ⧸ K → Quot (Out.QkPt.Equiv D₀ F (k := k)) := fun x => Quot.mk _ (I.ev k x.out)
  rw [← hK]
  refine (Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro x x' h
    obtain ⟨e, he⟩ := (I.ker k hk _ _).1 (hE.symm (hE.eqvGen_iff.1 (Quot.eqvGen_exact h)))
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x', QuotientAddGroup.eq]
    exact ⟨e, by rw [he, neg_add_cancel_left]; rfl⟩
  · rintro ⟨p⟩
    obtain ⟨v, hv⟩ := I.onto k hk p
    obtain ⟨e, he⟩ : -v + (QuotientAddGroup.mk v : D.La ⧸ K).out ∈ K := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    refine ⟨QuotientAddGroup.mk v, Quot.sound (hE.trans ((I.ker k hk _ _).2 ⟨e, ?_⟩) hv)⟩
    rw [show k • e = _ from he, add_neg_cancel_left]

theorem finrank_V_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) → Module.finrank ℂ Λ.A.V = g := by
  intro hL hL2 E _ _ _ H _ D l c O _ β _ _ b a Λ g ty hty ⟨r, z, hr, hz⟩
  obtain ⟨-, I, -⟩ := a.geom ℂ r z hr hz _ rfl
  have h₁ := card_qk_pre hL hL2 a.D₀ a.bimult ℂ 2 (by norm_num)
  rw [card_qk_of_tateIsoQ a.bimult I 2 two_pos, datum_finrank_int,
    ← (GlobalTheory.PeriodExists.period_of_isTypeFn H D g ty hty).1] at h₁
  have h₂ := Nat.pow_right_injective le_rfl h₁
  have h₃ : Module.finrank ℤ Λ.A.X = a.D₀.rank := (Λ.ε.toAddEquiv.toIntLinearEquiv).finrank_eq
  rw [Λ.A.finrank_V, h₃, Λ.gB_eq]
  omega

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsFactor
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_isFactor : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∃ (lin : ℂ → A.La → A.V →ₗ[ℂ] ℂ) (cst : ℂ → A.La → ℂ), IsFactor A lin cst ∧ ∀ w la la', lin w la (A.Pw w la') - lin w la' (A.Pw w la) = -(2 * Real.pi * Complex.I) * A.EF la la' := by
  intro O _ _ A
  refine ⟨fun _ la => A.lin la, A.logConst, fun w la v j α th h m => ?_, fun w la la' => ?_⟩
  · rw [A.term_add_period h w la m v, A.perFactor_eq_exp, A.L_apply]
  · rw [A.lin_Pw_sub]; ring

end GlobalTheory.ArcPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section
namespace GlobalTheory.GermRing
open GlobalTheory.Conv

def Rep (w : ℂ) (f : ℂ⸨X⸩) (x : ℂ) : Prop :=
  ∃ (T : ℝ) (hw : T < w.im) (a s : halfRing T),
    ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s

theorem Rep.common {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hf : Rep w f x) (hg : Rep w g y) :
    ∃ (T : ℝ) (hw : T < w.im) (a s b t : halfRing T),
      (ev T w hw s ≠ 0 ∧ (s : ℂ⸨X⸩) * f = a ∧ ev T w hw a = x * ev T w hw s) ∧
      (ev T w hw t ≠ 0 ∧ (t : ℂ⸨X⸩) * g = b ∧ ev T w hw b = y * ev T w hw t) := by
  obtain ⟨T, hw, a, s, h⟩ := hf
  obtain ⟨T', hw', b, t, h'⟩ := hg
  exact ⟨max T T', max_lt hw hw', ⟨a, halfRing_mono (le_max_left _ _) a.2⟩,
    ⟨s, halfRing_mono (le_max_left _ _) s.2⟩, ⟨b, halfRing_mono (le_max_right _ _) b.2⟩,
    ⟨t, halfRing_mono (le_max_right _ _) t.2⟩, h, h'⟩

theorem Rep.unique {w : ℂ} {f : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w f y) : x = y := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  have e : a * t = b * s := Subtype.ext (by
    push_cast
    rw [← h2, ← k2]; ring)
  have e' := congrArg (ev T w hw) e
  rw [map_mul, map_mul, h3, k3] at e'
  apply mul_right_cancel₀ (mul_ne_zero h1 k1)
  linear_combination e'

theorem Rep.add {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f + g) (x + y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * t + b * s, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_add (f := _), map_mul, map_mul, map_mul, h3, k3]; ring

theorem Rep.mul {w : ℂ} {f g : ℂ⸨X⸩} {x y : ℂ} (hx : Rep w f x) (hy : Rep w g y) :
    Rep w (f * g) (x * y) := by
  obtain ⟨T, hw, a, s, b, t, ⟨h1, h2, h3⟩, k1, k2, k3⟩ := hx.common hy
  refine ⟨T, hw, a * b, s * t, by rw [map_mul]; exact mul_ne_zero h1 k1, ?_, ?_⟩
  · push_cast
    rw [← h2, ← k2]; ring
  · rw [map_mul, map_mul, h3, k3]; ring

theorem rep_of_mem {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    Rep w (s : ℂ⸨X⸩) (ev T w hw s) :=
  ⟨T, hw, s, 1, by rw [map_one]; exact one_ne_zero, by simp, by rw [map_one, _root_.mul_one]⟩

theorem rep_algebraMap (w c : ℂ) : Rep w (algebraMap ℂ ℂ⸨X⸩ c) c := by
  have hw : w.im - 1 < w.im := sub_one_lt _
  have h := rep_of_mem hw (algebraMap ℂ (halfRing (w.im - 1)) c)
  rw [AlgHom.commutes] at h
  exact h

theorem Rep.inv {w : ℂ} {f : ℂ⸨X⸩} {x : ℂ} (hx : Rep w f x) (h0 : x ≠ 0) :
    ∃ g, Rep w g x⁻¹ ∧ f * g = 1 := by
  obtain ⟨T, hw, a, s, h1, h2, h3⟩ := hx
  have ha : ev T w hw a ≠ 0 := by rw [h3]; exact mul_ne_zero h0 h1
  have ha' : (a : ℂ⸨X⸩) ≠ 0 := fun h => ha (by rw [show a = 0 from Subtype.ext h, map_zero])
  have hf : f ≠ 0 := fun h => ha' (by rw [← h2, h, mul_zero])
  refine ⟨f⁻¹, ⟨T, hw, s, a, ha, ?_, ?_⟩, mul_inv_cancel₀ hf⟩
  · rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hf, _root_.mul_one]
  · rw [h3, ← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]

def ring (w : ℂ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {f | ∃ x, Rep w f x}
  mul_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.mul hy⟩
  add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, hx.add hy⟩
  algebraMap_mem' c := ⟨c, rep_algebraMap w c⟩

def val (w : ℂ) (f : ring w) : ℂ := Classical.choose (show ∃ x, Rep w f x from f.2)

theorem rep_val (w : ℂ) (f : ring w) : Rep w f (val w f) := Classical.choose_spec (show ∃ x, Rep w f x from f.2)

def evRing (w : ℂ) : ring w →ₐ[ℂ] ℂ where
  toFun := val w
  map_one' := (rep_val w 1).unique (by simpa using rep_algebraMap w 1)
  map_mul' f g := (rep_val w (f * g)).unique ((rep_val w f).mul (rep_val w g))
  map_zero' := (rep_val w 0).unique (by simpa using rep_algebraMap w 0)
  map_add' f g := (rep_val w (f + g)).unique ((rep_val w f).add (rep_val w g))
  commutes' c := (rep_val w _).unique (rep_algebraMap w c)

def germs : Germs where
  R := ring
  ev := evRing
  unit w s hs := by
    obtain ⟨g, hg, h⟩ := (rep_val w s).inv hs
    exact IsUnit.of_mul_eq_one (⟨g, _, hg⟩ : ring w) (Subtype.ext h)
  le T w hw f hf := ⟨_, rep_of_mem hw ⟨f, hf⟩⟩
  ev_eq T w hw s := (rep_val w _).unique (rep_of_mem hw s)
  frac w f := by
    obtain ⟨T, hw, a, s, h1, h2, -⟩ := rep_val w f
    exact ⟨T, hw, a, s, h1, h2⟩

theorem germs_spec : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  refine ⟨⟨germs⟩, fun Γ w => ⟨?_, fun f => ?_, fun f g hf h => ?_⟩⟩
  · refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
    by_cases h : Γ.ev w f = 0
    · exact Or.inr (Γ.unit w _ (by rw [map_sub, map_one, h, sub_zero]; exact one_ne_zero))
    · exact Or.inl (Γ.unit w _ h)
  · obtain ⟨T, hw, a, s, h1, h2⟩ := Γ.frac w f
    have hs : (s : ℂ⸨X⸩) ≠ 0 := fun h => h1 (by rw [show s = 0 from Subtype.ext h, map_zero])
    have e : (f : ℂ⸨X⸩) = (s : ℂ⸨X⸩)⁻¹ * a := by
      rw [← h2, ← _root_.mul_assoc, inv_mul_cancel₀ hs, _root_.one_mul]
    rw [e]
    exact mul_mem (convLaurent.inv_mem (halfRing_le_convLaurent T s.2)) (halfRing_le_convLaurent T a.2)
  · obtain ⟨k, hk⟩ := (Γ.unit w f hf).exists_left_inv
    have hk' : (k : ℂ⸨X⸩) * f = 1 := congrArg Subtype.val hk
    have e : g = k * (f * g) := by rw [← _root_.mul_assoc, hk', _root_.one_mul]
    rw [e]
    exact mul_mem k.2 h

end GlobalTheory.GermRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermsSpecStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_germs_localRing_convergent_divisible : Nonempty Germs ∧ ∀ (Γ : Germs) (w : ℂ), IsLocalRing (Γ.R w) ∧ (∀ f : Γ.R w, (f : ℂ⸨X⸩) ∈ Conv.convLaurent) ∧ ∀ (f : Γ.R w) (g : ℂ⸨X⸩), Γ.ev w f ≠ 0 → (f : ℂ⸨X⸩) * g ∈ Γ.R w → g ∈ Γ.R w := by
  first | exact @GlobalTheory.GermRing.germs_spec | exact GlobalTheory.GermRing.germs_spec | (intros; apply GlobalTheory.GermRing.germs_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToHalfPlaneMono
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory.HolomorphicArc

theorem map_nsmul_eq_pow {L G : Type} [AddCommGroup L] [Group G] (f : L → G) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.1 h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem nsmul_mem (v : D.La) : l.M • v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  have h' : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left h
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul h' Submodule.mem_top

theorem over_of_generic {S : Scheme.{0}} {k : Type} [CommRing k] (s : S ⟶ Sp k) (σ : k →+* ℂ)
    (R : Subalgebra ℂ ℂ⸨X⸩) (y : Sp R ⟶ S) (ev : R →ₐ[ℂ] ℂ)
    (h : (spMap R.val.toRingHom ≫ y) ≫ s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ)) :
    (spMap ev.toRingHom ≫ y) ≫ s = spMap σ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ s)
  have h₁ : y ≫ s = spMap φ.hom := hφ.symm
  rw [Category.assoc, h₁, ← spMap_comp] at h ⊢
  have h₂ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  congr 1
  ext x
  have h₃ : φ.hom x = algebraMap ℂ R (σ x) := Subtype.ext (DFunLike.congr_fun h₂ x)
  exact (congrArg ev h₃).trans (ev.commutes _)

theorem isHolTo_halfPlane_mono {X : Scheme.{0}} {y : ℂ → (Sp ℂ ⟶ X)} {T T' : ℝ} (h : T ≤ T')
    (hol : IsHolTo {w : ℂ | T < w.im} y) : IsHolTo {w : ℂ | T' < w.im} y := by
  intro U f
  have e : {b | b ∈ {w : ℂ | T' < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} =
      {w : ℂ | T' < w.im} ∩ {b | b ∈ {w : ℂ | T < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => ⟨fun hb => ⟨hb.1, h.trans_lt hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
  rw [e]
  exact ⟨(isOpen_lt continuous_const Complex.continuous_im).inter (hol U f).1,
    (hol U f).2.mono Set.inter_subset_right⟩

end GlobalTheory.HolomorphicArc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisation
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.HolomorphicArc

theorem main : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  intro L₁ L₂ hU E _ _ _ H D l Xo c O _ β Y bF _ _ a χ W g ty Fu _ hty hrz hχ hgen
  letI := H.starRing
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  haveI := Xo.smooth
  haveI : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  haveI : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨Λ⟩ := GlobalTheory.ArcModel.nonempty_gtAn L₁ L₂ hU E H D l c O β _ a
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_chain_arc_witness_universal_family L₁ L₂ E H D l Xo c O β Y bF a χ W Λ hχ hgen
  choose laA hA using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.A l.A_pos).1 (a.etaA v)
  choose laM hM using fun v => (GlobalTheory.GtRep.exists_rep_and_shift L₁ L₂ E H D l c O β _ a Λ l.M (le_trans (by norm_num) l.three_le)).1 (a.eta v)
  obtain ⟨levA, levM⟩ := GlobalTheory.ArcPts.chain_levels L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C laA laM hA hM
  have hfin : AnFin Λ.A := (GlobalTheory.ArcThetaSpaces.sections_theta L₁ L₂ E H D l c O β _ a Λ).2.1
  have hover : (C.yF ≫ pullback.fst _ _) ≫ Xo.s =
      spMap ((algebraMap ℂ ℂ⸨X⸩).comp (bF.comp (IntermediateField.inclusion c.le).toRingHom)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.yF_over, ← spMap_comp]
  have hrat : C.Φ.Rational := GlobalTheory.ConstRational.rational L₁ L₂ E H D l Xo Λ.A _ _ C.Φ laA laM hfin hover levA levM
  obtain ⟨Γ⟩ := GlobalTheory.T.exists_germs_localRing_convergent_divisible.1
  obtain ⟨Ψ⟩ := GlobalTheory.ArcPts.Special.specPts_nonempty L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ _ Xo.s _ hover hfin hrat
  obtain ⟨lin, cst, hfac, hEF⟩ := GlobalTheory.ArcPts.exists_isFactor _ Λ.A
  obtain ⟨T₁, hT₁, hol, hfib⟩ :=
    GlobalTheory.SpecFibre.specPts_isFibAt L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat lin cst hfac
  obtain ⟨TA, -, hlA⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.A
  obtain ⟨TM, -, hlM⟩ := GlobalTheory.SpecLevel.level_on_fibre L₁ L₂ E H D l _ _ Xo.X Xo.s Xo.univ Λ.A _ C.Φ Γ Ψ hfin hrat l.M
  have hdim := GlobalTheory.ArcPts.finrank_V_eq L₁ L₂ E H D l c O β _ a Λ g ty hty hrz
  have hol' : IsHolTo {w : ℂ | max T₁ (max TA TM) < w.im} Ψ.yw := isHolTo_halfPlane_mono (le_max_left _ _) hol
  obtain ⟨K, -⟩ := GlobalTheory.ArcPts.exists_cmp L₁ L₂ E H D l Xo _ g ty Fu Λ.A lin cst (max T₁ (max TA TM)) Ψ.yw Ψ.pi Ψ.fr laA laM
    rfl hEF hdim hol' (by
      intro w hw
      simp only [max_lt_iff] at hw
      obtain ⟨h₁, h₂, h₃⟩ := hw
      refine ⟨?_, hfib w h₁, fun hs => ⟨fun v => hlA w h₂ hs (hfib w h₁).per _ _ ?_ (levA v),
        fun v hv => hlM w h₃ hs (hfib w h₁).per _ _ ?_ (levM v hv)⟩⟩
      · rw [Ψ.yw_eq w (hT₁.trans_lt h₁)]
        exact over_of_generic _ _ _ _ _ (by rw [Ψ.yT_gen]; exact hover)
      · rw [← map_nsmul_eq_pow _ Xo.univ.etaA_add, Xo.univ.etaA_ker]
      · rw [← map_nsmul_eq_pow _ Xo.univ.eta_add, Xo.univ.eta_ker _ (nsmul_mem v)])
  exact GlobalTheory.ArcPts.nonempty_holArc L₁ L₂ E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib

end GlobalTheory.HolomorphicArc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degenerationArc_of_uniformisation : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  first | exact @GlobalTheory.HolomorphicArc.main | exact GlobalTheory.HolomorphicArc.main | (intros; apply GlobalTheory.HolomorphicArc.main <;> assumption)
end
