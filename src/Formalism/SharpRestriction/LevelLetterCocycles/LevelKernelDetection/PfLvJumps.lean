module

public import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfMembership

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvJumps
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

section Jumps

variable {T : LocLat G Qp LL O}

theorem pfLvJumps_act (g : G) (z : T.V ⊗[Qp] B) :
    actVdR PD T.ρ g (ιV PD (LL := LL) (V := T.V) z) = ιV PD (LL := LL) (V := T.V) (actVB PD T.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVdR, actVB, ιV, PD.ι_comm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem pfLvJumps_mul (c : K₀) (z : T.V ⊗[Qp] B) :
    mulVdR (K := K) (BdR := BdR) (V := T.V) (LL := LL) (algebraMap K₀ K c) (ιV PD (LL := LL) (V := T.V) z) =
      ιV PD (LL := LL) (V := T.V) (mulVB (K₀ := K₀) (B := B) (V := T.V) (LL := LL) c z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    simp [mulVdR, mulVB, ιV, map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem pfLvJumps_dcrisL (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL)
    (τ : K →ₐ[Qp] LL) (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀) (z : T.V ⊗[Qp] B)
    (hz : z ∈ DcrisL PD T.ρ τ₀) : ιV PD (LL := LL) (V := T.V) z ∈ DdRE PD T.ρ τ := by
  rw [DcrisL, Submodule.mem_inf] at hz
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz1
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hz2
  rw [DdRE, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro g
    rw [pfLvJumps_act, hz1 g]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro c
    obtain ⟨c', rfl⟩ := hK c
    have hτc : τ (algebraMap K₀ K c') = τ₀ c' := by
      rw [← hτ]
      rfl
    rw [pfLvJumps_mul, hz2 c', map_smul, hτc]

theorem pfLvJumps_fil (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL)
    (τ : K →ₐ[Qp] LL) (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀) (a : ℤ)
    (h : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a) :
    FilCris PD T.ρ a ⊓ DcrisL PD T.ρ τ₀ = FilCris PD T.ρ (a + 1) ⊓ DcrisL PD T.ρ τ₀ := by
  have key : ∀ b b' : ℤ, FildR PD T.ρ τ b ≤ FildR PD T.ρ τ b' →
      FilCris PD T.ρ b ⊓ DcrisL PD T.ρ τ₀ ≤ FilCris PD T.ρ b' ⊓ DcrisL PD T.ρ τ₀ := by
    intro b b' hbb x hx
    rw [Submodule.mem_inf, FilCris, Submodule.mem_inf, Submodule.mem_comap] at hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    have hd : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ b :=
      (Submodule.mem_inf).2 ⟨pfLvJumps_dcrisL hK τ₀ τ hτ x hx3, hx2⟩
    have hd' := ((Submodule.mem_inf).1 (hbb hd)).2
    exact (Submodule.mem_inf).2 ⟨(Submodule.mem_inf).2 ⟨hx1, hd'⟩, hx3⟩
  exact le_antisymm (key a (a + 1) h.ge) (key (a + 1) a h.le)

theorem pfLvJumps_filD (c : ZMod n) (s : ℕ) (u : ℤ)
    (h : FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n))) =
      FilCris PD T.ρ (u + 1) ⊓ DcrisL PD T.ρ (W.emb (c - (s : ZMod n)))) :
    FilD W T c s u = FilD W T c s (u + 1) := by
  unfold FilD FilLev
  rw [h]

theorem pfLvJumps_over (hK : Function.Surjective (algebraMap K₀ K)) (τ₀ : K₀ →ₐ[Qp] LL) :
    ∃ τ : K →ₐ[Qp] LL, τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = τ₀ := by
  let e : K₀ ≃ₐ[Qp] K :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) ⟨(algebraMap K₀ K).injective, hK⟩
  refine ⟨τ₀.comp e.symm.toAlgHom, ?_⟩
  ext c
  exact congrArg τ₀ (e.symm_apply_apply c)

theorem pfLvJumps_win (hK : Function.Surjective (algebraMap K₀ K)) (G₀ Sz η : ℕ) (ty : ZMod n → LT)
    (hJ : KindJumps PD T W.emb G₀ Sz η ty) (c : ZMod n) (s : ℕ) (u : ℤ)
    (hu : FilD W T c s u ≠ FilD W T c s (u + 1)) : u ∈ (ty (c - (s : ZMod n))).win G₀ Sz η := by
  obtain ⟨τ, hτ⟩ := pfLvJumps_over hK (W.emb (c - (s : ZMod n)))
  refine hJ (c - (s : ZMod n)) τ hτ u ?_
  intro h
  exact hu (pfLvJumps_filD c s u (pfLvJumps_fil hK _ τ hτ u h))

theorem jumps_holds (hK : Function.Surjective (algebraMap K₀ K)) (c : ZMod n) (ell : ℕ)
    (G₀ Sz η : ℕ) (ty : ZMod n → LT) (hJ : KindJumps PD T W.emb G₀ Sz η ty) :
    ∀ s < ell, Formalism.ExponentWindows.G.Jumps (E.kindAt (kdOf ty) c s) G₀ Sz η (E.sizeAt (bbOf ty) c s) (FilD W T c s) := by
  intro s _
  have hw := pfLvJumps_win hK G₀ Sz η ty hJ c s
  change Formalism.ExponentWindows.G.Jumps (kdOf ty (c - (s : ZMod n))) G₀ Sz η (bbOf ty (c - (s : ZMod n))) (FilD W T c s)
  cases h : ty (c - (s : ZMod n)) with
  | thin =>
    simp only [kdOf, h, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu
  | up b =>
    simp only [kdOf, bbOf, h, LT.size, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu
  | down b =>
    simp only [kdOf, bbOf, h, LT.size, Formalism.ExponentWindows.G.Jumps]
    intro u hu
    simpa [LT.win, h] using hw u hu

theorem jumps_holds_quot (hK : Function.Surjective (algebraMap K₀ K))
    (hQuot : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂)
    (hon : F.Onto) (c : ZMod n) (ell : ℕ) (G₀ Sz η : ℕ) (ty : ZMod n → LT)
    (hJ : KindJumps PD T₁ W.emb G₀ Sz η ty) :
    ∀ s < ell, Formalism.ExponentWindows.G.Jumps (E.kindAt (kdOf ty) c s) G₀ Sz η (E.sizeAt (bbOf ty) c s)
      (FilD W T₂ c s) :=
  jumps_holds hK c ell G₀ Sz η ty fun i τ hτ a ha => hJ i τ hτ a (hQuot T₁ T₂ F hc₁ hc₂ hon τ a ha)

end Jumps

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapLoc
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

theorem Pf_MapLoc_ιV_inj (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem Pf_MapLoc_ιV_map {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (y : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR) (ιV PD (LL := LL) (V := T₁.V) y) =
      ιV PD (LL := LL) (V := T₂.V) (AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [ιV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Pf_MapLoc_levB_map {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (crys₁ : IsCrys PD T₁.ρ) (crys₂ : IsCrys PD T₂.ρ)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (i : ZMod n) (ζ : LL) (x : ↥(W.N T₁)) (hx : W.map F (x : W.DD T₁) ∈ W.N T₂) (k : ℤ) :
    Lb.levB T₂ i ζ ⟨W.map F (x : W.DD T₁), hx⟩ k =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (Lb.levB T₁ i ζ x k) := by
  apply Pf_MapLoc_ιV_inj (PD := PD) T₂
  rw [← levN_eq, W.levN_map F crys₁ crys₂ i ζ x hx k, levN_eq, Pf_MapLoc_ιV_map]

theorem Pf_MapLoc_toKsD_map (s : ℕ) {D₁ D₂ : Type} [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] (g : D₁ →ₗ[LL] D₂) (f : Rs LL PD.p s → D₁) :
    g.baseChange (KsW W s) (toKsD W s D₁ f) = toKsD W s D₂ (fun ζ => g (f ζ)) := by
  classical
  obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s)).surjective f
  have h1 : (fun ζ => g (TensorProduct.piScalarRight LL LL D₁ (Rs LL PD.p s) y ζ)) =
      TensorProduct.piScalarRight LL LL D₂ (Rs LL PD.p s) (g.rTensor _ y) := by
    induction y using TensorProduct.induction_on with
    | zero => funext ζ; simp
    | tmul x a => funext ζ; simp
    | add y y' hy hy' =>
      funext ζ
      have e1 := congrFun hy ζ
      have e2 := congrFun hy' ζ
      simp only [map_add (f := _), Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  simp only [toKsD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply]
  rw [h1, LinearEquiv.symm_apply_apply]
  clear h1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x a => simp [LinearMap.baseChange_tmul]
  | add y y' hy hy' => simp only [map_add (f := _), hy, hy']

theorem Pf_MapLoc_ambF_expN (s : ℕ) {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}
    (h : MemD W F c) (x : ↥(W.N T₁)) (y : ↥(W.N T₂))
    (hxy : ∀ (ζ : LL) (k : ℤ), Lb.levB T₂ c ζ y k =
      AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (Lb.levB T₁ c ζ x k)) :
    ambF h s (expN Lb s T₁ c x) = expN Lb s T₂ c y := by
  have hc : ∀ k, (dmapOf h).baseChange (KsW W s) (coefN Lb s T₁ c x k) = coefN Lb s T₂ c y k := by
    intro k
    simp only [coefN]
    rw [Pf_MapLoc_toKsD_map]
    congr 1
    funext ζ
    apply Subtype.ext
    exact (hxy ζ.1 k).symm
  apply (HahnModule.of (KsW W s)).symm.injective
  ext k
  simp [ambF, ambMap, expN, HahnSeries.ofSuppBddBelow, hc]

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem locComm_holds (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (kap₁_unit : ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ₁)))
    (kap₂_unit : ∀ s < ell, IsUnit (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ₂))) :
    ∀ s < ell, ∀ (w : C₁.V)
    (hw : w ∈ (latOf C₁).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell))
    (hw' : (latHomOf hC).f w ∈ (latOf C₂).W c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell)),
    prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
        ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨w, hw⟩) =
      (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).loc s ⟨(latHomOf hC).f w, hw'⟩ := by
  intro s _ w hw hw'
  refine funext fun ⟨s', hs'⟩ => Subtype.ext ?_
  show ambF Mh.memD s' (locF Lb C₁ κ₁ s' (κ₁ • w) _) = locF Lb C₂ κ₂ s' (κ₂ • hC.f w) _
  have hm₁ : C₂.t c (κ₁ • hC.f w) ∈ W.N T₂ := by
    have h0 := (latHomOf hC).map_N c (κ₁ • w) (Hy₁.kap w hw)
    rw [show (latHomOf hC).f (κ₁ • w) = κ₁ • hC.f w from hC.f.map_smul κ₁ w] at h0
    exact (mem_N C₂ c _).1 h0
  have hm₂ : C₂.t c (κ₂ • hC.f w) ∈ W.N T₂ := (mem_N C₂ c _).1 (Hy₂.kap _ hw')
  have hA : ambF Mh.memD s' (expN Lb s' T₁ c ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩) =
      expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ := by
    apply Pf_MapLoc_ambF_expN
    intro ζ k
    have hx : W.map F (C₁.t c (κ₁ • w)) ∈ W.N T₂ := by
      rw [← hC.coord_hom_map_trace, map_smul]
      exact hm₁
    have he : (⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ : ↥(W.N T₂)) = ⟨W.map F (C₁.t c (κ₁ • w)), hx⟩ :=
      Subtype.ext (by
        show C₂.t c (κ₁ • hC.f w) = W.map F (C₁.t c (κ₁ • w))
        rw [← hC.coord_hom_map_trace, map_smul])
    rw [he]
    exact Pf_MapLoc_levB_map F hC.crys hC.crys' levN_eq c ζ ⟨C₁.t c (κ₁ • w), Hy₁.kap w hw⟩ hx k
  have hs₁ : (baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) ∈ W.N T₂ := (W.N T₂).smul_mem _ hm₁
  have hs₂ : (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w) ∈ W.N T₂ := (W.N T₂).smul_mem _ hm₂
  have hE : HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂) •
        expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩ =
      HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁) •
        expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩ := by
    rw [← Hy₂.expSemi s' κ₂ ⟨_, hm₁⟩ hs₁, ← Hy₂.expSemi s' κ₁ ⟨_, hm₂⟩ hs₂]
    congr 1
    apply Subtype.ext
    change (baseIdOf hR).d κ₂ • C₂.t c (κ₁ • hC.f w) = (baseIdOf hR).d κ₁ • C₂.t c (κ₂ • hC.f w)
    rw [← C₂.t_smul, ← C₂.t_smul, smul_smul, smul_smul, mul_comm]
  unfold locF
  rw [Mh.smul s', hA]
  set ρ₁ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₁)
  set ρ₂ := HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' κ₂)
  calc Ring.inverse ρ₁ • expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩
      = (Ring.inverse ρ₁ * Ring.inverse ρ₂) • (ρ₂ • expN Lb s' T₂ c ⟨C₂.t c (κ₁ • hC.f w), hm₁⟩) := by
        rw [smul_smul, mul_assoc, Ring.inverse_mul_cancel ρ₂ (kap₂_unit s' hs'), mul_one]
    _ = (Ring.inverse ρ₁ * Ring.inverse ρ₂) • (ρ₁ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩) := by
        rw [hE]
    _ = Ring.inverse ρ₂ • expN Lb s' T₂ c ⟨C₂.t c (κ₂ • hC.f w), hm₂⟩ := by
        rw [smul_smul, mul_comm (Ring.inverse ρ₁), mul_assoc, Ring.inverse_mul_cancel ρ₁ (kap₁_unit s' hs'),
          mul_one]

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfMapLocL
noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Cst

variable {LL Ks D D₂ : Type} [Field LL] [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
  [AddCommGroup D₂] [Module LL D₂]

theorem mapLocL_cstD_add (d d' : D) :
    cstD (LL := LL) Ks (d + d') = cstD Ks d + cstD Ks d' := by
  simp [cstD, TensorProduct.tmul_add]

theorem mapLocL_cstD_zero : cstD (LL := LL) (D := D) Ks 0 = 0 := by
  simp [cstD]

theorem mapLocL_cstD_sum {ι : Type} (s : Finset ι) (f : ι → D) :
    cstD (LL := LL) Ks (∑ i ∈ s, f i) = ∑ i ∈ s, cstD Ks (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mapLocL_cstD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mapLocL_cstD_add, ih]

theorem mapLocL_C_smul_cstD (x : LL) (d : D) :
    (HahnSeries.C (algebraMap LL Ks x) : HahnSeries ℤ Ks) • cstD (LL := LL) Ks d = cstD Ks (x • d) := by
  apply HahnModule.ext
  funext i
  rw [HahnSeries.C_apply, HahnModule.coeff_single_zero_smul]
  simp only [cstD, Equiv.symm_apply_apply, HahnSeries.coeff_single]
  split_ifs
  · rw [TensorProduct.tmul_smul, algebraMap_smul]
  · rw [smul_zero]

theorem mapLocL_ambMap_cstD (g : Ks ⊗[LL] D →ₗ[Ks] Ks ⊗[LL] D₂) (d : D) :
    ambMap g (cstD (LL := LL) Ks d) = HahnModule.of Ks (HahnSeries.single 0 (g ((1 : Ks) ⊗ₜ[LL] d))) := by
  apply HahnModule.ext
  funext i
  simp only [ambMap, cstD, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply]
  rw [HahnSeries.map_coeff]
  simp only [HahnSeries.coeff_single]
  split_ifs <;> simp

end Cst

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

section Helpers

theorem mapLocL_ambF_cstD {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}
    (h : MemD W F c) (s : ℕ) (d : Dc W T₁ c) :
    ambF h s (cstD (KsW W s) d) = cstD (KsW W s) (dmapOf h d) := by
  unfold ambF
  rw [mapLocL_ambMap_cstD, LinearMap.baseChange_tmul]
  rfl

theorem mapLocL_cmp_d (hR : Ring9 W) (T : LocLat G Qp LL O) (a : PowerSeries O) (x : ↥(W.N T)) :
    W.cmp T ((baseIdOf hR).d a • x) = algebraMap O LL (PowerSeries.constantCoeff a) • W.cmp T x := by
  set a' : PowerSeries O := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) a
  set π' : PowerSeries O := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) W.π₀₁
  have ha : a = PowerSeries.X * a' + PowerSeries.C (PowerSeries.constantCoeff a) :=
    PowerSeries.eq_X_mul_shift_add_const a
  have hπ : W.π₀₁ = PowerSeries.X * π' := by
    have := PowerSeries.eq_X_mul_shift_add_const W.π₀₁
    rwa [π₀₁_const hR, map_zero, add_zero] at this
  have hd : (baseIdOf hR).d a = (letπ : LetA O n) * ((fun _ => π') * (baseIdOf hR).d a') +
      algebraMap O (LetA O n) (PowerSeries.constantCoeff a) := by
    funext i
    have hC0 : (PowerSeries.C (PowerSeries.constantCoeff a) : PowerSeries O) =
        algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) := by
      rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [BaseId.d_apply]
    conv_lhs => rw [ha, hC0, map_add (f := _), map_mul, AlgHom.commutes, (baseIdOf hR).ι_X, hπ]
    simp only [Pi.add_apply, Pi.mul_apply, BaseId.d_apply, letπ, Pi.algebraMap_apply]
    ring
  rw [hd, add_smul, map_add (f := _), mul_smul, W.cmp_π, zero_add, algebraMap_smul, W.cmp_smul]

theorem mapLocL_t_sum {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n) {ι : Type}
    (s : Finset ι) (f : ι → C.V) : C.t i (∑ l ∈ s, f l) = ∑ l ∈ s, C.t i (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [C.t_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, C.t_add, ih]

theorem mapLocL_map_φVB {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (z : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (φVB PD (LL := LL) (V := T₁.V) z) =
      φVB PD (LL := LL) (V := T₂.V) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [φVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mapLocL_map_φVB_pow {T₁ T₂ : LocLat G Qp LL O} (f : T₁.V →ₗ[LL] T₂.V) (e : ℕ)
    (z : T₁.V ⊗[Qp] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) (((φVB PD (LL := LL) (V := T₁.V)) ^ e) z) =
      ((φVB PD (LL := LL) (V := T₂.V)) ^ e) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) z) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, mapLocL_map_φVB, ih, pow_succ', Module.End.mul_apply]

theorem mapLocL_cmp_map {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁}
    {C₂ : Coord W (baseIdOf hR) T₂} {F : LatHom T₁.L T₂.L} (hC : CoordHom C₁ C₂ F) (i : ZMod n)
    {r : ℕ} (x : C₁.V) (hx : C₁.t i x ∈ W.N T₁) (e₂ : Fin r → C₂.V) (he₂ : ∀ l, C₂.t i (e₂ l) ∈ W.N T₂)
    (a : Fin r → PowerSeries O) (ha : hC.f x = ∑ l, a l • e₂ l) :
    AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) (W.cmp T₁ ⟨C₁.t i x, hx⟩) =
      ∑ l, algebraMap O LL (PowerSeries.constantCoeff (a l)) • W.cmp T₂ ⟨C₂.t i (e₂ l), he₂ l⟩ := by
  have hy : W.map F ((⟨C₁.t i x, hx⟩ : ↥(W.N T₁)) : W.DD T₁) ∈ W.N T₂ := by
    show W.map F (C₁.t i x) ∈ W.N T₂
    rw [← hC.coord_hom_map_trace]
    exact (latHomOf hC).map_N i x hx
  rw [← W.cmp_map F hC.crys hC.crys' ⟨C₁.t i x, hx⟩ hy]
  have heq : (⟨W.map F ((⟨C₁.t i x, hx⟩ : ↥(W.N T₁)) : W.DD T₁), hy⟩ : ↥(W.N T₂)) =
      ∑ l, (baseIdOf hR).d (a l) • (⟨C₂.t i (e₂ l), he₂ l⟩ : ↥(W.N T₂)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show W.map F (C₁.t i x) = ∑ l, (baseIdOf hR).d (a l) • C₂.t i (e₂ l)
    rw [← hC.coord_hom_map_trace, ha, mapLocL_t_sum]
    simp only [Coord.t_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [heq, map_sum]
  simp only [mapLocL_cmp_d]

theorem mapLocL_lamOf_coe {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ)
    {r : ℕ} (e : Fin r → C.V) (k : Fin r) (hk : C.t (c - (ell : ZMod n)) (e k) ∈ W.N T) :
    ((lamOf C c ell e k : Dc W T c) : T.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩) := by
  have h1 : W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ ∈ DcrisL PD T.ρ (W.emb (c - (ell : ZMod n))) := by
    have h0 := W.cmp_letter T (c - (ell : ZMod n)) ⟨_, hk⟩
    have hx : ((letE (c - (ell : ZMod n)) : LetA O n) • (⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ : ↥(W.N T))) =
        ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩ := Subtype.ext (C.t_letter _ _)
    rwa [hx] at h0
  have h' : ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨C.t (c - (ell : ZMod n)) (e k), hk⟩) ∈
      DcrisL PD T.ρ (W.emb c) := by
    have h2 := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T (c - (ell : ZMod n)) h1 ell
    rwa [sub_add_cancel] at h2
  unfold lamOf
  rw [dite_eq_left hk, dite_eq_left h']

end Helpers

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem mapLocL_dmap_lam (hC : CoordHom C₁ C₂ F) (Mh : MapHyp hR uZ ιZ F c)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) (k : Fin r₁) :
    dmapOf Mh.memD (lamOf C₁ c ell e₁ k) =
      ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lamOf C₂ c ell e₂ l := by
  obtain ⟨a, ha, hPa⟩ := hP k
  apply Subtype.ext
  rw [Submodule.coe_sum]
  show AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) ((lamOf C₁ c ell e₁ k : Dc W T₁ c) : T₁.V ⊗[Qp] B) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mapLocL_lamOf_coe C₁ c ell e₁ k (he₁ k), mapLocL_map_φVB_pow,
    mapLocL_cmp_map hC _ (e₁ k) (he₁ k) e₂ he₂ a ha, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, Submodule.coe_smul, mapLocL_lamOf_coe C₂ c ell e₂ l (he₂ l), hPa l]

theorem loclComm_holds (hC : CoordHom C₁ C₂ F)
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ)
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (hlam₁ : lam₁ = lamOf C₁ c ell e₁) (hlam₂ : lam₂ = lamOf C₂ c ell e₂)
    (he₁ : ∀ k, e₁ k ∈ (latOf C₁).N (c - (ell : ZMod n)))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    ∀ s < ell, ∀ y : Fin r₁ → PowerSeries O,
      prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell
          ((lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s y) =
        (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).locL s (E.extL P y) := by
  subst hlam₁ hlam₂
  intro s _ y
  apply prL_inj
  intro s' hs'
  erw [prL_of_lt s' hs', prL_of_lt s' hs']
  change ambF Mh.memD s' (locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (lamOf C₁ c ell e₁) s' y) =
    locLF (hR := hR) (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) (lamOf C₂ c ell e₂) s' (E.extL P y)
  have hk : ∀ k, ambF Mh.memD s' (cstD (KsW W s') (lamOf C₁ c ell e₁ k)) =
      ∑ l, HahnSeries.ofPowerSeries ℤ (KsW W s') (rhoL hR c s' (PowerSeries.C (LinearMap.toMatrix' P l k))) •
        cstD (KsW W s') (lamOf C₂ c ell e₂ l) := by
    intro k
    rw [mapLocL_ambF_cstD, mapLocL_dmap_lam hC Mh e₁ e₂ P he₁ he₂ hP k, mapLocL_cstD_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Hy₂.rhoC, HahnSeries.ofPowerSeries_C, mapLocL_C_smul_cstD]
  have hext : ∀ l, E.extL P y l = ∑ k, PowerSeries.C (LinearMap.toMatrix' P l k) * y k := by
    intro l
    simp [E.extL, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  simp only [locLF]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Mh.smul, map_sum]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Mh.smul, hk, hext, map_sum, map_mul, Finset.sum_smul, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

theorem prLIs_holds (hC : CoordHom C₁ C₂ F) {r₁ r₂ : ℕ}
    (e₁ : Fin r₁ → C₁.V) (e₂ : Fin r₂ → C₂.V) (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (he₂ : ∀ l, e₂ l ∈ (latOf C₂).N (c - (ell : ZMod n)))
    (hP : ∀ k, ∃ a : Fin r₂ → PowerSeries O, (latHomOf hC).f (e₁ k) = ∑ l, a l • e₂ l ∧
      ∀ l, LinearMap.toMatrix' P l k = PowerSeries.constantCoeff (a l)) :
    ∀ k, (latHomOf hC).f (e₁ k) -
      ∑ l, PowerSeries.C (LinearMap.toMatrix' P l k) • e₂ l ∈
    E.sm (PowerSeries.X : PowerSeries O) ((latOf C₂).N (c - (ell : ZMod n))) := by
  intro k
  obtain ⟨a, ha, hPa⟩ := hP k
  refine Submodule.mem_map.2 ⟨∑ l, (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a l)) • e₂ l,
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (he₂ l), ?_⟩
  rw [LinearMap.lsmul_apply, Finset.smul_sum, ha, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul, hPa l, ← sub_smul]
  congr 1
  rw [eq_sub_iff_add_eq]
  exact (PowerSeries.eq_X_mul_shift_add_const (a l)).symm

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
end
end
