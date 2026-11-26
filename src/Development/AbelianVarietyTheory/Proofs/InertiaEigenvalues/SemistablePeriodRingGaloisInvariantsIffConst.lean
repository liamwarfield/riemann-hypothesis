module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecomp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem stInv_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l)
    (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔
      ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  intro l _ P AI T K x
  constructor
  · intro h
    obtain ⟨hdom, h2, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
    haveI := hdom
    obtain ⟨c, hcK, hc⟩ := h2 K 1 x one_ne_zero fun g => by rw [map_one, h g, one_mul]
    have hmem : (c : Om l) ∈ K0 K := IntermediateField.mem_inf.2 ⟨hcK, c.2⟩
    refine ⟨⟨c, hmem⟩, ?_⟩
    rw [hc, mul_one, Polynomial.algebraMap_apply]
    rfl
  · rintro ⟨c, rfl⟩ g
    have hc : (c : Om l) ∈ (K.1 : IntermediateField ℚ_[l] (Om l)) := (IntermediateField.mem_inf.1 c.2).1
    have hg : (g : GQ l) (c : Om l) = (c : Om l) := (mem_fixingSubgroup_iff _).1 g.2 _ hc
    have hK0 : algebraMap ↥(K0 K) P.R.B c =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, (IntermediateField.mem_inf.1 c.2).2⟩ := rfl
    rw [actSt]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, stHom_apply, Polynomial.map_C, Polynomial.C_comp]
    congr 1
    rw [hK0]
    exact P.actQ_Kur _ _ _ hg

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConstStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔ ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  first | exact @GlobalTheory.PMon.stInv_iff | exact GlobalTheory.PMon.stInv_iff | (intros; apply GlobalTheory.PMon.stInv_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionClassEqLPowSmulGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionClassEqLPowSmulGalois
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtClass

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {T Tp U : LocLat (Gl l) ℚ_[l] K O} {f : LatHom T.L Tp.L} {g : LatHom Tp.L U.L}


omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem map_injective (hfg : IsSESLat (Qp := ℚ_[l]) f g) (B : Type) [AddCommGroup B] [Module O B] :
    Function.Injective (TensorProduct.map (LinearMap.id : B →ₗ[O] B) ((f.f.restrictScalars O).restrict f.T_le)) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := hfg
  have := U.L.free
  refine LinearMap.lTensor_injective_of_exact_of_flat ((g.f.restrictScalars O).restrict g.T_le) (fun z => ?_)
    ((f.f.restrictScalars O).restrict f.T_le) (fun x y h => Subtype.ext (h1 (congrArg Subtype.val h)))
    (fun z => ⟨fun h => ?_, ?_⟩) B
  · obtain ⟨x, hx, h⟩ := h3 z.1 z.2
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩
  · obtain ⟨y, hy⟩ := (h4 z.1).1 (congrArg Subtype.val h)
    exact ⟨⟨y, h5 y (hy ▸ z.2)⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((h4 _).2 ⟨y.1, rfl⟩)

theorem exists_solution {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {R : PhiMod O K l e a μ}
    {I : Ident t ϖ P T} {Ip : Ident t ϖ Q Tp} {Iu : Ident t ϖ R U} {F : GlobalTheory.BK.Hom P Q} {G : GlobalTheory.BK.Hom Q R}
    (hfg : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I Ip f F) (hG : IsMapOf Ip Iu g G) (u : ME R) (x : ↥U.L.T)
    (hux : toW t ϖ R u = Iu.ofT x) (k : ℕ) {x₂ : Vec K a κ} (hx₂ : x₂ ∈ Q.M) (hGx : G.app x₂ = k • u.1)
    (v : ↥Tp.L.T) (hv : g.f v = x.1) {y : Vec K a ι} (hy : y ∈ ME P) (hFy : F.app y = Q.phi x₂ - x₂) :
    ∃ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P ⟨y, hy⟩ ∧
      homW t ϖ F m₀ = toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v := by
  obtain ⟨m₁, hm₁⟩ := I.exists_phiW_sub (toW t ϖ P ⟨y, hy⟩)
  have hfixp : ∀ z, phiW t ϖ Q (Ip.ofT z) = Ip.ofT z := fun z =>
    mem_Treal.1 (by rw [← Ip.range_ofT]; exact ⟨z, rfl⟩)
  have hfix : ∀ z, phiW t ϖ P (I.ofT z) = I.ofT z := fun z =>
    mem_Treal.1 (by rw [← I.range_ofT]; exact ⟨z, rfl⟩)
  have h1 : phiW t ϖ Q (homW t ϖ F m₁) - homW t ϖ F m₁ =
      phiW t ϖ Q (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) - toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ := by
    rw [← homW_phiW, ← map_sub, hm₁, homW_toW, ← toW_phi t ϖ Q hx₂, ← map_sub]
    exact congrArg _ (Subtype.ext hFy)
  have h2 : homW t ϖ F m₁ - (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v) ∈ LinearMap.range Ip.ofT := by
    rw [Ip.range_ofT, mem_Treal, map_sub, map_sub, map_nsmul, hfixp, sub_eq_iff_eq_add.1 h1]
    abel
  obtain ⟨z, hz⟩ := h2
  have h3 : homW t ϖ G (homW t ϖ F m₁) = 0 := by
    apply Iu.j.injective
    rw [hG, hF, map_zero]
    induction I.j m₁ using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul w s =>
      have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) s) = 0 :=
        Subtype.ext ((hfg.2.2.2.1 _).2 ⟨s.1, rfl⟩)
      simp only [latW, TensorProduct.map_tmul, h0, TensorProduct.tmul_zero]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, add_zero]
  have h4 : homW t ϖ G (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) = k • Iu.ofT x := by
    rw [homW_toW, ← hux, ← map_nsmul]
    exact congrArg _ (Subtype.ext hGx)
  have h5 : homW t ϖ G (Ip.ofT v) = Iu.ofT x := by
    rw [hG.homW_ofT]
    exact congrArg _ (Subtype.ext hv)
  have h6 := congrArg (homW t ϖ G) hz
  rw [map_sub, map_sub, map_nsmul, h3, h4, h5, sub_self, sub_self, hG.homW_ofT, ← map_zero Iu.ofT] at h6
  obtain ⟨s, hs⟩ := (hfg.2.2.2.1 z.1).1 (congrArg Subtype.val (Iu.ofT_injective h6))
  have hsT : s ∈ T.L.T := hfg.2.2.2.2 s (hs ▸ z.2)
  refine ⟨m₁ - I.ofT ⟨s, hsT⟩, ?_, ?_⟩
  · rw [map_sub, hfix, ← hm₁]
    abel
  · rw [map_sub, hF.homW_ofT, show (⟨f.f (⟨s, hsT⟩ : ↥T.L.T), f.T_le _ hsT⟩ : ↥Tp.L.T) = z from Subtype.ext hs, hz]
    abel

theorem isCrisVal_toW {P : PhiMod O K l e a ι} (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {w : Vec K a ι}
    (hL : w ∈ P.L) (hS : w ∈ P.MMl) :
    IsCrisVal t ϖ P jB (toW t ϖ P ⟨w, mem_ME_of_mem_L hL⟩) (jB (toBcris t ϖ P ⟨w, hS⟩)) := by
  refine ⟨1, fun i => ϖ.iTot t K (coordL P (A O K) ⟨_, hL⟩ i), by rw [map_one]; exact isUnit_one, ?_, ?_⟩
  · rw [map_one, one_smul]
    exact (toW_toCris_of_mem_L t ϖ P hL (P.ext_mono (A_le_S l e) hL)).1
  · rw [map_one, one_smul]
    refine congrArg _ (funext fun i => ?_)
    rw [toBcris_apply, toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
    rfl

variable [TameDescentExponentData K l e a] {η H : ℕ}


set_option maxHeartbeats 1600000 in
theorem classOf {D : BKDat O K l e a ι η H} {Dp : BKDat O K l e a κ η H} {Du : BKDat O K l e a μ η H}
    (R : GalDat t ϖ (sQ l) D T) (Rp : GalDat t ϖ (sQ l) Dp Tp) (Ru : GalDat t ϖ (sQ l) Du U)
    (F : BKHom D Dp) (G : BKHom Dp Du) (hfg : IsSESLat (Qp := ℚ_[l]) f g)
    (hF : IsMapOf R.I Rp.I f F.toHom) (hG : IsMapOf Rp.I Ru.I g G.toHom) (hinj : Function.Injective F.app)
    (u : ME Du.toPhiMod) (x : ↥U.L.T) (hux : toW t ϖ Du.toPhiMod u = Ru.I.ofT x) (n : ℕ) {x₂ : Vec K a κ}
    (hx₂ : x₂ ∈ Dp.Minv) (hGx : G.app x₂ = (l ^ n) • u.1) {v : Tp.V} {c : Gl l → T.V} (hv : v ∈ Tp.L.T)
    (hgv : g.f v = x.1) (hc : ∀ h, Tp.ρ h v - v = f.f (c h)) {σ : Vec K a ι} (hσ : σ ∈ D.MMl)
    (hσi : σ ∈ D.desc.inv) (hFσ : F.app σ = Dp.phi x₂ - Dp.xi (red (Dp.phi x₂))) {y : Vec K a ι} (hy : y ∈ D.Y)
    (hFy : F.app y = Dp.phi x₂ - x₂) : R.ClassOf y ((l : K) ^ n • c) := by
  have hyE : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hy
  obtain ⟨m₀, hm₀, hFm₀⟩ := exists_solution hfg hF hG u x hux (l ^ n) hx₂.1 hGx ⟨v, hv⟩ hgv hyE hFy
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.GalPot.exists_isCrisVal R hy hyE m₀ hm₀
  have hz : D.conn σ = D.zeta y := by
    apply hinj
    rw [F.toHom.app_conn, F.toHom.app_zeta, hFσ, hFy, PhiMod.zeta_phi_sub, map_sub, PhiMod.conn_xi, sub_zero]
  refine ⟨_, ⟨hyE, m₀, ⟨σ, hσ⟩, b₀, hm₀, hσi, hz, hb₀, rfl⟩, ?_⟩
  have hAS : A O K ≤ invL l (S O K e) := (A_le_S l e).trans (le_away _ _)
  have hL := Dp.phi_mem_L hx₂.1
  have hS : Dp.phi x₂ ∈ Dp.MMl := Dp.ext_mono hAS hL
  have hFS : F.app σ ∈ Dp.MMl := F.toHom.app_mem_ext hAS hσ
  have hξ : Dp.xi (red (Dp.phi x₂)) ∈ Dp.MMl := by
    have := sub_mem hS hFS
    rwa [hFσ, sub_sub_cancel] at this
  have hfixξ := GlobalTheory.GalPot.fix_of_horiz Rp ⟨_, hξ⟩ (fun γ => by
    change Dp.desc.act γ (Dp.xi _) = Dp.xi _
    rw [Descent.act_xi, ← Descent.red_act, Dp.desc.act_phi, hx₂.2 γ]) (Dp.conn_xi _)
  have N := GlobalTheory.T.bcrisTensorIdentification_natural l a e O K t ϖ ι D.toPhiMod T R.I R.jB R.cmp κ Dp.toPhiMod Tp Rp.I Rp.jB f
    F.toHom Rp.cmp hF
  have C := (GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Dp.toPhiMod Tp Rp.I).2 Rp.jB Rp.cmp
  set Φ := TensorProduct.map (R := O) (LinearMap.id (R := O) (M := OB l O))
    ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  have hfix : phiW t ϖ Dp.toPhiMod (Rp.I.ofT ⟨v, hv⟩) = Rp.I.ofT ⟨v, hv⟩ :=
    mem_Treal.1 (by rw [← Rp.I.range_ofT]; exact ⟨_, rfl⟩)
  have h1 := N.2 _ _ hb₀
  rw [homW_phiW, hFm₀, map_sub, map_nsmul, hfix, ← toW_phi t ϖ Dp.toPhiMod hx₂.1] at h1
  have h2 := C.2.1 _ _ _ h1 (IsCrisVal.sub t ϖ (isCrisVal_toW Rp.jB hL hS)
    (GlobalTheory.GalPot.isCrisVal_nsmul (C.2.2.2.1 ⟨v, hv⟩) (l ^ n)))
  have h3 : Φ (R.jB (toBcris t ϖ D.toPhiMod ⟨σ, hσ⟩) - b₀) =
      (l ^ n) • ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) - Rp.jB (toBcris t ϖ Dp.toPhiMod ⟨_, hξ⟩) := by
    rw [map_sub, h2, ← N.1 ⟨σ, hσ⟩ ⟨_, hFS⟩ rfl,
      show (⟨F.app σ, hFS⟩ : Dp.MMl) = ⟨_, hS⟩ - ⟨_, hξ⟩ from Subtype.ext hFσ, map_sub, map_sub]
    abel
  intro γ k s hs
  apply map_injective hfg (OB l O)
  have hact : actB (sQ l) Tp γ ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) =
      (1 : OB l O) ⊗ₜ[O] (Tp.actT γ ⟨v, hv⟩) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hs' : (f.f.restrictScalars O).restrict f.T_le s = (l : O) ^ k • (l : O) ^ n • (Tp.actT γ ⟨v, hv⟩ - ⟨v, hv⟩) := by
    have hsm : ∀ (j : ℕ) (w : Tp.V), ((l : O) ^ j) • w = (l : K) ^ j • w := fun j w => by
      rw [← algebraMap_smul K ((l : O) ^ j) w, map_pow, map_natCast]
    apply Subtype.ext
    change f.f (s : T.V) = (l : O) ^ k • (l : O) ^ n • (Tp.ρ γ v - v)
    rw [hs, hsm, hsm, hc, Pi.smul_apply, map_smul, map_smul]
  rw [map_smul, map_sub, GlobalTheory.CocycleNat.actB_map, ← hΦ, h3, map_sub, map_nsmul, hfixξ, hact, hΦ,
    TensorProduct.map_tmul, LinearMap.id_apply, hs', TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    TensorProduct.tmul_sub, smul_sub, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  congr 1
  abel


set_option maxHeartbeats 1000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L), IsSESLat (Qp := ℚ_[l]) f g → ∀ (Pk : Pack a ϖ η H T) (Pp : Pack a ϖ η H Tp) (Pu : Pack a ϖ η H (unitLat (Gl l) : QLat LL)) (F : BKHom Pk.D Pp.D) (G : BKHom Pp.D Pu.D), IsMapOf Pk.R.I Pp.R.I f F.toHom → IsMapOf Pp.R.I Pu.R.I g G.toHom → IsExactTriple F.toHom G.toHom → Function.Injective F.app → ∀ (u : ME Pu.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) → u.1 ∈ Pu.D.Minv → Pu.D.phi u.1 = u.1 → toW (thetaW a LL) ϖ Pu.D.toPhiMod u = Pu.R.I.ofT x → ∀ (n : ℕ) (x₂ : Vec ↥LL.1 a (Fin Pp.n)), x₂ ∈ Pp.D.Minv → G.app x₂ = (l ^ n) • u.1 → ∀ (v : Tp.V) (c : Gl l → T.V), v ∈ Tp.L.T → g.f v = (1 : ↥LL.1) → (∀ h, Tp.ρ h v - v = f.f (c h)) → ∀ σ ∈ Pk.D.MMl, σ ∈ Pk.D.desc.inv → F.app σ = Pp.D.phi x₂ - Pp.D.xi (red (Pp.D.phi x₂)) → ∀ y ∈ Pk.D.Y, F.app y = Pp.D.phi x₂ - x₂ → Pk.R.ClassOf y ((l : ↥LL.1) ^ n • c) := by
  intro l _ a e _ _ ϖ LL _ _ η H T Tp f g hfg Pk Pp Pu F G hF hG _ hinj u x hx1 _ _ hux n x₂ hx₂ hGx₂ v c hv hgv hc σ hσ hσi hFσ y hy hFy
  exact classOf Pk.R Pp.R Pu.R F G hfg hF hG hinj u x hux n hx₂ hGx₂ hv (hgv.trans hx1.symm) hc hσ hσi hFσ hy hFy

end GlobalTheory.ExtClass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionClassEqLPowSmulGaloisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionClass_eq_lPow_smul_galois : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L), IsSESLat (Qp := ℚ_[l]) f g → ∀ (Pk : Pack a ϖ η H T) (Pp : Pack a ϖ η H Tp) (Pu : Pack a ϖ η H (unitLat (Gl l) : QLat LL)) (F : BKHom Pk.D Pp.D) (G : BKHom Pp.D Pu.D), IsMapOf Pk.R.I Pp.R.I f F.toHom → IsMapOf Pp.R.I Pu.R.I g G.toHom → IsExactTriple F.toHom G.toHom → Function.Injective F.app → ∀ (u : ME Pu.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) → u.1 ∈ Pu.D.Minv → Pu.D.phi u.1 = u.1 → toW (thetaW a LL) ϖ Pu.D.toPhiMod u = Pu.R.I.ofT x → ∀ (n : ℕ) (x₂ : Vec ↥LL.1 a (Fin Pp.n)), x₂ ∈ Pp.D.Minv → G.app x₂ = (l ^ n) • u.1 → ∀ (v : Tp.V) (c : Gl l → T.V), v ∈ Tp.L.T → g.f v = (1 : ↥LL.1) → (∀ h, Tp.ρ h v - v = f.f (c h)) → ∀ σ ∈ Pk.D.MMl, σ ∈ Pk.D.desc.inv → F.app σ = Pp.D.phi x₂ - Pp.D.xi (red (Pp.D.phi x₂)) → ∀ y ∈ Pk.D.Y, F.app y = Pp.D.phi x₂ - x₂ → Pk.R.ClassOf y ((l : ↥LL.1) ^ n • c) := by
  first | exact @GlobalTheory.ExtClass.main | exact GlobalTheory.ExtClass.main | (intros; apply GlobalTheory.ExtClass.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCrystallineOfLatticeReads
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCrystallineOfLatticeReads
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime]

theorem exists_read_map {Γ : Type} [Group Γ] {a d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l])
    (r : Γ →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l])
    (hR : Reads ρ r b e) (L : FinExt l) (r' : Γ →* GL (Fin a) ↥L.1)
    (R : Representation ↥L.1 Γ (Fin a → ↥L.1)) (hRr : ∀ g v, R g v = (r' g).val *ᵥ v)
    (hr : ∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) (v : Fin a → ↥L.1) :
    ∃ (F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : Fin d → ℚ_[l]),
      (∀ g y, F (qRep ρ g y) = R g (F y)) ∧ F x = v := by
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ↥L.1 (Om l))
    (LinearMap.ker_eq_bot.2 (algebraMap ↥L.1 (Om l)).injective)
  have hp' : ∀ c : ↥L.1, p (c : Om l) = c := fun c => LinearMap.congr_fun hp c
  let Φ : (Fin d → ℚ_[l]) → Matrix (Fin a) (Fin a) (Om l) := fun x => ∑ j, algebraMap ℚ_[l] (Om l) (x j) • b j
  let w : Fin a → Om l := fun k => (v k : Om l)
  have hΦs : ∀ (c : ℚ_[l]) x, Φ (c • x) = c • Φ x := by
    intro c x
    simp only [Φ, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, algebraMap_smul]
  have hΦa : ∀ x y, Φ (x + y) = Φ x + Φ y := by
    intro x y
    simp only [Φ, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  let F : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] (Fin a → ↥L.1) :=
    { toFun := fun x i => p ((Φ x *ᵥ w) i)
      map_add' := by
        intro x y; funext i
        simp only [hΦa, Matrix.add_mulVec, Pi.add_apply, map_add (f := _)]
      map_smul' := by
        intro c x; funext i
        have h1 : ((Φ (c • x)) *ᵥ w) i = c • ((Φ x *ᵥ w) i) := by
          rw [hΦs]
          simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Matrix.smul_apply, smul_mul_assoc]
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [h1]
        exact LinearMap.map_smul_of_tower p c _ }
  have hq : ∀ g y, qRep ρ g y = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ y := fun g y => rfl
  have hΦg : ∀ g y, Φ (qRep ρ g y) = (r g).val * Φ y := by
    intro g y
    rw [hq]
    simp only [Φ, Matrix.mul_sum, Matrix.mul_smul, hR.equi, Finset.smul_sum, smul_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨F, fun j => algebraMap ℤ_[l] ℚ_[l] (e j), fun g y => ?_, ?_⟩
  · funext i
    rw [hRr]
    change p ((Φ (qRep ρ g y) *ᵥ w) i) = ∑ k, (r' g).val i k * p ((Φ y *ᵥ w) k)
    rw [hΦg, ← Matrix.mulVec_mulVec]
    generalize Φ y *ᵥ w = z
    change p (∑ k, (r g).val i k * z k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hr]
    exact LinearMap.map_smul p ((r' g).val i k) (z k)
  · funext i
    change p ((Φ _ *ᵥ w) i) = v i
    have h1 : Φ (fun j => algebraMap ℤ_[l] ℚ_[l] (e j)) = 1 := hR.one
    rw [h1, Matrix.one_mulVec]
    exact hp' (v i)

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem crys_pass (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsCrys (P.PD K) ρq) : IsCrys (P.PD K) R := by
  haveI := L.2
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have hf := GlobalTheory.TateDualCrys.fracInv_of_tied T K
  have hu := GlobalTheory.TateDualCrys.lineUnit_of_tied T K
  rw [GlobalTheory.RegularRing.isCrys_iff_span (P.PD K) hf hu] at h ⊢
  refine GlobalTheory.RegularRing.eq_top_of_tmul _ fun c v => ?_
  obtain ⟨F, x, hFe, rfl⟩ := hF v
  have hm : ∀ y ∈ DcrisK₀ (P.PD K) ρq, F.baseChange P.R.B y ∈ DcrisK₀ (P.PD K) R := by
    intro y hy
    rw [GlobalTheory.RegularRing.mem_DcrisK₀] at hy ⊢
    intro g
    have hc : ∀ z, F.baseChange P.R.B (GlobalTheory.RegularRing.sig (P.PD K) ρq g z) =
        GlobalTheory.RegularRing.sig (P.PD K) R g (F.baseChange P.R.B z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul b w => simp [GlobalTheory.RegularRing.sig_tmul, hFe]
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    rw [← hc, hy g]
  have h1 : Submodule.span P.R.B (DcrisK₀ (P.PD K) ρq : Set (P.R.B ⊗[ℚ_[l]] V)) ≤
      (Submodule.span P.R.B (DcrisK₀ (P.PD K) R : Set (P.R.B ⊗[ℚ_[l]] (Fin a → ↥L.1)))).comap
        (F.baseChange P.R.B) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (hm y hy)
  have h2 := h1 (h ▸ Submodule.mem_top : c ⊗ₜ[ℚ_[l]] x ∈ _)
  simpa using h2

theorem dr_pass (T : LocTied l P AI) (K L : FinExt l) {LL0 : Type} [Field LL0] [Algebra ℚ_[l] LL0]
    {V : Type} [AddCommGroup V] [Module LL0 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL0 V] {a : ℕ}
    (ρ0 : Representation LL0 ↥(GK K) V) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρ0 g y) = R g (F y)) ∧ F x = v)
    (h : GlobalTheory.DRFil.Spans (P.PD K) ρ0) : IsDR (P.PD K) R := by
  haveI := L.2
  apply GlobalTheory.DRFil.isDR_of_spans T K L R
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add y z hy hz =>
    obtain ⟨m, b, dd, hd, rfl⟩ := hy
    obtain ⟨m', b', dd', hd', rfl⟩ := hz
    refine ⟨m + m', Fin.append b b', Fin.append dd dd', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hd i
      · simpa using hd' i
    · rw [Fin.sum_univ_add]
      simp
  | tmul v c =>
    obtain ⟨F, x, hFe, rfl⟩ := hF v
    obtain ⟨m, b, dd, hd, hx⟩ := h (x ⊗ₜ[ℚ_[l]] c)
    let E : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR :=
      TensorProduct.map F (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)
    have hE : ∀ (β : P.R.BdR) z, E (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR LL0 V β z) =
        GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) β (E z) := by
      intro β z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E]
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    have hg : ∀ g z, E (actVdR (P.PD K) ρ0 g z) = actVdR (P.PD K) R g (E z) := by
      intro g z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul u c' => simp [E, actVdR, hFe]
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    refine ⟨m, b, fun i => E (dd i), fun i => ?_, ?_⟩
    · have h1 := hd i
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at h1 ⊢
      intro g
      rw [← hg, h1 g]
    · have h2 := congrArg E hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simp only [hE] at h2
      simpa [E] using h2

end GlobalTheory.ReadPass

namespace GlobalTheory.ReadPass

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem dr_pass_rat (T : LocTied l P AI) (K L : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] {a : ℕ} (ρq : Representation ℚ_[l] ↥(GK K) V)
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1))
    (hF : ∀ v : Fin a → ↥L.1, ∃ (F : V →ₗ[ℚ_[l]] (Fin a → ↥L.1)) (x : V),
      (∀ g y, F (ρq g y) = R g (F y)) ∧ F x = v)
    (h : IsDR (P.PD K) ρq) : IsDR (P.PD K) R := by
  let LL : FinExt l := ⟨⊥, inferInstance⟩
  let e : (↥(LL.1)) ≃ₐ[ℚ_[l]] ℚ_[l] := IntermediateField.botEquiv ℚ_[l] (Om l)
  letI iM : Module (↥(LL.1)) V := Module.compHom V e.toRingEquiv.toRingHom
  haveI iT : IsScalarTower ℚ_[l] (↥(LL.1)) V :=
    ⟨fun q x v => by
      show e (q • x) • v = q • (e x • v)
      rw [show e (q • x) = q • e x from e.toLinearEquiv.map_smul q x, smul_eq_mul, mul_smul]⟩
  haveI iF : FiniteDimensional (↥(LL.1)) V := Module.Finite.of_restrictScalars_finite ℚ_[l] (↥(LL.1)) V
  let ρ' : Representation (↥(LL.1)) (↥(GK K)) V :=
    { toFun := fun g =>
        { toFun := ρq g, map_add' := (ρq g).map_add, map_smul' := fun x v => (ρq g).map_smul (e x) v }
      map_one' := by ext v; simp
      map_mul' := by intro g h; ext v; simp; rfl }
  have hact : ∀ g (x : V ⊗[ℚ_[l]] P.R.BdR), actVdR (P.PD K) ρ' g x = actVdR (P.PD K) ρq g x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rfl
    | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]
  have hmem : ∀ x : V ⊗[ℚ_[l]] P.R.BdR, x ∈ DdR (P.PD K) ρ' ↔ x ∈ DdR (P.PD K) ρq := by
    intro x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, hact]
  have hfr : ∀ (W : Type) [AddCommGroup W] [Module (↥(LL.1)) W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] (↥(LL.1)) W], Module.finrank (↥(LL.1)) W = Module.finrank ℚ_[l] W := by
    intro W _ _ _ _
    rw [← Module.finrank_mul_finrank ℚ_[l] (↥(LL.1)) W]
    have : Module.finrank ℚ_[l] (↥(LL.1)) = 1 := IntermediateField.finrank_bot
    rw [this, one_mul]
  let eq : ↥(DdR (P.PD K) ρ') ≃ₗ[ℚ_[l]] ↥(DdR (P.PD K) ρq) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h' : IsDR (P.PD K) ρ' := by
    unfold IsDR at h ⊢
    rw [hfr, hfr, eq.finrank_eq, h]
  exact dr_pass T K L ρ' R hF ((GlobalTheory.DRFil.filSpans T K LL ρ' h').spans)

theorem isDR_isCrys_of_reads : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → (Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → Formalism.MainNotions.N.IsDR (P.PD K) R) ∧ (IsCrys (P.PD K) (qRep ρ) → IsCrys (P.PD K) R) := by
  intro l _ K L₀ P AI T a d ρ r b e hR L r' R _ hRr hr
  have hF := exists_read_map ρ r b e hR L r' R hRr hr
  exact ⟨dr_pass_rat T K L (qRep ρ) R hF, crys_pass T K L (qRep ρ) R hF⟩

end GlobalTheory.ReadPass

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamCrystallineOfLatticeReadsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_crystalline_of_lattice_reads : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → (Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → Formalism.MainNotions.N.IsDR (P.PD K) R) ∧ (IsCrys (P.PD K) (qRep ρ) → IsCrys (P.PD K) R) := by
  first | exact @GlobalTheory.ReadPass.isDR_isCrys_of_reads | exact GlobalTheory.ReadPass.isDR_isCrys_of_reads | (intros; apply GlobalTheory.ReadPass.isDR_isCrys_of_reads; all_goals assumption)
end
end
