module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChart
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels Formalism.L2.Pj
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)

namespace GlobalTheory.KeyFramePoint


open scoped CategoryTheory.MonObj in
theorem card_eq_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] [Nontrivial R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n n' : ℕ} {v : Fin n → (epsR R ⟶ G')} {v' : Fin n' → (epsR R ⟶ G')}
    (hb : IsLieBasis v) (hb' : IsLieBasis v') : n = n' := by
  obtain ⟨b₁⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb
  obtain ⟨b₂⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb'
  simpa using Fintype.card_congr (b₁.indexEquiv b₂)

theorem exists_keyAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y M V K _ _ _ _ _ yt hz t m n w hw θ x hx hgen
  obtain ⟨w₁, θM, ⟨hw₁, hr₁⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev yt M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev yt M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨vM, hvM, hbM, -⟩ := M.lie V (ev yt M.U hz) t m'
  rw [hm'] at hvM
  have he : eSec t.G ≫ m.φ = yt ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ yt he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp V ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr₁

  obtain ⟨a, ha, -⟩ := hgen θM
  have hau : IsUnit a := by
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact (NonzeroClosed.of_isMul ha ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩).1
  obtain ⟨a, rfl⟩ := hau

  obtain ⟨P, hP, rig, hrig', th, hthne, v, hv⟩ := x
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := hx
  dsimp only at φ' he' w' hg' hp' hw' hr' hs' hv'
  subst hg'
  have hn : P.g = M.n := card_eq_of_isLieBasis m.cart hw hbM
  have hbM' : IsLieBasis (fun i : Fin P.g => vM (i.cast hn)) := by
    have key : ∀ (k : ℕ) (h : k = M.n), IsLieBasis (fun i : Fin k => vM (i.cast h)) := by
      rintro k rfl
      exact hbM
    exact key _ hn
  choose Mat hMat using fun i : Fin P.g => (hw.2 _ (hbM'.1 i)).exists
  obtain ⟨d, hd⟩ : IsUnit (Matrix.det (Matrix.of Mat)) :=
    ((GlobalTheory.LieComb.lieComb_algebra V t.G P.g w hw.1).2.2.2.2 (Matrix.of Mat) _ hw hMat).1 hbM'
  haveI := P.isAb.comm
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A P.g v hv.1
  choose v' hvv' using fun i => (ex (((Matrix.of Mat).map (algebraMap V K)) i)).exists
  have hdet : ((Matrix.of Mat).map (algebraMap V K)).det = algebraMap V K d := by
    rw [hd, RingHom.map_det]; rfl
  have hb' : IsLieBasis v' := (bas _ v' hv hvv').2 (hdet ▸ d.isUnit.map _)
  obtain ⟨th', e₀, -, hle⟩ := GlobalTheory.KeyPow.exists_sec_div P.A.hom (a := algebraMap V K (a⁻¹ : Vˣ)) (b := algebraMap V K a)
    (by rw [← map_mul, Units.inv_mul, map_one]) th
  have hth' : ∀ s : Sp K, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th' :=
    fun s => (hthne s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  refine ⟨⟨P, hP, rig, hrig', th', hth', v', hb'⟩, a, d, ?_, fun κ hκ => ?_⟩
  swap
  · rw [← hdet]
    exact hκ.1 K P hP rig hrig' th hthne v hv th' hth' v' hb' _ _ e₀ hvv'
  have g := (isGen_iff w₁).1 hw₁
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp t.PP.isLB w₁ w' g g' Y.t.PP.isLB P.isLB
  have he'' : eSec P.A ≫ φ' ≫ m.φ = (spMap (algebraMap V K) ≫ yt) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = dualMap (algebraMap V K) := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [dualMap])
  have hq := hp'.comp m.cart
  refine ⟨φ' ≫ m.φ, he'', w'', hn, hq, (isGen_iff w'').2 (T.pgen_comp t.PP.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₁ _ (fun _ => eSec Y.t.G) _ t.PP.rig Y.t.PP.rig yt _
      (rigPull_le m.φ yt he Y.t.PP.L) (fun _ => rfl)).1 hr₁
    have r₁ := (maps_iff w' _ (fun _ => eSec t.G) _ rig t.PP.rig (spMap (algebraMap V K)) _
      (rigPull_le φ' (spMap (algebraMap V K)) he' t.PP.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ rig Y.t.PP.rig (spMap (algebraMap V K) ≫ yt) _
      (rigPull_le (φ' ≫ m.φ) (spMap (algebraMap V K) ≫ yt) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp t.PP.isLB (fun _ => he') r₀ r₁)
  · refine (KeyAtBC.appLE_eq_iff_stalk w'' (KeyAtBC.mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ th').2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (φ' (q y))
    have a₁ := (KeyAtBC.appLE_eq_iff_stalk w₁ (KeyAtBC.mem_of_comm m.cart.1.w hz) M.θ θM).1 (fun j i h =>
      (hth (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))) Z (q ≫ φ') y j i hj hi
    have b₁ := (KeyCancel.appLE_eq_iff_stalk w' θ th).1 hs' Z q y i k hi hk
    have c₁ : gs (q ≫ φ') y _ (θM.f i) = cst ((q ≫ φ') ≫ t.G.hom) y a * gs (q ≫ φ') y _ (θ.f i) := by
      rw [ha i, gs_mul _ y _ hi, gs_constFn _ _ _ y hi]
    have c₂ : gs q y _ (th'.f k) = cst (q ≫ P.A.hom) y (algebraMap V K a) * gs q y _ (th.f k) := by
      rw [e₀ k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
    rw [Category.assoc, hp'.1.w, ← Category.assoc, cst_comp] at c₁
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a₁, c₁, b₁, c₂, Units.val_mul]
    ring
  · have e := (GlobalTheory.lieComb_baseChange V K (algebraMap V K) t.G P.A φ' hp' P.g w (vM (i.cast hn)) (Mat i) v (v' i)
      (fun j => (hv' j).trans (by rw [hF]; rfl)) (hMat i)).2 (hvv' i)
    rw [← Category.assoc, e, Category.assoc, hvM, FlagMod.ev_spMap _ yt M.U hz, FlagMod.dualMap_comp,
      KeyAtBC.spMap_comp₀, Category.assoc]
    rfl

end GlobalTheory.KeyFramePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChartStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generatingFrame_unit_change_to_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  first | exact @GlobalTheory.KeyFramePoint.exists_keyAt_units | exact GlobalTheory.KeyFramePoint.exists_keyAt_units | (intros; apply GlobalTheory.KeyFramePoint.exists_keyAt_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnH
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnH
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HalfLatInt

variable {D : D7}

theorem toEAf_idem_mul_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {a : D.host.E}
    (ha : a ∈ D.host.AA) : toEAf D (e * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  exact GlobalTheory.ConjHalfInt.toEAf_mul_mem ((hes PP hPP).2 : GlobalTheory.IdemSupport.Comparison₂ PP (es PP))
    (GlobalTheory.HalfCompare.primeToAA_of_not_mem (hP PP hPP)) ha

theorem isIntM_of_mem {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (hl : x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    IsIntM (frMapO S T βS βT x) := by
  have hx' : e • x = x := Matrix.ext hx
  rw [← hx']
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapO S T βS βT (e • u))) ?_ ?_ ?_ ?_ hl
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      unfold frMapO
      rw [GlobalTheory.ConjHalfInt.map_gen, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc (βT⁻¹).val, Matrix.mul_assoc]
      exact GlobalTheory.ConjHalfInt.isIntM_smul (mul_mem (toEAf_idem_mul_mem he hP ha) hα')
        (GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int fT ht)
          (GlobalTheory.ConjHalfInt.pair_row_int hS fS hs))
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapO_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.ConjHalfInt.frMapO_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapO_neg]
    exact fun i j => neg_mem (hu i j)


open GlobalTheory.ExportSeries.Model in
theorem isIntM_adj {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {x : WO S T} (h : IsIntM (frMapO S T βS βT x)) : IsIntM (frMapAdj S T βS βT x) := by
  have e : x.map (toEAf D) = βT.val * frMapO S T βS βT x * (βS⁻¹).val := by
    unfold frMapO
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  have := int_mul (int_mul (gram_frame_int S hS fS).2 (int_ct h)) (gram_frame_int T hT fT).1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq]
  change IsIntM (_ * ct (x.map (toEAf D)) * _)
  rw [e, ct_mul, ct_mul]
  simpa only [Matrix.mul_assoc] using this

theorem mem_of_isIntM {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) {x : WO S T}
    (hx : IsHalf e x) (h : IsIntM (frMapO S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  have hN : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  refine GlobalTheory.DatumFourier.mem_latO_of_int hS hT fS fT (Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj he) hN
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) ?_ ?_ (isIntM_adj hS hT fS fT h)
  · intro PP' hPP' hm
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hPP'
    have h2 : Formalism.L2.DIV.starOHom ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hm
    rw [map_natCast] at h2
    exact hP PP hPP (GlobalTheory.HalfCompare.mem_of_dvd h2 (Dvd.intro_left _ rfl))
  · intro i j
    rw [Formalism.L2.Theta.cA_cA]
    exact hx i j

end GlobalTheory.HalfLatInt

theorem GlobalTheory.HalfLatInt.isIntM_iff_mem_latP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ x → (IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x)) ↔ x ∈ lattice₂ R i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i _ Q hQ eQ he x hx
  obtain ⟨t, hQt⟩ := hQ
  have hSV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hSW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  obtain ⟨cV, hBV⟩ := hC.lev.βV i
  obtain ⟨cW, hBW⟩ := hC.lev.βW i
  have hP : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hG.2 t PP (hQt hPP)
  exact ⟨GlobalTheory.HalfLatInt.mem_of_isIntM hSV hSW hBV.1 hBW.1 he hP hx,
    GlobalTheory.HalfLatInt.isIntM_of_mem hSV hBV.1 hBW.1 he hP hx⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnHStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ x → (IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x)) ↔ x ∈ lattice₂ R i) := by
  first | exact @GlobalTheory.HalfLatInt.isIntM_iff_mem_latP | exact GlobalTheory.HalfLatInt.isIntM_iff_mem_latP | (intros; apply GlobalTheory.HalfLatInt.isIntM_iff_mem_latP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.CdvrLiftCp

theorem mem_int_iff' {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem norm_p_lt_one' {p : ℕ} [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem mem_range_of_norm_le {p : ℕ} [Fact p.Prime] {W L : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (kL : L →+* ℂ_[p])
    (hW : ∀ w, ‖kL (algebraMap W L w)‖ ≤ 1) (x : L) (hx : ‖kL x‖ ≤ 1) : x ∈ Set.range (algebraMap W L) := by
  by_contra hxr
  have hx0 : x ≠ 0 := by rintro rfl; exact hxr ⟨0, map_zero _⟩
  have hunit : ∀ u : Wˣ, ‖kL (algebraMap W L u)‖ = 1 := by
    intro u
    have h1 : kL (algebraMap W L u) * kL (algebraMap W L ↑u⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a1 := hW u
    have a2 := hW ↑u⁻¹
    nlinarith [norm_nonneg (kL (algebraMap W L u)), norm_nonneg (kL (algebraMap W L ↑u⁻¹))]
  obtain ⟨y, hy⟩ : IsLocalization.IsInteger W x⁻¹ :=
    (ValuationRing.isInteger_or_isInteger W x).resolve_left (fun ⟨a, ha⟩ => hxr ⟨a, ha⟩)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hx0 (inv_eq_zero.1 hy.symm)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hxr
    refine ⟨↑u⁻¹, ?_⟩
    rw [hyu, pow_zero, mul_one] at hy
    rw [map_units_inv, hy, inv_inv]
  have hy1 : ‖kL (algebraMap W L y)‖ = 1 := by
    have h1 : kL x * kL (algebraMap W L y) = 1 := by rw [← map_mul, hy, mul_inv_cancel₀ hx0, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a2 := hW y
    nlinarith [norm_nonneg (kL x), norm_nonneg (kL (algebraMap W L y))]
  have hϖ1 : ‖kL (algebraMap W L ϖ)‖ = 1 := by
    rw [hyu, map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hy1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 hy1
  have hall : ∀ w : W, w ≠ 0 → ‖kL (algebraMap W L w)‖ = 1 := by
    intro w hw
    obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    rw [map_mul, map_mul, norm_mul, hunit, map_pow, map_pow, norm_pow, hϖ1, one_pow, one_mul]
  have hp : kL (algebraMap W L (p : W)) = (p : ℂ_[p]) := by simp
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpW : (p : W) ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hp
    exact hp0 hp.symm
  have := hall _ hpW
  rw [hp] at this
  exact absurd this (ne_of_lt norm_p_lt_one')

end GlobalTheory.CdvrLiftCp

namespace GlobalTheory.CdvrLiftCp

theorem exists_cdvr_lift : ∀ (p : ℕ) [Fact p.Prime] (T : CDVR), T.FinRes → ∀ (kO : T.V →+* 𝓞_ℂ_[p]) (k : T.Fr →+* ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L] (kL : L →+* ℂ_[p]), (∀ a, kL (algebraMap T.Fr L a) = k a) → ∃ (T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr) (ψ : L ≃+* T'.Fr) (kO' : T'.V →+* 𝓞_ℂ_[p]), T'.FinRes ∧ Function.Injective kO' ∧ (∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a)) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iF a) ∧ (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap T'.V T'.Fr a))) ∧ ∀ (A : Type) [CommRing A] (f : A →+* L), (∀ a, ‖kL (f a)‖ ≤ 1) → ∃ fO : A →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (fO a) = ψ (f a) := by
  intro p _ T hT kO k hk L _ _ _ kL hkL
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  let iF : T.Fr →+* FractionRing W := ψ.toRingHom.comp (algebraMap T.Fr L)
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := by
    intro w
    change (FractionRing.algEquiv W L).symm (algebraMap W L w) = _
    exact AlgEquiv.commutes _ w
  have hψs : ∀ w : W, ψ.symm (algebraMap W (FractionRing W) w) = algebraMap W L w := by
    intro w
    rw [← hψ, RingEquiv.symm_apply_apply]
  have hφ : ∀ a, iF (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change ψ (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, hψ]
  haveI : Algebra.IsIntegral T.V W := Algebra.IsIntegral.of_finite T.V W
  have hint : ∀ w : W, kL (algebraMap W L w) ∈ 𝓞_ℂ_[p] := by
    intro w
    have hw : IsIntegral T.V w := Algebra.IsIntegral.isIntegral w
    have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = (kL.comp (algebraMap W L)).comp (algebraMap T.V W) := by
      ext a
      change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = kL (algebraMap W L (algebraMap T.V W a))
      rw [hk, ← hkL, ← RingHom.comp_apply (algebraMap W L), ← RingHom.comp_apply (algebraMap T.Fr L), hc]
    have h1 : IsIntegral 𝓞_ℂ_[p] (kL (algebraMap W L w)) := IsIntegral.map_of_comp_eq kO _ hcomp hw
    exact (PadicComplexInt.integers p).mem_of_integral h1
  have hW : ∀ w : W, ‖kL (algebraMap W L w)‖ ≤ 1 := fun w => (mem_int_iff' _).1 (hint w)
  let kO' : W →+* 𝓞_ℂ_[p] := (kL.comp (algebraMap W L)).codRestrict 𝓞_ℂ_[p] hint
  have hkO' : ∀ w, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' w) = kL (algebraMap W L w) := fun w => rfl
  refine ⟨T', algebraMap T.V W, iF, ψ, kO', ?_, ?_, fun a => (hφ a).symm, fun a => rfl, ?_, ?_⟩
  · haveI : Finite (IsLocalRing.ResidueField T.V) := hT
    exact Module.finite_of_finite (IsLocalRing.ResidueField T.V) (M := IsLocalRing.ResidueField W)
  · intro a b hab
    have h1 := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) hab
    rw [hkO', hkO'] at h1
    exact IsFractionRing.injective W L (kL.injective h1)
  · intro a
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap W (FractionRing W) a))
    rw [hkO', hψs]
  · intro A _ f hf
    have hmem : ∀ a, f a ∈ (algebraMap W L).range := fun a => mem_range_of_norm_le kL hW (f a) (hf a)
    let e : W ≃+* (algebraMap W L).range :=
      RingEquiv.ofBijective (algebraMap W L).rangeRestrict
        ⟨fun a b h => IsFractionRing.injective W L (congrArg Subtype.val h), (algebraMap W L).rangeRestrict_surjective⟩
    refine ⟨e.symm.toRingHom.comp (f.codRestrict _ hmem), fun a => ?_⟩
    change algebraMap W (FractionRing W) (e.symm (f.codRestrict _ hmem a)) = ψ (f a)
    have h2 : algebraMap W L (e.symm (f.codRestrict _ hmem a)) = f a := by
      have h3 : e (e.symm (f.codRestrict _ hmem a)) = f.codRestrict _ hmem a := e.apply_symm_apply _
      exact congrArg Subtype.val h3
    rw [← hψ, h2]

end GlobalTheory.CdvrLiftCp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunction
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetRatio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
  {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {σ σ' : Rule t π p q}

theorem sec_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) (a : ∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left)
    (b : ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left) : σ R' x' v' w' = g (σ R x v w) :=
  hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v' w'
    (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h' hx a b

theorem ratio_frame (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') {j : c.F →+* R} {x : Sp R ⟶ X} {v w v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w') {a : R}
    (e : σ' R x v w = a * σ R x v w) : σ' R x v' w' = a * σ R x v' w' := by
  have h₁ : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v' w := ⟨h.1, h.2.1, h'.2.2.1, h.2.2.2⟩
  choose M hM using fun i => (h.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  have ow : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin q) (Fin q) R) i) w (w i) :=
    fun i => DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have ov : ∀ i, IsCombAt (x ≫ π) ((1 : Matrix (Fin p) (Fin p) R) i) v' (v' i) :=
    fun i => DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
  have e1 := hσ.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e1' := hσ'.2 R j x v w v' w (Matrix.of M) 1 h h₁ hM ow
  have e2 := hσ.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  have e2' := hσ'.2 R j x v' w v' w' 1 (Matrix.of N) h₁ h' ov hN
  rw [Matrix.det_one, _root_.one_mul] at e1 e1' e2 e2'
  have hu : IsUnit (Matrix.of M).det := isUnit_of_mul_isUnit_left (e1 ▸ hn R j x v w h)
  have e3 : σ' R x v' w = a * σ R x v' w := by
    refine hu.mul_left_cancel ?_
    rw [← e1', e, e1]; ring
  rw [← e2', ← e2, e3]; ring

theorem ratio_pull (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'}
    {x : Sp R ⟶ X} {v w} {x' : Sp R' ⟶ X} {v' w'}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w')
    (hx : x' = spMap g ≫ x) {a : R} (e : σ' R x v w = a * σ R x v w) :
    σ' R' x' v' w' = g a * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h hx
  obtain rfl := (exists_chg g h h' hx).1
  refine ratio_frame hσ hn hσ' h₁ h' ?_
  rw [sec_pull hσ g h h₁ hx a₁ b₁, sec_pull hσ' g h h₁ hx a₁ b₁, e, map_mul]

theorem exists_ratio_affine (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ)
    (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ) (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ')
    {W : X.Opens} (hW : IsAffineOpen W) {j₀ : c.F →+* Γ(X, W)} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v₀ w₀) :
    ∃ f : Γ(X, W), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, ⊤ ≤ x ⁻¹ᵁ W →
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x W f * σ R x v w := by
  obtain ⟨u, hu⟩ := hn _ j₀ _ v₀ w₀ h₀
  refine ⟨σ' _ _ v₀ w₀ * u.inv, fun R _ j x v w hx h => ?_⟩
  rw [Points.valR_eq x W hx]
  refine ratio_pull hσ hn hσ' (Points.valMap x W hx).hom h₀ h (Points.specMap_valMap_fromSpec hW x hx).symm ?_
  rw [← hu, _root_.mul_assoc, u.inv_val, _root_.mul_one]

theorem valR_fromSpec {A : X.Opens} (hA : IsAffineOpen A) (f : Γ(X, A)) :
    valR (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A f = f := by
  have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
  rw [Points.valR_eq _ A hx]
  have : Points.valMap (show Sp Γ(X, A) ⟶ X from hA.fromSpec) A hx = 𝟙 _ := by
    apply Spec.map_injective
    rw [← cancel_mono hA.fromSpec, Points.specMap_valMap_fromSpec]
    exact ((congrArg (· ≫ hA.fromSpec) (Spec.map_id _)).trans (Category.id_comp _)).symm
  rw [this]
  rfl

end GlobalTheory.DetRatio


open GlobalTheory.DetRatio in
theorem GlobalTheory.detLine_exists_ratio (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ)
    (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q) (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q)
    (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) (hn : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (hσ' : IsSection t π s V (HermitianCompactForm.chi c τ) σ') :
    ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  choose W hW j₀ v₀ w₀ hz h₀ using fun z : V => hc z z.2
  choose f hf using fun z : V => exists_ratio_affine hσ hn hσ' (hW z) (h₀ z)
  have hle : ∀ z, W z ≤ V := fun z y hy => (h₀ z).2.1 (by
    change y ∈ Set.range (hW z).fromSpec
    rw [(hW z).range_fromSpec]; exact hy)
  have hcov : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hz _⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf W f := by
    intro a b
    refine X.sheaf.eq_of_locally_eq' (fun A : {A : X.affineOpens // A.1 ≤ W a ⊓ W b} => A.1.1) (W a ⊓ W b)
      (fun A => homOfLE A.2) (fun y hy => ?_) _ _ fun A => ?_
    · obtain ⟨_, ⟨A, hA, rfl⟩, hy', hA'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy (W a ⊓ W b).2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨A, hA⟩, hA'⟩, hy'⟩
    · obtain ⟨⟨A, hA⟩, hAle⟩ := A
      replace hA : IsAffineOpen A := hA
      have hx : ⊤ ≤ (show Sp Γ(X, A) ⟶ X from hA.fromSpec) ⁻¹ᵁ A := hA.fromSpec_preimage_self.ge
      have hxa := Points.le_preimage_mono _ (hAle.trans inf_le_left) hx
      have hxb := Points.le_preimage_mono _ (hAle.trans inf_le_right) hx
      have hxab := Points.le_preimage_mono _ hAle hx
      obtain ⟨v, w, h, -, -⟩ := exists_pull (Points.valMap _ (W a) hxa).hom (h₀ a)
        (Points.specMap_valMap_fromSpec (hW a) _ hxa).symm
      have e := (hn _ _ _ v w h).mul_right_cancel ((hf a _ _ _ v w hxa h).symm.trans (hf b _ _ _ v w hxb h))
      refine (valR_fromSpec hA _).symm.trans (Eq.trans ?_ (valR_fromSpec hA _))
      refine (Points.valR_res _ hAle hx _).trans (Eq.trans ?_ (Points.valR_res _ hAle hx _).symm)
      exact (Points.valR_res _ inf_le_left hxab _).trans (e.trans (Points.valR_res _ inf_le_right hxab _).symm)
  obtain ⟨F, hF, -⟩ := X.sheaf.existsUnique_gluing' W V (fun z => homOfLE (hle z)) hcov f hcomp
  refine ⟨F, fun R _ j x v w h => ?_⟩
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := fun y _ => h.2.1 ⟨y, rfl⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  let g := algebraMap R (Localization.AtPrime J)
  obtain ⟨v₁, w₁, h₁, a₁, b₁⟩ := exists_pull g h rfl
  let z : V := ⟨(spMap g ≫ x) (IsLocalRing.closedPoint (Localization.AtPrime J)), h₁.2.1 ⟨_, rfl⟩⟩
  have hxW : ⊤ ≤ (spMap g ≫ x) ⁻¹ᵁ W z := (Points.le_preimage_iff _ _).2 (hz z)
  have e := hf z _ _ _ v₁ w₁ hxW h₁
  rw [sec_pull hσ g h h₁ rfl a₁ b₁, sec_pull hσ' g h h₁ rfl a₁ b₁, ← hF z] at e
  have e' := (Points.valR_res _ (hle z) hxW F).trans (Points.valR_spMap_comp g x V hxV F)
  change g _ = 0
  rw [map_sub, map_mul, ← e', sub_eq_zero]
  exact e
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunctionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieDeterminantLine_ratio_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ) (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q), FrameCover t π s V (HermitianCompactForm.chi c τ) p q → IsSection t π s V (HermitianCompactForm.chi c τ) σ → NowhereZero t π s V (HermitianCompactForm.chi c τ) σ → IsSection t π s V (HermitianCompactForm.chi c τ) σ' → ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  first | exact @GlobalTheory.detLine_exists_ratio | exact GlobalTheory.detLine_exists_ratio | (intros; apply GlobalTheory.detLine_exists_ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqLeOfForallNonneg
noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.Bdd

theorem sq_le_of_forall_nonneg {A B D : ℤ} (h : ∀ s t : ℤ, 0 ≤ s * s * A + 2 * (s * t) * B + t * t * D) :
    B * B ≤ A * D := by
  have hA : 0 ≤ A := by simpa using h 1 0
  have hD : 0 ≤ D := by simpa using h 0 1
  rcases hA.eq_or_lt with hA0 | hA0
  · subst hA0
    have h2 := h (-B * (D + 1)) 1
    have : B = 0 := by
      by_contra hB
      have hB2 : 1 ≤ B * B := by nlinarith [mul_self_pos.2 hB]
      nlinarith
    subst this; simp
  · have h1 := h B (-A)
    nlinarith

theorem seq_le (F : ℕ → ℤ) (h0 : ∀ k, 0 ≤ F k) (hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2)) (d : ℕ)
    (p : ℕ → ℤ) (hd : p d = 1) (hrec : ∑ i ∈ Finset.range (d + 1), p i * F i = 0) :
    F 1 ≤ (∑ i ∈ Finset.range (d + 1), |p i|) * F 0 := by
  set C := ∑ i ∈ Finset.range (d + 1), |p i| with hCdef
  have hC1 : 1 ≤ C := by
    have := Finset.single_le_sum (f := fun i => |p i|) (fun i _ => abs_nonneg (p i)) (Finset.self_mem_range_succ d)
    simpa [hd] using this
  by_contra hlt
  push_neg at hlt
  have hF0 : 0 < F 0 := by
    rcases (h0 0).eq_or_lt with h | h
    · have := hlc 0
      rw [← h] at this hlt
      have h1 : F 1 * F 1 ≤ 0 := by simpa using this
      have : F 1 = 0 := by nlinarith [mul_self_nonneg (F 1)]
      simp [this] at hlt
    · exact h
  have hF1 : C * F 0 < F 1 := hlt
  have key : ∀ k, 0 < F k ∧ F 1 * F k ≤ F 0 * F (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨hF0, by rw [mul_comm]⟩
    | succ k ih =>
      obtain ⟨hk, hk'⟩ := ih
      have hpos : 0 < F (k + 1) := by
        have : 0 < F 1 * F k := mul_pos (by nlinarith) hk
        nlinarith
      refine ⟨hpos, ?_⟩
      have h2 := hlc k
      have h3 : F 1 * F k * F (k + 1) ≤ F 0 * F (k + 1) * F (k + 1) := mul_le_mul_of_nonneg_right hk' hpos.le
      have h4 : F k * (F 1 * F (k + 1)) ≤ F k * (F 0 * F (k + 2)) := by nlinarith
      exact le_of_mul_le_mul_left h4 hk
  have inc : ∀ k, C * F k < F (k + 1) := by
    intro k
    obtain ⟨hk, hk'⟩ := key k
    have : F 0 * (C * F k) < F 0 * F (k + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this hF0.le
  have mono : Monotone F := monotone_nat_of_le_succ fun k => by
    have := inc k
    have := (key k).1
    nlinarith
  cases d with
  | zero =>
    simp [hd] at hrec
    exact hF0.ne' hrec
  | succ e =>
    rw [Finset.sum_range_succ, hd, one_mul] at hrec
    rw [Finset.sum_range_succ, hd] at hCdef
    have hle : -(∑ i ∈ Finset.range (e + 1), p i * F i) ≤ (∑ i ∈ Finset.range (e + 1), |p i|) * F e := by
      rw [← Finset.sum_neg_distrib, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ e := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1 : -(p i * F i) ≤ |p i| * F i := by
        have := neg_abs_le (p i)
        nlinarith [h0 i]
      exact h1.trans (mul_le_mul_of_nonneg_left (mono hi') (abs_nonneg _))
    have he := inc e
    have hpe := (key e).1
    have : F (e + 1) = -(∑ i ∈ Finset.range (e + 1), p i * F i) := by linarith
    rw [this] at he
    rw [hCdef] at he
    simp only [abs_one] at he
    nlinarith

theorem bddAct_of_isIntegral {O : Type} [CommRing O] (bar : O → O) (hmul : ∀ a b, bar (a * b) = bar a * bar b)
    (hone : bar 1 = 1) (hinv : ∀ a, bar (bar a) = a) (hint : ∀ a : O, IsIntegral ℤ a) : BddAct bar := by
  intro c
  obtain ⟨P, hPm, hP⟩ := hint (bar c * c)
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), |P.coeff i|, ?_⟩
  intro X _ _ _ β hβ hpsd x
  have hpow : ∀ k, bar (c ^ k) = bar c ^ k := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hcs : ∀ u v : X, β u v * β u v ≤ β u u * β v v := by
    intro u v
    refine sq_le_of_forall_nonneg fun s t => ?_
    have := hpsd (s • u + t • v)
    simp only [map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hβ.1 v u] at this
    linarith
  have hF : ∀ k, β (c ^ k • x) (c ^ k • x) = β x ((bar c * c) ^ k • x) := by
    intro k
    rw [hβ.2, smul_smul, hpow, mul_pow]
  set F : ℕ → ℤ := fun k => β (c ^ k • x) (c ^ k • x) with hFdef
  have hlc : ∀ k, F (k + 1) * F (k + 1) ≤ F k * F (k + 2) := by
    intro k
    set y := c ^ k • x
    have e1 : F (k + 1) = β y ((bar c * c) • y) := by
      simp only [hFdef, y, pow_succ', mul_smul]
      rw [hβ.2, smul_smul]
    have e2 : F (k + 2) = β ((bar c * c) • y) ((bar c * c) • y) := by
      have hw : bar (c * c) * (c * c) = bar (bar c * c) * (bar c * c) := by rw [hmul, hmul, hinv]; ring
      show β (c ^ (k + 2) • x) (c ^ (k + 2) • x) = β ((bar c * c) • (c ^ k • x)) ((bar c * c) • (c ^ k • x))
      rw [show c ^ (k + 2) = (c * c) * c ^ k by ring, mul_smul, hβ.2, hβ.2 (bar c * c), smul_smul, smul_smul, hw]
      simp only [mul_smul]
    rw [e1, e2]
    exact hcs _ _
  have hrec : ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * F i = 0 := by
    have h0 : β x ((Polynomial.aeval (bar c * c) P) • x) = 0 := by rw [Polynomial.aeval_def, hP, zero_smul, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_smul, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFdef]
    dsimp only
    rw [hF, smul_assoc, map_zsmul, smul_eq_mul]
  have := seq_le F (fun k => hpsd _) hlc P.natDegree P.coeff hPm.coeff_natDegree hrec
  simpa [hFdef] using this

end GlobalTheory.Poinc.Bdd

namespace GlobalTheory.Poinc

open NumberField

theorem bddAct_int_and_cm : BddAct (id : ℤ → ℤ) ∧ ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), BddAct H.bar := by
  refine ⟨Bdd.bddAct_of_isIntegral id (fun _ _ => rfl) rfl (fun _ => rfl) fun a => Algebra.IsIntegral.isIntegral a, ?_⟩
  intro E _ _ _ H
  refine Bdd.bddAct_of_isIntegral H.bar (fun a b => map_mul _ a b) (map_one _) (fun a => ?_)
    fun a => Algebra.IsIntegral.isIntegral a
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProof
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceLevelPf

variable {D : D7} {S T : HSp D}

theorem series_om_fin {B : Base S T} (hB : B.Good) {χS χT : (AE D)ˣ →* Circle} {ω : PairRep S T}
    (hω : IsWeilDatumO B.F.ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f) (h : GA D S)
    (P : PolF D T.rank S.rank) (g : GA D T) {κ : GA D T} (hκ : κ ∈ GfC T) :
    series B.F ω (ω (1, κ) f) h P g = series B.F ω f h P (g * κ) := by
  rw [series_apply, series_apply]
  have e : ((h, g * κ) : GA D S × GA D T) = (h, g) * (1, κ) := Prod.ext (mul_one h).symm rfl
  rw [e, map_mul, Module.End.mul_apply, Frame.fock, Frame.fock,
    GlobalTheory.OrientedHeis.om_fin_pureTensorO B.F.ψ S T χS χT ω hω B.F.θ hB.frame.vac.2.inf 1 (one_mem _) κ hκ _ _ _ _ f P hf]

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
  {B : Base (Vc D i) (Wc D i)}

theorem rTup_datWp_val (x : GL (Fin (Wc D i).rank) (EAf D)) (PP : ↥(R.datWp i R.triv).Pg) (a b : Fin (R.datWp i R.triv).r) :
    (rTup (R.βW i) (R.datWp i R.triv) x PP).val a b =
      (redFn (R.βW i) PP.1 x).val (Fin.castLE (R.datWp i R.triv).hr a) (Fin.castLE (R.datWp i R.triv).hr b) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hm : redFn (R.βW i) PP.1 x ∈ blockTri (blk2 (R.datWp i R.triv).r) := by
    refine mem_blockTri.2 fun c d hcd => ?_
    have hc : c.val < (R.datWp i R.triv).r := lt_of_lt_of_eq c.2 rW
    have e : blk2 (R.datWp i R.triv).r c = 0 := if_pos hc
    exact absurd (lt_of_lt_of_eq hcd e) (Nat.not_lt_zero _)
  unfold rTup
  rw [upper_block_val_submatrix _ hm]
  rfl

theorem red_of_rTup (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g) : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x := by
  intro PP
  have hP : PP.1 ∈ R.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := congrArg (fun y : G0 (R.datWp i R.triv).Pg (R.datWp i R.triv).r => (y ⟨PP.1, hP⟩).val (Fin.cast (rank_Wc i) a)
    (Fin.cast (rank_Wc i) c)) hx
  simp only at h1
  rw [rTup_datWp_val] at h1
  rw [hent g PP.1 PP.2 hP a c]
  exact h1.symm.trans (by rw [hB.βT]; rfl)

theorem rTup_of_red (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) (x : GL (Fin (Wc D i).rank) (EAf D))
    (hx : ∀ PP : ↥B.G.Pg, e g PP = redFn B.F.βT PP.1 x) : rTup (R.βW i) (R.datWp i R.triv) x = R.eG g := by
  funext PP
  have hP : PP.1 ∈ B.G.Pg := hB.Pg ▸ PP.2
  refine Units.ext (Matrix.ext fun a c => ?_)
  have h1 := hent g PP.1 hP PP.2 (Fin.cast (rank_Wc i).symm a) (Fin.cast (rank_Wc i).symm c)
  rw [hx ⟨PP.1, hP⟩, hB.βT] at h1
  rw [rTup_datWp_val]
  exact h1

theorem lifts_of_datWp (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) {g : G} {κ : GA D (Wc D i)}
    (hκ : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) : GlobalTheory.ExportType.Lifts B (e g) κ :=
  ⟨hκ.1, hB.βT ▸ parLev_St hκ.2.1, red_of_rTup hB e hent g _ hκ.2.2⟩

theorem exists_lift_datWp (hB0 : B.Good) (hB : BaseOf R i B) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) (g : G) :
    ∃ κ, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  obtain ⟨κ, hκ, -⟩ := GlobalTheory.TypeSupportLift.exists_lift_supp B hB0 (e g)
  have h1 := GlobalTheory.FlatVecSum.levelLift_isLift_principalLevelDatum_realisation hB hκ
  rw [rTup_of_red hB e hent g _ (GlobalTheory.ExportType.lifts_of_isLiftG0 hκ).red] at h1
  exact ⟨κ, h1⟩

end Real

theorem traceLevel : GlobalTheory.BaseCmp.TraceLevel := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i B hB hBo U ψ e hent hU hchi ω hω hh P
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (GlobalTheory.FlatVecSum.princ B).vecBase :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) (Base.admissible_empty_of_good (GlobalTheory.FlatVecSum.princ_good hB)) _)
      hB.frame.vac.2.theta
  have hsum : B.vecBase = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) (GlobalTheory.FlatVecSum.princ B).vecBase := by
    have := GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) (Twist.triv_good splitSet_empty) (Base.admissible_empty_of_good hB)
      (ω := ω) hω (fun p => (hlift (e.symm p)).choose) (fun p => by
        have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
        rwa [MulEquiv.apply_symm_apply] at this)
    rwa [Base.vecFlat_triv, Base.vecFlat_triv] at this
  funext x
  have hL : levelTrace R i U ψ ((GlobalTheory.FlatVecSum.princ B).theta ω hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : B.theta ω hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω (GlobalTheory.FlatVecSum.princ B).vecBase hh P (x * (hlift (e.symm p)).choose) := by
    rw [Base.theta, hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dite_eq_right, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dite_eq_left hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceLevelPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTraceLevelCompatible_proof : GlobalTheory.BaseCmp.TraceLevel := by
  first | exact @GlobalTheory.TraceLevelPf.traceLevel | exact GlobalTheory.TraceLevelPf.traceLevel | (intros; apply GlobalTheory.TraceLevelPf.traceLevel <;> assumption)
end
end
