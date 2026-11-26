module

public import Development.WeilBound.ThetaLifts.AgreeOfLeaves
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaEvaluationZeroCone
public import Development.WeilBound.ThetaLifts.WeilDomination.ExistsUnitChrWNe
public import Development.WeilBound.ThetaLifts.CartanFactorisation.InjPure
public import Development.WeilBound.ThetaLifts.WeilDomination.SwAnisoXOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.BadFin
public import Development.WeilBound.ThetaLifts.SmallCones.SplitInv
public import Development.WeilBound.ThetaLifts.LocalTheory.HypOf
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.FLocBOf
public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.BumpAFin
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.DarbouxExt
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.UnramifiedDeterminedBySphericalHolds
public import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ArchimedeanMultiplicityOneOfLie
public import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ExistsVol
public import Development.WeilBound.ThetaLifts.LocalTheory.LocBOf
public import Development.WeilBound.ThetaLifts.Reductions.TopPolarZero.PolZero
public import Development.WeilBound.ThetaLifts.Reductions.JoinTriOf
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.VacIntZ
public import Development.WeilBound.ThetaLifts.Reductions.WeightConstants.ConstOfGood
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.TraceBlocks
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaBasic
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.PerpZeroOf
public import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwo
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixXClosed
public import Development.WeilBound.ThetaLifts.WeilDomination.DomWeilOf
public import Development.WeilBound.ThetaLifts.SmallCones.ThetaExp
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.SmallAnyOf
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.EigenKillSet
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.SubMemKer
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.KRealAsm
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.UpperProjectionInverseTransposeRightInverse
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ValuationIntegersEqCompletion
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct
public import Development.WeilBound.ThetaLifts.WeilDomination.MatchEx
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.RealVanishOf
public import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SlicePol
public import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFacOf
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.TwoStepOf
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.LocalFieldT2Space
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ActsOfReads
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ColOpSingle
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.CuspOfLineOfKeys
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConstFin
public import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
public import Development.WeilBound.ThetaLifts.Reductions.ArchimedeanMatchedMapsCompare
public import Development.WeilBound.ThetaLifts.CartanFactorisation.KillInf
public import Development.WeilBound.ThetaLifts.SmallCones.SoZeroAOf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxFinTOfPublished
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolReOf2T
noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKF PositivityTheory.HoweDualityUnitaryAlt
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem cmp_finT (hM : MaxFinT) {R R₂ : RealMaps F a a'} {Rf Rf₂ : FinMaps F a a'} (m : IsMatched B G X om om' R Rf)
    (v : Pl F) (n₂ : Nontrivial (Rf₂.Pi v)) (o : (SB _).map (Rf₂.p v) = ⊤) (o' : (SB _).map (Rf₂.p' v) = ⊤)
    (x₁ : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p v) ⊓ SB _))
    (x₂ : Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p' v) ⊓ SB _))
    (eq₂ : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      Rf₂.p v φ = Rf₂.p' v φ' → Rf₂.p v φ₁ = Rf₂.p' v φ₁') :
    ∃ (e : Rf.Pi v →ₗ[ℂ] Rf₂.Pi v) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ SB _, e (Rf.p v x) = Rf₂.p v x) ∧
      ∀ x ∈ SB _, e (Rf.p' v x) = c • Rf₂.p' v x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om
    ⟨p1.base, ⟨_, _, p1.herm⟩, ⟨_, _, p1.skew⟩, p1.good, ⟨_, _, p1.weil⟩⟩ v
  choose A' hA' hA'' using fun (i : UAt σ G.W (evFin F v)) (x : SB (Fin a' × Fin (a + a') → Fv F v)) => ex_fin p2 v i x x.2
  have ac : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)),
      Acts (evFin F v) (om (1, i.1)) x (ω (1, i.1) x) := fun i x => (hω.acts 1 (one_at _) i i.2 x x.2 _).2 rfl
  have pr : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)), ω (1, i.1) x ∈ SB _ :=
    fun i x => hω.pres 1 (one_at _) i i.2 x x.2
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  exact schur_match (SB _) (SB _) (Rf.p v) (Rf.p' v) (Rf₂.p v) (Rf₂.p' v) (m.fin.onto v) (m.fin.onto' v) o o'
    (fun x hx => (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).1 _ _ (maxFinP m v).1 x₁) x hx).1)
    (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).2 _ _ (maxFinP m v).2 x₂))
    (fun i : UAt σ G.W (evFin F v) => ω (1, i.1) ∘ₗ Submodule.subtype _) A' pr hA'
    (fun i x x' => m.fin.equiv v i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun i x x' => eq₂ i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun N hN => m.fin.irred v N fun h hh x hx y _ e hp => by
      rw [(hω.acts 1 (one_at _) h hh x hx y).1 e]; exact hN ⟨h, hh⟩ ⟨x, hx⟩ hp)
    (rank_SB _)

theorem polRe_of2T (hH : PositivityTheory.ThKR.JoinTri) (hM : MaxFinT) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    (hJ : CartanConj) (hV : CartanMove) (hK : KCoinv) (hI : ILeft) : PolRe := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' R Rf m V V' W R₂ Rf₂ m₂ ⟨c₂, hc₂, hc⟩
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨h, hh, hh'⟩ := hJ F E σ B _ G.W W _ _ p1.base p1.skew m₂.triple.geo.hW
  obtain ⟨g, hg, hg', hP⟩ := hV F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 V W (reG G V V' W).M rfl (pairV m₂.triple) h hh hh'
  obtain ⟨g', hk, hk', hP'⟩ := hV F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 V' W (reG G V V' W).M' rfl (pairV' m₂.triple) h hh hh'
  obtain ⟨T, hT, -⟩ := hO F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 g hg h hh
  obtain ⟨T', hT', -⟩ := hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 g' hk h hh
  obtain ⟨e, c, c0, he, he'⟩ := archimedean_matched_maps_compare hH hO hL hQ hC ⟨m₂.triple, real_trans hO hL hQ m.triple m₂.triple m.real ⟨hg, hg'⟩ ⟨hk, hk'⟩
    ⟨hh, hh'⟩ hT hT' (hP T hT) (hP' T' hT'), m₂.fin⟩ m₂
  choose ef cf cf0 hef hef' using fun v => cmp_finT (R₂ := R₂) hM m v (m₂.fin.nontriv v) (m₂.fin.onto v) (m₂.fin.onto' v)
    (maxFinP m₂ v).1 (maxFinP m₂ v).2 (m₂.fin.equiv v)
  have cf1 : ∀ v ∉ X.T, cf v = 1 := fun v hv => by
    obtain ⟨s1, s2⟩ := m₂.fin.sph v hv
    have x1 := hef v _ (p1.good.vac v).1
    rw [(m.fin.sph v hv).1, hef' v _ (p2.good.vac v).1] at x1
    have x2 : cf v • Rf₂.p v (G.M.vac v) = (1 : ℂ) • Rf₂.p v (G.M.vac v) := by
      rw [one_smul]; exact (congrArg (cf v • ·) s1).trans x1
    exact smul_left_injective ℂ s2 x2
  let Λ : ℂ := c * ∏ v ∈ X.T, cf v
  refine ⟨c₂ * Λ, mul_ne_zero hc₂ (mul_ne_zero c0 (Finset.prod_ne_zero_iff.2 fun v _ => cf0 v)), ?_⟩
  rintro Φ Φ' hΦ' ⟨S, hS, k, k', f, φ, f', φ', h1, h2, rfl, rfl, eq⟩ x
  choose u hu hu' using fun i => (show f i ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) from hP T hT ▸ (h1 i).1)
  choose u' hw hw' using fun i => (show f' i ∈ ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) from hP' T' hT' ▸ (h2 i).1)
  have e1 := move_sum p1.good hT u φ (fun i => (h1 i).2.1) fun i => ev_of_off (h1 i).2.2
  have e2 := move_sum p2.good hT' u' φ' (fun i => (h2 i).2.1) fun i => ev_of_off (h2 i).2.2
  have fu : ∀ i, T (u i) = f i := hu'
  have fu' : ∀ i, T' (u' i) = f' i := hw'
  simp only [fu] at e1
  simp only [fu'] at e2
  have s1 : ∑ i, pure (u i) (φ i) ∈ schA F _ := sum_mem fun i _ =>
    GlobalTheory.TensUniq.pure_mem_schA _ _ (h1 i).2.1 ((good_std p1.good).congr (ev_of_off (h1 i).2.2))
  have so : ∑ i, pure (u' i) (φ' i) ∈ G.M'.So B.ψ B.τ₁ := by
    have := (hK F E σ B a a' G X om om' R Rf m).2 (g', h)⁻¹ _ hΦ'
    rwa [← e2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e3 : Λ • ∑ i, pure (u' i) (φ' i) = ∑ i, pure (Λ • u' i) (φ' i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => funext fun y => (mul_assoc _ _ _).symm
  have pm : PolMatch B (reG G V V' W) X R₂ Rf₂ (∑ i, pure (u i) (φ i)) (Λ • ∑ i, pure (u' i) (φ' i)) := by
    refine ⟨S, hS, k, k', u, φ, fun i => Λ • u' i, φ', fun i => ⟨hu i, (h1 i).2⟩,
      fun i => ⟨Submodule.smul_mem _ _ (hw i), (h2 i).2⟩, rfl, e3, ?_⟩
    have := congrArg (TensorProduct.map e (PiTensorProduct.map fun v : S => ef v)) eq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [← fu i, show e (R.p (T (u i))) = R₂.p (u i) from he _ (hu i)]
      simp only [hef _ _ ((h1 i).2.1 _)]
    · rw [← fu' j, show e (R.p' (T' (u' j))) = c • R₂.p' (u' j) from he' _ (hw j)]
      simp only [hef' _ _ ((h2 j).2.1 _)]
      rw [MultilinearMap.map_smul_univ, TensorProduct.smul_tmul_smul, map_smul, TensorProduct.smul_tmul']
      simp only [RingHom.id_apply]
      rw [Finset.prod_coe_sort S cf, ← Finset.prod_subset hS fun v _ hv => cf1 v hv]
  have := hc _ _ (Submodule.smul_mem _ Λ (so_re V V' W so)) pm (x * h)
  rw [← e1, ← e2, I_move hI p1 s1, I_move hI p2 (so_le p2.good _ so), mul_assoc, ← I_smul]
  exact this

end GlobalTheory.CompanionTheory.ThetaK

end
end

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem PositivityTheory.HoweDualityUnitaryAlt.polRe_of2T : PositivityTheory.ThKR.JoinTri → PositivityTheory.HoweDualityUnitaryAlt.MaxFinT → PositivityTheory.ThKF.ArchOp → PositivityTheory.ThKF.ArchLie → PositivityTheory.ThKF.ArchUniq → PositivityTheory.ThKF.PolCount → PositivityTheory.ThKF.CartanConj → PositivityTheory.ThKF.CartanMove → GlobalTheory.ThK.KCoinv → PositivityTheory.ThKF.ILeft → GlobalTheory.ThK.PolRe := GlobalTheory.CompanionTheory.ThetaK.polRe_of2T
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.ThetaKillsCuspFormsSpherical
noncomputable section

namespace PositivityTheory.Sph

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThK PositivityTheory.ThKF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r q r' q' : ℕ}

theorem killFin3 (hU : Unimod) (hT : ThetaBasic) (hP : PureAct) (hL : LocCpt) (hp : IsPair B M χX χW om r q r' q') {𝓒}
    (hc : Cls B M om 𝓒) (v : Pl F) (hsa : SphAt M B.ψ om v ∨ IrrAt om v) {N}
    (hN : GlobalTheory.Published.ThetaSub om v N) (hNe : N ≠ SB _)
    {f} (hf : f ∈ M.Pol B.ψ B.emb) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    (h𝓒 : ∀ x ∈ SB _, pure f (upd φ v x) ∈ 𝓒) (hv : φ v ∈ N) : M.I om (pure f φ) = 0 := by
  classical
  obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one hP hp f h1 h2 v
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, ⟨_, _, hp.weil⟩⟩ v
  obtain ⟨hΓ, μ, 𝓕, hμ, h𝓕, hr⟩ := uniW hU hp
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  obtain ⟨hinv, hmul, -⟩ := hL F E σ d W v
  have o1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by simp [mat]
  have o2 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by simp [mat]
  let Q := SB (Fin n × Fin d → Fv F v)
  have jc : ∀ x : Q, j x ∈ 𝓒 := fun x => hj x ▸ h𝓒 x x.2
  let u : Q →ₗ[ℂ] (UA σ W.J → ℂ) :=
    { toFun := fun x => M.I om (j x)
      map_add' := fun x y => by rw [Submodule.coe_add, map_add (f := _), I_add' hp hc (jc x) (jc y)]
      map_smul' := fun c x => funext fun h => by
        rw [Submodule.coe_smul, map_smul]; exact PositivityTheory.ThKG.I_smul M om c _ h }
  have hu' : ∀ x, u x = M.I om (j x) := fun _ => rfl
  have uc : ∀ x, Continuous (u x) := fun x => hc.cont _ (jc x)
  have u2 : ∀ x, IntegrableOn (fun g => ‖u x g‖ ^ 2) 𝓕 μ := fun x => hc.sq μ 𝓕 hμ h𝓕 _ (jc x)
    (hj x ▸ Submodule.subset_span ⟨f, hf, _, upd_sb h1 x.2, upd_cof h2 v x, rfl⟩)
  have ui : ∀ x, L2.Inv (ratU σ W.J) (u x) := fun x => I_inv hT hp (hc.sch (jc x))
  have augle : augAt om v ≤ Q := hN.1.trans hN.2.1
  have uaug : ∀ z ∈ augAt om v, M.I om (j z) = 0 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
      have e : j y = j (y - x) + j x := by rw [← map_add (f := _), sub_add_cancel]
      have e2 := I_add' hp hc (jc ⟨y - x, sub_mem hy hx⟩) (jc ⟨x, hx⟩)
      rw [← e, ← hjS _ x hx y hxy, I_left hU hT hp (hc.sch (jc ⟨x, hx⟩))] at e2
      exact (left_eq_add.1 (e2.trans (add_comm _ _)))
    | zero => rw [map_zero]; exact PositivityTheory.ThKG.I_zero M om
    | add a b ha hb iha ihb => rw [map_add (f := _), I_add' hp hc (jc ⟨a, augle ha⟩) (jc ⟨b, augle hb⟩), iha, ihb, add_zero]
    | smul c a _ iha => funext h; rw [map_smul, PositivityTheory.ThKG.I_smul, iha]; simp
  rcases hsa with hsa | hsa
  swap
  · have e := (hsa N hN).resolve_right hNe
    have := uaug _ (e ▸ hv)
    rwa [hj, upd_eq] at this
  obtain ⟨s, hs⟩ := hsa ω ρ hω
  obtain ⟨β, hβ, -, -⟩ := exists_beta 𝓕 μ u uc u2
  let A : ∀ h ∈ UAt σ W (evFin F v), Module.End ℂ Q := fun h hh => (ω (1, h)).restrict (hω.pres 1 o1 h hh)
  have hA : ∀ h hh (x : Q), (A h hh x : _ → ℂ) = ω (1, h) x := fun _ _ _ => rfl
  have uA : ∀ h hh x g, u (A h hh x) g = u x (g * h) := fun h hh x g => by
    rw [hu', hu', hA h hh, ← hjS (om (1, h)) x x.2 _ ((hω.acts 1 o1 h hh x x.2 _).2 rfl), I_right]
  have iso : ∀ h hh x y, β (A h hh x) (A h hh y) = β x y := fun h hh x y => by
    simp only [hβ, uA]; exact L2.form_right h𝓕 (ui x) (ui y) h
  have Amul : ∀ h hh h' hh' x, A (h * h') (hmul h hh h' hh') x = A h hh (A h' hh' x) := fun h hh h' hh' x =>
    Subtype.ext (by
      have := hω.mul 1 o1 h hh 1 o1 h' hh' x x.2
      rw [mul_one] at this
      exact this)
  have Aone : ∀ x, A 1 o2 x = x := fun x => Subtype.ext (hω.one x x.2)
  have st := stab_of hω hN
  have sN : s ∉ N := Stab.not_mem hs.gen st hNe
  have bz : ∀ x y : Q, y.1 ∈ augAt om v → β x y = 0 := fun x y hy => by
    rw [hβ, show u y = 0 from (hu' y).trans (uaug _ hy)]; simp
  have bz' : ∀ x y : Q, x.1 ∈ augAt om v → β x y = 0 := fun x y hx => by
    rw [hβ, show u x = 0 from (hu' x).trans (uaug _ hx)]; simp
  let sQ : Q := ⟨s, hs.mem⟩
  have s0 : s ≠ 0 := by
    rintro rfl
    refine hNe (le_antisymm hN.2.1 fun φ hφ => (sup_le hN.1 (Submodule.span_le.2 ?_)) (hs.gen φ hφ))
    rintro _ ⟨h, hh, rfl⟩
    rw [map_zero]
    exact N.zero_mem

  have kA : ∀ y : Q, y.1 ∈ N → β sQ y = 0 := fun y hy => by
    obtain ⟨m, k, w, c, hw, hc⟩ := hs.line y.1 y.2
    have hsum : ∑ i, w i • ω (1, k i) y.1 ∈ N := N.sum_mem fun i _ => N.smul_mem _ (st.2.2 (k i) (hw i).1 y.1 hy)
    have hcs : c • s ∈ N := by
      have := N.sub_mem hsum (hN.1 hc)
      rwa [sub_sub_cancel] at this
    have c0 : c = 0 := by
      by_contra hc0
      have := N.smul_mem c⁻¹ hcs
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
      exact sN this
    rw [c0, zero_smul, sub_zero] at hc
    let z : Q := ∑ i, w i • A (k i) (hw i).1 y
    have hz : (z : _ → ℂ) = ∑ i, w i • ω (1, k i) y.1 := by
      simp only [z, Submodule.coe_sum, Submodule.coe_smul, hA]
    have h0 : β sQ z = 0 := bz sQ z (by rw [hz]; exact hc)
    have hk : ∀ i, β sQ (A (k i) (hw i).1 y) = starRingEnd ℂ (w i) * β sQ y := fun i => by
      have e : sQ = w i • A (k i) (hw i).1 sQ := Subtype.ext (by
        rw [Submodule.coe_smul, hA (k i) (hw i).1]; exact ((hw i).2).symm)
      calc β sQ (A (k i) (hw i).1 y) = β (w i • A (k i) (hw i).1 sQ) (A (k i) (hw i).1 y) := by
            rw [← e]
        _ = starRingEnd ℂ (w i) * β sQ y := by
            rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, iso (k i) (hw i).1, smul_eq_mul]
    have e3 : β sQ z = (∑ i, w i * starRingEnd ℂ (w i)) * β sQ y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [z, map_sum, map_smul, hk, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0] at e3
    have w0 : w 0 ≠ 0 := fun e => s0 (by
      have := (hw 0).2
      rw [e, zero_smul] at this
      exact this.symm)
    have pos : (0 : ℝ) < ∑ i, Complex.normSq (w i) :=
      lt_of_lt_of_le (Complex.normSq_pos.2 w0)
        (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (w i)) (Finset.mem_univ 0))
    have hne : (∑ i, w i * starRingEnd ℂ (w i)) ≠ 0 := by
      simp_rw [Complex.mul_conj]
      rw [← Complex.ofReal_sum]
      exact_mod_cast pos.ne'
    exact (mul_eq_zero.1 e3.symm).resolve_left hne

  have kB : ∀ y : Q, y.1 ∈ N → ∀ h (hh : h ∈ UAt σ W (evFin F v)), β (A h hh sQ) y = 0 := fun y hy h hh => by
    have e : A h hh (A h⁻¹ (hinv h hh) y) = y := by
      rw [← Amul h hh h⁻¹ (hinv h hh)]
      simp only [mul_inv_cancel, Aone]
    calc β (A h hh sQ) y = β (A h hh sQ) (A h hh (A h⁻¹ (hinv h hh) y)) := by rw [e]
      _ = β sQ (A h⁻¹ (hinv h hh) y) := iso h hh _ _
      _ = 0 := kA _ (by rw [hA h⁻¹ (hinv h hh)]; exact st.2.2 h⁻¹ (hinv h hh) y.1 hy)

  have kC : ∀ y : Q, y.1 ∈ N → ∀ z : Q, β z y = 0 := fun y hy z => by
    have hle : augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) s} ≤
        (LinearMap.ker (β.flip y)).map Q.subtype := by
      refine sup_le ?_ (Submodule.span_le.2 ?_)
      · intro a ha
        exact ⟨⟨a, augle ha⟩, by rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]; exact bz' _ _ ha, rfl⟩
      · rintro _ ⟨h, hh, rfl⟩
        exact ⟨A h hh sQ, by rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]; exact kB y hy h hh, rfl⟩
    obtain ⟨z', hz', e⟩ := hle (hs.gen z.1 z.2)
    rw [show z = z' from (Subtype.ext e).symm]
    have h0 : β.flip y z' = 0 := hz'
    rwa [LinearMap.flip_apply] at h0
  have key : β ⟨φ v, h1 v⟩ ⟨φ v, h1 v⟩ = 0 := kC _ hv _
  have := L2.eq_zero h𝓕 (uc _) (ui _) (u2 _) ((hβ _ _).symm.trans key)
  rwa [hu', hj, upd_eq] at this

theorem theta_kills_cusp_forms_spherical (hT : ThetaBasic) (hW : WeilConv) (hc : SoCont) (hS : SqInt) (hD : KDecay) (hK : KCoinv) (hC : ICont)
    (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hAi : RadMax) (hSph : SphTri) (hH : PositivityTheory.ThKR.JoinTri)
    (hSo : SoCoinv) : Kills := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf m
  have p1 := PositivityTheory.ThKG.pairV m.triple
  have p2 := PositivityTheory.ThKG.pairV' m.triple
  have c1 := clsV hW hC hS m.triple
  have c2 := clsV' hD hK hc hC hS m
  have sch : ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → pure f φ ∈ schA F _ :=
    fun f φ h1 h2 => by
      obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA p1.good φ h1 h2
      rw [e]
      exact PositivityTheory.ThKG.pureA_mem f hg
  refine ⟨fun f hf φ h1 h2 h => ?_, fun f hf φ h1 h2 h3 h => ?_⟩
  · rcases h with h | ⟨v, h⟩
    · exact killInf' unimodularity_holds hT hO hL hQ exists_maximal_compact_infinite p1 (hAi F E σ B a a' G X om om' m.triple).1 c1 (maxInfP hO hL hQ m).1
        (hH F E σ B a a' G X om om' m.triple).1 h1 h2 (fun f => sch f φ h1 h2) ⟨h, hf⟩
    · exact killFin3 unimodularity_holds hT pureAct local_compact_open_subgroups p1 c1 v (hSph F E σ B a a' G X om om' m.triple v).1
        (maxFinP m v).1.prop.1 (maxFinP m v).1.prop.2 hf h1 h2
        (fun x hx => sch f _ (upd_sb h1 hx) (upd_cof h2 v x)) ⟨h, h1 v⟩
  · rcases h with h | ⟨v, h⟩
    · exact killInf' unimodularity_holds hT hO hL hQ exists_maximal_compact_infinite p2 (hAi F E σ B a a' G X om om' m.triple).2 c2 (maxInfP hO hL hQ m).2
        (hH F E σ B a a' G X om om' m.triple).2 h1 h2
        (fun f => upd_eq φ B.v₁ ▸ pure_soK m.triple f h1 h2 h3) ⟨h, hf⟩
    · by_cases e : v = B.v₁
      · subst e
        have ha := hSo F E σ B a a' G X om om' m.triple _ h3
          ((((hK F E σ B a a' G X om om' R Rf m).1 _ m.triple.chars.good).2.1 _ (h1 _)).1 h)
        obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one pureAct p2 f h1 h2 B.v₁
        have key : ∀ z ∈ augOn om' B.v₁ (G.M'.SoLoc B.ψ B.τ₁), j z ∈ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' (j z) = 0 := fun z hz => by
          induction hz using Submodule.span_induction with
          | mem z h =>
            obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
            have a1 : j x ∈ G.M'.So B.ψ B.τ₁ := hj x ▸ pure_soK m.triple f h1 h2 (Submodule.subset_span hx)
            have a2 : j y ∈ G.M'.So B.ψ B.τ₁ := hjS _ x hx.1 y hxy ▸ (hK F E σ B a a' G X om om' R Rf m).2 _ _ a1
            have a3 : j (y - x) ∈ G.M'.So B.ψ B.τ₁ := by rw [map_sub]; exact sub_mem a2 a1
            have e2 := I_add' p2 c2 a3 a1
            rw [← map_add (f := _), sub_add_cancel, ← hjS _ x hx.1 y hxy, I_left unimodularity_holds hT p2 (c2.sch a1)] at e2
            exact ⟨a3, left_eq_add.1 (e2.trans (add_comm _ _))⟩
          | zero => rw [map_zero]; exact ⟨zero_mem _, PositivityTheory.ThKG.I_zero _ _⟩
          | add a b _ _ iha ihb => rw [map_add (f := _), I_add' p2 c2 iha.1 ihb.1, iha.2, ihb.2, add_zero]; exact ⟨add_mem iha.1 ihb.1, rfl⟩
          | smul c a _ iha =>
            rw [map_smul]
            exact ⟨Submodule.smul_mem _ _ iha.1, funext fun h => by rw [PositivityTheory.ThKG.I_smul, iha.2]; simp⟩
        have := (key _ ha).2
        rwa [hj, upd_eq] at this
      · exact killFin3 unimodularity_holds hT pureAct local_compact_open_subgroups p2 c2 v (hSph F E σ B a a' G X om om' m.triple v).2
          (maxFinP m v).2.prop.1 (maxFinP m v).2.prop.2 hf h1 h2
          (fun x hx => upd_eq (upd φ v x) B.v₁ ▸ pure_soK m.triple f (upd_sb h1 hx) (upd_cof h2 v x)
            (by rwa [upd_ne _ _ _ (Ne.symm e)])) ⟨h, h1 v⟩

end PositivityTheory.Sph

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.SphericalClosure.EndCore
theorem PositivityTheory.Sph.Tr.endAB_sph
    (hSiegelSet : GlobalTheory.Published.SiegelSetUnitary)
    (h_Weil6_ThKG_Tow_WeilEx : PositivityTheory.ThKG.Tow.WeilEx)
    (hKCo : PositivityTheory.KCo.DictSt → GlobalTheory.ThK.KCoinv)
    (hFinRam : PositivityTheory.ThK.FinRam)
    (hFinSplit : PositivityTheory.ThK.FinSplit)
    (hFinInert : PositivityTheory.ThK.FinInert)
    (h_LieSecond : GlobalTheory.RealLift.LieSecond)
    (h_Weil6_ThKF_ArchLie : PositivityTheory.ThKF.ArchLie)
    (h_SWStd : GlobalTheory.ThK.Dbl.SiegelWeilStd)
    (h_EisBL : GlobalTheory.ThK.Dbl.EisBL) :
    GlobalTheory.ThK.EndA ∧ GlobalTheory.ThK.EndB := by
  have h_Bump : GlobalTheory.ThK.Dbl.Bump := GlobalTheory.ThK.Dbl.bump
  have h_FrameConj : GlobalTheory.ThK.Dbl.FrameConj := (GlobalTheory.ThK.Dbl.frameConj)
  have h_Weil6_ThKEnd_Cusp_VacBar := PositivityTheory.ThKEnd.Cusp.vacBar
  have h_GlobalTheory_ThK_Dbl_LocUnrSplit := GlobalTheory.ThK.Dbl.locUnrSplit
  have h_GlobalTheory_ThK_Dbl_BadFactor : GlobalTheory.ThK.Dbl.BadFactor := GlobalTheory.ThK.Dbl.badFactor_of GlobalTheory.ThK.Dbl.dblX PositivityTheory.ThKG.Tow.stabEx GlobalTheory.ThK.Dbl.vacFix2 h_Bump
  have h_Weil6_ThKEnd_Iwa : PositivityTheory.ThKEnd.Iwa := (PositivityTheory.ThKG.Tow.iwa)
  have h_Weil6_ThKEnd_CTBasic : PositivityTheory.ThKEnd.CTBasic := (PositivityTheory.ThKEnd.Grp.ctBasic)
  have h_Weil6_ThKEnd_LineMove : PositivityTheory.ThKEnd.LineMove := (PositivityTheory.ThKEnd.Grp.lineMove)
  have h_GlobalTheory_ThK_ThetaBasic : GlobalTheory.ThK.ThetaBasic := (PositivityTheory.ThKF0.thetaBasic)
  have h_Weil6_ThKF_ICont : PositivityTheory.ThKF.ICont := (PositivityTheory.ThKEst.iCont hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKCT_SoStab : PositivityTheory.ThKCT.SoStab := (PositivityTheory.ThKCT.soStab_of)
  have h_Weil6_ThKEnd_IAut : PositivityTheory.ThKEnd.IAut := (PositivityTheory.ThKEnd.Grp.iAut_of h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_ICont h_Weil6_ThKCT_SoStab)
  have h_Weil6_ThKF_ArchOp : PositivityTheory.ThKF.ArchOp := (PositivityTheory.ThKF.A.archOp)
  have h_Weil6_ThKF_PureAct : PositivityTheory.ThKF.PureAct := (PositivityTheory.ThKF.pureAct)
  have h_Weil6_ThKEst_Level : PositivityTheory.ThKEst.Level := (PositivityTheory.ThKEst.level)
  have h_Weil6_ThKEnd_MatchStab : PositivityTheory.ThKEnd.MatchStab := (PositivityTheory.ThKEnd.Grp.matchStab_of h_Weil6_ThKF_ArchOp h_Weil6_ThKF_PureAct h_Weil6_ThKEst_Level h_Weil6_ThKCT_SoStab)
  have h_Weil6_ThKF_CartanMove : PositivityTheory.ThKF.CartanMove := (PositivityTheory.ThKF.cartanMove_of h_Weil6_ThKF_ArchOp)
  have h_Weil6_ThKF_CartanConj : PositivityTheory.ThKF.CartanConj := (PositivityTheory.ThKF.cartan_conjugacy_holds)
  have h_Weil6_ThKEst_IInv : PositivityTheory.ThKEst.IInv := (PositivityTheory.ThKEst.iInv_of h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEnd_SigRe : PositivityTheory.ThKEnd.SigRe := (PositivityTheory.ThKEnd.Grp.sigRe_of h_Weil6_ThKF_ArchOp h_Weil6_ThKF_CartanMove h_Weil6_ThKF_CartanConj h_Weil6_ThKEst_IInv h_Weil6_ThKCT_SoStab)
  have h_Weil6_ThKEnd_TowerA2 : PositivityTheory.ThKEnd.TowerCodimensionTwo := (PositivityTheory.ThKG.Tow.towerCodimensionTwo_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_Weil6_ThKCT_UnipEx : PositivityTheory.ThKCT.UnipEx := (PositivityTheory.ThKCT.unipEx_of)
  have h_Weil6_ThKCT_Low : PositivityTheory.ThKCT.Low := (PositivityTheory.ThKCT.low_of)
  have h_Weil6_ThKG_Tow_PairEx : PositivityTheory.ThKG.Tow.PairEx := (PositivityTheory.ThKG.Tow.pairEx_of PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_Weil6_ThKEst_TriplePair : PositivityTheory.ThKEst.TriplePair := (PositivityTheory.ThKEst.Sq.triplePair_holds)
  have h_GlobalTheory_ThK_EvZero : GlobalTheory.ThK.EvZero := PositivityTheory.ThKF0.evZero
  have h_Weil6_ThKG_MixW : PositivityTheory.ThKG.MixW := (PositivityTheory.Mix.mixW_closed)
  have h_Weil6_ThKG_MixX : PositivityTheory.ThKG.MixX := (PositivityTheory.Mix.mixX_closed)
  have h_Weil6_Mix_AdelSt : PositivityTheory.Mix.AdelSt := (PositivityTheory.Mix.adelic_estimates_holds)
  have h_GlobalTheory_ThK_EvCone : GlobalTheory.ThK.EvCone := (PositivityTheory.ThKF0.evCone_of_adel h_Weil6_Mix_AdelSt)
  have h_GlobalTheory_ThK_StabEx : GlobalTheory.ThK.StabEx := (PositivityTheory.ThKG.Tow.stabEx)
  have h_Weil6_ThKG_Tow_PlaneHerm : PositivityTheory.ThKG.Tow.PlaneHerm := (PositivityTheory.ThKG.Tow.planeHerm)
  have h_Weil6_ThKEst_GrpTop : PositivityTheory.ThKEst.GrpTop := (PositivityTheory.ThKEst.grpTop_of)
  have h_Weil6_ThKEst_EpsOf : PositivityTheory.ThKEst.EpsOf := (PositivityTheory.ThKEst.epsOf_of)
  have h_GlobalTheory_ThK_WeilConv : GlobalTheory.ThK.WeilConv := (PositivityTheory.ThKEst.weilConv hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEst_DomWeilU : PositivityTheory.ThKEst.DomWeilU := (PositivityTheory.ThKEst.domWeilU hSiegelSet)
  have h_Weil6_ThKEst_DomWeil : PositivityTheory.ThKEst.DomWeil := (PositivityTheory.ThKClose.domWeil_of h_Weil6_ThKEst_DomWeilU)
  have h_Weil6_ThKEst_SoSemiU : PositivityTheory.ThKEst.SoSemiU := (PositivityTheory.ThKEst.soSemiU hSiegelSet)
  have h_Weil6_ThKEst_SoSemi : PositivityTheory.ThKEst.SoSemi := (PositivityTheory.ThKClose.soSemi_of h_Weil6_ThKEst_SoSemiU)
  have h_GlobalTheory_ThK_SoDecay : GlobalTheory.ThK.SoDecay := (PositivityTheory.ThKEst.soDecay hSiegelSet)
  have h_Weil6_ThKEst_FinVolU : PositivityTheory.ThKEst.FinVolU := (PositivityTheory.ThKEst.finVolU)
  have h_Weil6_ThKEst_SoFin : PositivityTheory.ThKEst.SoFin := (PositivityTheory.ThKEst.soFin_of)
  have h_Weil6_ThKCT_Ext : PositivityTheory.ThKCT.Ext := ⟨h_Weil6_ThKG_MixW, h_Weil6_ThKG_MixX, h_GlobalTheory_ThK_ThetaBasic, h_GlobalTheory_ThK_EvZero, h_GlobalTheory_ThK_EvCone, h_GlobalTheory_ThK_StabEx, h_Weil6_ThKG_Tow_PairEx, h_Weil6_ThKG_Tow_PlaneHerm, h_Weil6_ThKEst_GrpTop, h_Weil6_ThKEst_EpsOf, h_Weil6_ThKEst_TriplePair, h_GlobalTheory_ThK_WeilConv, h_Weil6_ThKEst_DomWeil, h_Weil6_ThKEst_SoSemi, h_GlobalTheory_ThK_SoDecay, h_Weil6_ThKEst_FinVolU, h_Weil6_ThKEst_SoFin⟩
  have h_Weil6_ThKG_CTKernel : PositivityTheory.ThKG.CTKernel := (PositivityTheory.ThKCT.Ext.kernel h_Weil6_ThKCT_Ext)
  have h_Weil6_ThKCT_CTFub : PositivityTheory.ThKCT.CTFub := (PositivityTheory.ThKCT.ctFub_of h_Weil6_ThKCT_UnipEx h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKCT_Witt : PositivityTheory.ThKCT.Witt := (PositivityTheory.ThKCT.witt_of)
  have h_Weil6_ThKCT_GenAniso : PositivityTheory.ThKCT.GenAniso := (PositivityTheory.ThKCT.genAniso_of h_Weil6_ThKG_CTKernel h_Weil6_ThKCT_CTFub h_Weil6_ThKG_MixW h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKCT_Witt h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKCT_Unfold : PositivityTheory.ThKCT.Unfold := (PositivityTheory.ThKCT.unfold_of)
  have h_Weil6_ThKCT_StabDec : PositivityTheory.ThKCT.StabDec := (PositivityTheory.ThKCT.stabDec_of)
  have h_Weil6_ThKCT_EvAdm : PositivityTheory.ThKCT.EvAdm := (PositivityTheory.ThKCT.evAdm_of)
  have h_Weil6_ThKCT_ThetaExp : PositivityTheory.ThKCT.ThetaExp := (PositivityTheory.ThKCT.thetaExp)
  have h_Weil6_ThKCT_EvUniq : PositivityTheory.ThKCT.EvUniq := (PositivityTheory.ThKCT.evUniq_of h_Weil6_ThKCT_ThetaExp)
  have h_Weil6_ThKCT_MixAB : PositivityTheory.ThKCT.MixAB := (PositivityTheory.ThKCT.Ker.mixAB_of h_Weil6_ThKG_MixW h_Weil6_ThKG_MixX h_GlobalTheory_ThK_EvZero h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKCT_ThetaExp h_Weil6_ThKCT_EvUniq)
  have h_Weil6_ThKCT_Slice : PositivityTheory.ThKCT.Slice := (PositivityTheory.ThKCT.slice_of)
  have h_Weil6_ThKCT_SchInt : PositivityTheory.ThKCT.SchInt := (PositivityTheory.ThKCT.schInt)
  have h_Weil6_ThKCT_TateAbs : PositivityTheory.ThKCT.TateAbs := (PositivityTheory.ThKCT.tateAbs)
  have h_Weil6_ThKCT_LineInt : PositivityTheory.ThKCT.LineInt := (PositivityTheory.ThKCT.lineInt_of h_Weil6_ThKCT_Slice h_Weil6_ThKCT_SchInt h_Weil6_ThKCT_TateAbs)
  have h_Weil6_ThKCT_SoEv : PositivityTheory.ThKCT.SoEv := (PositivityTheory.ThKCT.soEv_of' h_Weil6_ThKCT_Low)
  have h_Weil6_ThKCT_ConeB : PositivityTheory.ThKCT.ConeB := (PositivityTheory.ThKCT.coneB_of h_Weil6_ThKCT_Unfold h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_StabDec h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_MixAB h_Weil6_ThKCT_LineInt h_Weil6_ThKEst_SoSemi h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_SoFin h_Weil6_ThKCT_SoStab h_Weil6_ThKCT_SoEv)
  have h_Weil6_ThKCT_TwoExp : PositivityTheory.ThKCT.TwoExp := (PositivityTheory.ThKCT.Ker.twoExp_of h_Weil6_ThKCT_ThetaExp)
  have h_Weil6_ThKCT_SoZeroA_ : PositivityTheory.ThKCT.SoZeroA' := (PositivityTheory.ThKCT.soZeroA'_of' h_Weil6_ThKG_MixX h_Weil6_ThKCT_ThetaExp h_Weil6_ThKCT_EvUniq)
  have h_Weil6_ThKCT_GenSmall : PositivityTheory.ThKCT.GenSmall := (PositivityTheory.ThKCT.genSmall_of h_Weil6_ThKG_CTKernel h_Weil6_ThKCT_CTFub h_Weil6_ThKCT_ConeB h_Weil6_ThKCT_TwoExp h_Weil6_ThKCT_MixAB h_Weil6_ThKG_MixW h_GlobalTheory_ThK_EvCone h_Weil6_ThKCT_Witt h_Weil6_ThKCT_StabDec h_Weil6_ThKCT_UnipEx h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_GlobalTheory_ThK_SoDecay h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_SoFin h_Weil6_ThKCT_SoStab h_Weil6_ThKCT_SoZeroA_ h_Weil6_ThKCT_SoEv)
  have h_Weil6_ThKCT_KFinData : PositivityTheory.ThKCT.KFinData := PositivityTheory.ThKCT.kFinData_of h_GlobalTheory_ThK_StabEx
  have h_Weil6_ThKCT_IwaEx : PositivityTheory.ThKCT.IwaEx := (PositivityTheory.ThKCT.iwaEx_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKEnd_Comp_SmallAny : PositivityTheory.ThKEnd.Comp.SmallAny := (PositivityTheory.ThKEnd.Comp.smallAny_of h_Weil6_ThKCT_GenSmall h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone)
  have h_Weil6_ThKF_Unimod : PositivityTheory.ThKF.Unimod := (PositivityTheory.ThKF.unimodularity_holds)
  have h_Weil6_ThKEst_DomSoU : PositivityTheory.ThKEst.DomSoU := (PositivityTheory.ThKEst.domSoU hSiegelSet)
  have h_Weil6_ThKEnd_Comp_SoLower : PositivityTheory.ThKEnd.Comp.SoLower := PositivityTheory.ThKEnd.Comp.SoL.soLower_of h_Weil6_ThKG_MixW
  have h_Weil6_ThKEnd_Comp_SoMove : PositivityTheory.ThKEnd.Comp.SoMove := (PositivityTheory.ThKEnd.Comp.soMove_of h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_Unimod h_Weil6_ThKEst_DomSoU h_Weil6_ThKEst_SoFin h_Weil6_ThKEst_TriplePair h_Weil6_ThKEnd_Comp_SoLower)
  have h_GlobalTheory_RealLift_LieFirst : GlobalTheory.RealLift.LieFirst := PositivityTheory.RL.lieFirst h_LieSecond
  have h_GlobalTheory_ThK_KReal : GlobalTheory.ThK.KReal := PositivityTheory.KRealA.kReal_of_lie h_LieSecond h_GlobalTheory_RealLift_LieFirst
  have h_Weil6_ThK_FinRam : PositivityTheory.ThK.FinRam := (hFinRam)
  have h_Weil6_ThK_FinSplit : PositivityTheory.ThK.FinSplit := (hFinSplit)
  have h_Weil6_ThK_FinInert : PositivityTheory.ThK.FinInert := (hFinInert)
  have h_GlobalTheory_ThK_KFin : GlobalTheory.ThK.KFin := (PositivityTheory.ThK.kFin_of h_Weil6_ThK_FinRam h_Weil6_ThK_FinSplit h_Weil6_ThK_FinInert)
  have h_Weil6_KCo_DictX : PositivityTheory.KCo.DictX := (PositivityTheory.ThKG.StdDict.dictX)
  have h_Weil6_KCo_SecSt : PositivityTheory.KCo.SecSt := (PositivityTheory.KCo.section_statement)
  have h_Weil6_KCo_DictSt : PositivityTheory.KCo.DictSt := (PositivityTheory.KCo.dictSt_of h_Weil6_KCo_DictX h_Weil6_KCo_SecSt)
  have h_GlobalTheory_ThK_KCoinv : GlobalTheory.ThK.KCoinv := (hKCo h_Weil6_KCo_DictSt)
  have h_GlobalTheory_ThK_MatchEx : GlobalTheory.ThK.MatchEx := (PositivityTheory.ThKClose.matchEx_of h_GlobalTheory_ThK_KCoinv)
  have h_Weil6_ThKEnd_Comp_PolStab : PositivityTheory.ThKEnd.Comp.PolStab := (PositivityTheory.ThKEnd.Comp.polStab_of h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_MatchEx h_Weil6_ThKEnd_MatchStab)
  have h_Weil6_ThKG_PolDense : PositivityTheory.ThKG.PolDense := (GlobalTheory.ThK.Dbl.polDense)
  have h_GlobalTheory_RealLift_FrameEx : GlobalTheory.RealLift.FrameEx := (PositivityTheory.RL.frameEx)
  have h_GlobalTheory_RealLift_DerEx : GlobalTheory.RealLift.DerEx := (PositivityTheory.RL.derEx)
  have h_GlobalTheory_RealLift_FockEx : GlobalTheory.RealLift.FockEx := (PositivityTheory.RL.fockEx h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_LineEx : GlobalTheory.RealLift.LineEx := (PositivityTheory.RL.lineEx)
  have h_GlobalTheory_RealLift_ActsLaws : GlobalTheory.RealLift.ActsLaws := (PositivityTheory.RL.actsLaws)
  have h_GlobalTheory_RealLift_VacLine : GlobalTheory.RealLift.VacLine := (PositivityTheory.RL.vacLine h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_PolRange : GlobalTheory.RealLift.PolRange := (PositivityTheory.ThKEnd.Comp.PR.polRange_of h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine)
  have h_Weil6_ThKEnd_Comp_RealVanish : PositivityTheory.ThKEnd.Comp.RealVanish := (PositivityTheory.ThKEnd.Comp.realVanish_of h_Weil6_ThKF_ArchOp h_Weil6_ThKG_PolDense h_GlobalTheory_RealLift_FrameEx h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_LineEx h_GlobalTheory_RealLift_PolRange h_GlobalTheory_RealLift_LieFirst)
  have h_Weil6_ThKEnd_Comp_IZero : PositivityTheory.ThKEnd.Comp.IZero := (PositivityTheory.ThKEnd.Comp.iZero_of h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_Unimod h_Weil6_ThKEst_DomWeil h_Weil6_ThKEst_DomSoU h_Weil6_ThKEst_SoFin h_Weil6_ThKEnd_Comp_RealVanish)
  have h_Weil6_ThKEnd_AlphaZero : PositivityTheory.ThKEnd.AlphaZero := (PositivityTheory.ThKEnd.Comp.alphaZero_of h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_Low h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_GenAniso h_Weil6_ThKEnd_Comp_SmallAny h_Weil6_ThKEnd_Comp_SoMove h_Weil6_ThKEnd_Comp_PolStab h_Weil6_ThKEnd_Comp_IZero)
  have h_Weil6_ThKCT_ConeA : PositivityTheory.ThKCT.ConeA := (PositivityTheory.ThKCT.coneA_of h_Weil6_ThKCT_Unfold h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_StabDec h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_MixAB h_Weil6_ThKCT_LineInt h_Weil6_ThKEst_DomWeil)
  have h_Weil6_ThKCT_GenBig : PositivityTheory.ThKCT.GenBig := (PositivityTheory.ThKCT.genBig_of h_Weil6_ThKG_CTKernel h_Weil6_ThKCT_CTFub h_Weil6_ThKCT_ConeA h_Weil6_ThKG_MixW h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKCT_Witt h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKEnd_Comp_BigAny : PositivityTheory.ThKEnd.Comp.BigAny := (PositivityTheory.ThKEnd.Comp.bigAny_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone)
  have h_Weil6_ThKEnd_BetaZero : PositivityTheory.ThKEnd.BetaZero := (PositivityTheory.ThKEnd.Comp.betaZero_of h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_Low h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_GenAniso h_Weil6_ThKEnd_Comp_BigAny h_Weil6_ThKEnd_Comp_IZero)
  have h_GlobalTheory_ThK_ActsEx : GlobalTheory.ThK.ActsEx := (PositivityTheory.ThKF0.actsEx)
  have h_Weil6_ThKF_ArchUniq : PositivityTheory.ThKF.ArchUniq := (PositivityTheory.ThKF.A.archUniq)
  have h_Weil6_Mix_PureSt : PositivityTheory.Mix.PureSt := (PositivityTheory.Mix.pure_tensor_estimates_holds)
  have h_Weil6_ThKG_Loc_Bump_ArchDict : PositivityTheory.ThKG.Loc.Bump.ArchDict := (PositivityTheory.ThKG.Loc.Bump.archDict_of)
  have h_Weil6_ThKG_Loc_Bump_ArchHeis : PositivityTheory.ThKG.Loc.Bump.ArchHeis := (PositivityTheory.ThKG.Loc.Bump.archHeis_of)
  have h_Weil6_ThKG_Loc_Cone_ArchCone : PositivityTheory.ThKG.Loc.Cone.ArchCone := (PositivityTheory.ThKG.Loc.Bump.archCone_of h_Weil6_ThKG_Loc_Bump_ArchDict h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKG_Loc_Bump_ArchHeis h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_FrameEx h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_KFinData)
  have h_Weil6_ThKG_Loc_MeasEx : PositivityTheory.ThKG.Loc.MeasEx := (PositivityTheory.ThKG.Loc.Cone.coneFac_of h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone).1
  have h_Weil6_ThKEnd_Comp_ConeFacA2 : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation := (PositivityTheory.ThKG.Loc.Cone.coneFac_of h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone).2.1
  have h_Weil6_ThKEnd_Comp_ConePol : PositivityTheory.ThKEnd.Comp.ConePol := (PositivityTheory.ThKEnd.Comp.conePol_of h_Weil6_ThKG_Loc_MeasEx h_Weil6_ThKEnd_Comp_ConeFacA2)
  have h_Weil6_ThKEnd_AlphaLow : PositivityTheory.ThKEnd.AlphaLow := (PositivityTheory.ThKEnd.Comp.alphaLow_of h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKCT_UnipEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_EvCone h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKCT_KFinData h_Weil6_ThKCT_GenBig h_Weil6_ThKEnd_Comp_SmallAny h_Weil6_ThKEnd_Comp_SoMove h_Weil6_ThKEnd_Comp_PolStab h_Weil6_ThKEnd_Comp_ConePol)
  have h_GlobalTheory_ThK_KDecay : GlobalTheory.ThK.KDecay := (PositivityTheory.ThKEst.kDecay hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEnd_Two_SigMod : PositivityTheory.ThKEnd.Two.SigMod := (PositivityTheory.ThKEnd.Two.sigMod_of h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KDecay)
  have h_GlobalTheory_ThK_SplitEx : GlobalTheory.ThK.SplitEx := (PositivityTheory.ThKCT.splitEx_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenSmall h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_Low h_Weil6_ThKEst_TriplePair)
  have h_Weil6_ThKG_Tow_PlaneSkew : PositivityTheory.ThKG.Tow.PlaneSkew := (PositivityTheory.ThKG.Tow.planeSkew)
  have h_Weil6_ThKEnd_Two_SigSplit : PositivityTheory.ThKEnd.Two.SigSplit := (PositivityTheory.ThKEnd.Two.sigSplit_of h_GlobalTheory_ThK_SplitEx h_Weil6_ThKG_Tow_PlaneSkew h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_SigRe)
  have h_Weil6_ThKEnd_TwoStep : PositivityTheory.ThKEnd.TwoStep := (PositivityTheory.ThKEnd.Two.twoStep_of' h_Weil6_ThKEnd_Two_SigMod h_Weil6_ThKEnd_Two_SigSplit h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_IAut)
  have h_Weil6_ThKEnd_Cusp_LocThree : PositivityTheory.ThKEnd.Cusp.LocThree := (PositivityTheory.ThKEnd.Cusp.locThree)
  have h_Weil6_ThKEnd_Cusp_Places : PositivityTheory.ThKEnd.Cusp.Places := (PositivityTheory.ThKEnd.Cusp.places)
  have h_Weil6_ThKEnd_Cusp_KeyThree : PositivityTheory.ThKEnd.Cusp.KeyThree := (PositivityTheory.ThKEnd.Cusp.Key.keyThree_of_locThree h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_KDecay h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_Cusp_LocThree h_Weil6_ThKEnd_Cusp_Places)
  have h_Weil6_ThKEnd_Cusp_LocSupp : PositivityTheory.ThKEnd.Cusp.LocSupp := (PositivityTheory.ThKEnd.Cusp.locSupp)
  have h_Weil6_ThKEnd_Cusp_LocTwo : PositivityTheory.ThKEnd.Cusp.LocTwo := (PositivityTheory.ThKEnd.Cusp.locTwo_of h_Weil6_ThKEnd_Cusp_LocSupp)
  have h_Weil6_ThKEnd_Cusp_KeyTwo : PositivityTheory.ThKEnd.Cusp.KeyTwo := (PositivityTheory.ThKEnd.Cusp.Key.keyTwo_of_locTwo_vacBar h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_KDecay h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_Cusp_LocTwo h_Weil6_ThKEnd_Cusp_VacBar h_Weil6_ThKEnd_Cusp_Places)
  have h_Weil6_ThKEnd_CuspOfLine : PositivityTheory.ThKEnd.CuspOfLine := (PositivityTheory.ThKEnd.Cusp.cuspOfLine_of_keys h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KDecay h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_Cusp_KeyThree h_Weil6_ThKEnd_Cusp_KeyTwo)
  have h_Weil6_ThKEst_SiegelAll : PositivityTheory.ThKEst.SiegelAll := (PositivityTheory.ThKEst.siegelAll_of hSiegelSet)
  have h_GlobalTheory_ThK_Dbl_PolSch : GlobalTheory.ThK.Dbl.PolSch := (GlobalTheory.ThK.Dbl.polSch)
  have h_GlobalTheory_ThK_Dbl_GoodNe : GlobalTheory.ThK.Dbl.GoodNe := (GlobalTheory.ThK.Dbl.goodNe)
  have h_Weil6_ThKEnd_Orth_SigRapid : PositivityTheory.ThKEnd.Orth.SigRapid := (PositivityTheory.ThKEst.sigRapid hSiegelSet h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie)
  have h_GlobalTheory_ThK_Dbl_ConstOfGood : GlobalTheory.ThK.Dbl.ConstOfGood := (PositivityTheory.SA.constOfGood GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds)
  have h_GlobalTheory_ThK_Dbl_LocDist : GlobalTheory.ThK.Dbl.LocDist := (GlobalTheory.ThK.Dbl.locDist)
  have h_Weil6_ThKEnd_Orth_SigThConst : PositivityTheory.ThKEnd.Orth.SigThConst := (PositivityTheory.ThKEnd.Orth.sigThConst_fin h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_KDecay h_Weil6_ThKEst_SoFin h_Weil6_ThKF_Unimod h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_GoodNe h_GlobalTheory_ThK_Dbl_ConstOfGood h_GlobalTheory_ThK_Dbl_LocDist h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_KCoinv)
  have h_Weil6_ThKEnd_OrthIso : PositivityTheory.ThKEnd.OrthIso := (PositivityTheory.ThKEnd.Orth.orthIso_fin h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKG_Tow_PlaneHerm h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_SoDecay h_Weil6_ThKEst_DomSoU h_Weil6_ThKEst_SoFin h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_GoodNe h_Weil6_ThKEnd_Orth_SigRapid h_Weil6_ThKEnd_Orth_SigThConst)
  have h_GlobalTheory_ThK_Dbl_FinLevel : GlobalTheory.ThK.Dbl.FinLevel := (GlobalTheory.ThK.Dbl.finLevel)
  have h_GlobalTheory_ThK_Dbl_Stab2Cpt : GlobalTheory.ThK.Dbl.Stab2Cpt := (GlobalTheory.ThK.Dbl.stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWAniso : GlobalTheory.ThK.Dbl.SWAniso := (GlobalTheory.ThK.Dbl.siegelWeilAniso_of h_SWStd h_FrameConj h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt).1
  have h_GlobalTheory_ThK_Dbl_EisContinues : GlobalTheory.ThK.Dbl.EisContinues := GlobalTheory.ThK.Dbl.eisContinues_of h_EisBL h_FrameConj
  have h_GlobalTheory_ThK_Dbl_BoxSec : GlobalTheory.ThK.Dbl.BoxSec := (GlobalTheory.ThK.Dbl.boxSec_of h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWFull : GlobalTheory.ThK.Dbl.SWFull := (GlobalTheory.ThK.Dbl.swFull_of h_GlobalTheory_ThK_Dbl_SWAniso h_GlobalTheory_ThK_Dbl_EisContinues h_GlobalTheory_ThK_Dbl_BoxSec)
  have h_GlobalTheory_ThK_Dbl_DblW : GlobalTheory.ThK.Dbl.DblW := (GlobalTheory.ThK.Dbl.dblW)
  have h_GlobalTheory_ThK_Dbl_HgtEx : GlobalTheory.ThK.Dbl.HgtEx := GlobalTheory.ThK.Dbl.hgtEx_of h_GlobalTheory_ThK_Dbl_Stab2Cpt
  have h_GlobalTheory_ThK_Dbl_HgtInt : GlobalTheory.ThK.Dbl.HgtInt := GlobalTheory.ThK.Dbl.hgtInt_of h_GlobalTheory_ThK_Dbl_Stab2Cpt
  have h_GlobalTheory_ThK_Dbl_OffOpen : GlobalTheory.ThK.Dbl.OffOpen := (GlobalTheory.ThK.Dbl.offOpen)
  have h_GlobalTheory_ThK_Dbl_HtEmb : GlobalTheory.ThK.Dbl.HtEmb := (GlobalTheory.ThK.Dbl.htEmb)
  have h_Weil6_ThKEnd_Grp_UnipUGood : PositivityTheory.ThKEnd.Grp.UnipUGood := (PositivityTheory.ThKEnd.Grp.unipUGood)
  have h_Weil6_ThKEnd_Grp_UnipLine : PositivityTheory.ThKEnd.Grp.UnipLine := (PositivityTheory.ThKEnd.Grp.unipLine)
  have h_GlobalTheory_ThK_Dbl_CptAll : GlobalTheory.ThK.Dbl.CptAll := (GlobalTheory.ThK.Dbl.cptAll_of h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_FinVolU h_Weil6_ThKF_Unimod)
  have h_GlobalTheory_ThK_Dbl_LeviEx : GlobalTheory.ThK.Dbl.LeviEx := (GlobalTheory.ThK.Dbl.leviEx)
  have h_GlobalTheory_ThK_Dbl_OrthIn : GlobalTheory.ThK.Dbl.OrthIn := ⟨h_GlobalTheory_ThK_Dbl_SWFull, h_GlobalTheory_ThK_Dbl_BoxSec, h_GlobalTheory_ThK_Dbl_DblW, h_GlobalTheory_ThK_Dbl_HgtEx, h_GlobalTheory_ThK_Dbl_HgtInt, h_GlobalTheory_ThK_Dbl_Stab2Cpt, h_GlobalTheory_ThK_Dbl_EisContinues, h_GlobalTheory_ThK_Dbl_OffOpen, h_GlobalTheory_ThK_Dbl_HtEmb, h_Weil6_ThKEnd_Grp_UnipUGood, h_Weil6_ThKEnd_Grp_UnipLine, h_GlobalTheory_ThK_Dbl_CptAll, h_Weil6_ThKEst_GrpTop, h_Weil6_ThKEst_EpsOf, h_Weil6_ThKEst_FinVolU, h_GlobalTheory_ThK_ThetaBasic, h_Weil6_ThKF_ArchOp, h_Weil6_ThKF_CartanConj, h_Weil6_ThKF_CartanMove, h_GlobalTheory_ThK_Dbl_LeviEx⟩
  have h_GlobalTheory_ThK_Dbl_LInt2 : GlobalTheory.ThK.Dbl.LInt2 := GlobalTheory.ThK.Dbl.lInt2
  have h_GlobalTheory_ThK_Dbl_SWAnisoX : GlobalTheory.ThK.Dbl.SWAnisoX := (GlobalTheory.ThK.Dbl.siegelWeilAniso_of h_SWStd h_FrameConj h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt).2
  have h_GlobalTheory_ThK_Dbl_BoxSecX : GlobalTheory.ThK.Dbl.BoxSecX := (GlobalTheory.ThK.Dbl.boxSecX_of h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWFullX : GlobalTheory.ThK.Dbl.SWFullX := (GlobalTheory.ThK.Dbl.swFullX_of h_GlobalTheory_ThK_Dbl_SWAnisoX h_GlobalTheory_ThK_Dbl_EisContinues h_GlobalTheory_ThK_Dbl_BoxSecX)
  have h_GlobalTheory_ThK_Dbl_DblX : GlobalTheory.ThK.Dbl.DblX := (GlobalTheory.ThK.Dbl.dblX)
  have h_GlobalTheory_ThK_Dbl_NormZeta : GlobalTheory.ThK.Dbl.NormZeta := (GlobalTheory.ThK.Dbl.normZeta_of h_GlobalTheory_ThK_Dbl_SWFullX h_GlobalTheory_ThK_Dbl_BoxSecX h_GlobalTheory_ThK_Dbl_DblX h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_HgtInt h_GlobalTheory_ThK_Dbl_Stab2Cpt h_GlobalTheory_ThK_Dbl_CptAll h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_PolSch)
  have h_GlobalTheory_ThK_Dbl_EulerProd : GlobalTheory.ThK.Dbl.EulerProd := (GlobalTheory.ThK.Dbl.eulerProd)
  have h_GlobalTheory_ThK_Dbl_LocMeas : GlobalTheory.ThK.Dbl.LocMeas := (GlobalTheory.ThK.Dbl.locMeas)
  have h_GlobalTheory_ThK_Dbl_LocUnrInert : GlobalTheory.ThK.Dbl.LocUnrInert := GlobalTheory.ThK.Dbl.locUnrInert
  have h_GlobalTheory_ThK_Dbl_LocUnr : GlobalTheory.ThK.Dbl.LocUnr := (GlobalTheory.ThK.Dbl.locUnr_of h_GlobalTheory_ThK_Dbl_LocUnrSplit h_GlobalTheory_ThK_Dbl_LocUnrInert)
  have h_GlobalTheory_ThK_Dbl_RealInv : GlobalTheory.ThK.Dbl.RealInv := (GlobalTheory.ThK.Dbl.realInv_of h_Weil6_ThKF_ArchOp)
  have h_GlobalTheory_ThK_Dbl_DProd : GlobalTheory.ThK.Dbl.DProd := (GlobalTheory.ThK.Dbl.dProd)
  have h_GlobalTheory_ThK_Dbl_NonZeroBot : GlobalTheory.ThK.Dbl.NonZeroBot := (GlobalTheory.ThK.Dbl.nonZeroBottom_of_doubling_integral h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_Dbl_LInt2 h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_NormZeta h_GlobalTheory_ThK_Dbl_EulerProd h_GlobalTheory_ThK_Dbl_LocMeas h_GlobalTheory_ThK_Dbl_LocUnr h_GlobalTheory_ThK_Dbl_BadFactor h_GlobalTheory_ThK_Dbl_RealInv h_GlobalTheory_ThK_Dbl_DProd)
  have h_GlobalTheory_ThK_TowerA : GlobalTheory.ThK.TowerA := (PositivityTheory.ThKG.Tow.towerA_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_TowerB : GlobalTheory.ThK.TowerB := (PositivityTheory.ThKG.Tow.towerB_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_CTBigZero : GlobalTheory.ThK.CTBigZero := (PositivityTheory.ThKCT.ctBigZero_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone h_Weil6_ThKCT_UnipEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTSmallZero : GlobalTheory.ThK.CTSmallZero := (PositivityTheory.ThKCT.ctSmallZero_of h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_Dbl_SchToPol : GlobalTheory.ThK.Dbl.SchToPol := (GlobalTheory.ThK.Dbl.schToPol_of h_GlobalTheory_ThK_WeilConv)
  have h_GlobalTheory_ThK_Dbl_ToSo : GlobalTheory.ThK.Dbl.ToSo := (GlobalTheory.ThK.Dbl.toSo_of h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_KCoinv h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_CptAll)
  have h_GlobalTheory_ThK_NonZeroAn : GlobalTheory.ThK.NonZeroAn := (GlobalTheory.ThK.Dbl.nonZeroAn_of h_GlobalTheory_ThK_Dbl_NonZeroBot h_GlobalTheory_ThK_TowerA h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_CTBigZero h_GlobalTheory_ThK_CTSmallZero h_GlobalTheory_ThK_Dbl_SchToPol h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_LeviEx h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_Dbl_ToSo)
  have h_Weil6_ThKEnd_OrthAn : PositivityTheory.ThKEnd.OrthAn := (GlobalTheory.ThK.Dbl.orthAn_of h_GlobalTheory_ThK_Dbl_OrthIn h_Weil6_ThKEnd_Orth_SigRapid h_Weil6_ThKEnd_Orth_SigThConst h_GlobalTheory_ThK_NonZeroAn h_GlobalTheory_ThK_TowerA h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_CTBigZero h_GlobalTheory_ThK_CTSmallZero)
  have h_Weil6_ThKEst_SqAll : PositivityTheory.ThKEst.SqAll := (PositivityTheory.ThKEst.sqAll)
  have h_Weil6_ThKEst_SqSo : PositivityTheory.ThKEst.SqSo := (PositivityTheory.ThKEst.sqSo)
  have h_Weil6_ThKEst_LatCpt : PositivityTheory.ThKEst.LatCpt := (PositivityTheory.ThKEst.latCpt_of)
  have h_Weil6_ThKEst_LatTor : PositivityTheory.ThKEst.LatTor := (PositivityTheory.ThKEst.latTor)
  have h_Weil6_ThKEst_LatFull : PositivityTheory.ThKEst.LatFull := (PositivityTheory.ThKEst.latFull)
  have h_GlobalTheory_ThK_SqInt : GlobalTheory.ThK.SqInt := (PositivityTheory.ThKEst.Sq.sqInt_of_leaves h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_SqAll h_Weil6_ThKEst_SqSo h_Weil6_ThKEst_SoFin h_Weil6_ThKEst_LatCpt h_Weil6_ThKEst_LatTor h_Weil6_ThKEst_LatFull)
  have h_Weil6_ThKEnd_PerpZero : PositivityTheory.ThKEnd.PerpZero := (PositivityTheory.ThKEnd.Grp.perpZero_of h_GlobalTheory_ThK_SqInt h_Weil6_ThKEnd_IAut)
  have h_Weil6_ThKEnd_Leaves : PositivityTheory.ThKEnd.Leaves := ⟨h_Weil6_ThKEnd_Iwa, h_Weil6_ThKEnd_CTBasic, h_Weil6_ThKEnd_LineMove, h_Weil6_ThKEnd_IAut, h_Weil6_ThKEnd_MatchStab, h_Weil6_ThKEnd_SigRe, h_Weil6_ThKEnd_TowerA2, h_Weil6_ThKEnd_AlphaZero, h_Weil6_ThKEnd_BetaZero, h_Weil6_ThKEnd_AlphaLow, h_Weil6_ThKEnd_TwoStep, h_Weil6_ThKEnd_CuspOfLine, h_Weil6_ThKEnd_OrthIso, h_Weil6_ThKEnd_OrthAn, h_Weil6_ThKEnd_PerpZero⟩
  have h_GlobalTheory_ThK_EndA : GlobalTheory.ThK.EndA := (PositivityTheory.ThKEnd.endA_of h_Weil6_ThKEnd_Leaves h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_MatchEx)
  have h_GlobalTheory_ThK_EndB : GlobalTheory.ThK.EndB := (PositivityTheory.ThKEnd.endB_of h_Weil6_ThKEnd_Leaves h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_MatchEx)
  exact ⟨h_GlobalTheory_ThK_EndA, h_GlobalTheory_ThK_EndB⟩
end

theorem PositivityTheory.Sph.Tr.closeSph
    (hKCo : PositivityTheory.KCo.DictSt → GlobalTheory.ThK.KCoinv)
    (hSo : GlobalTheory.ThK.KFin → PositivityTheory.ThKF.SoCoinv)
    (hH1Ram : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne)
    (hFinRam : PositivityTheory.ThK.FinRam)
    (hFinSplit : PositivityTheory.ThK.FinSplit)
    (hSph : PositivityTheory.Sph.SphTri)
    (hFinInert : PositivityTheory.ThK.FinInert)
    (h_GlobalTheory_RealLift_LieSecond : GlobalTheory.RealLift.LieSecond)
    (h_Weil6_ThKF_ArchLie : PositivityTheory.ThKF.ArchLie)
    (h_GlobalTheory_ThK_KReal : GlobalTheory.ThK.KReal)
    (hSiegelSet : GlobalTheory.Published.SiegelSetUnitary)
    (h_GlobalTheory_ThK_Dbl_EisBL : GlobalTheory.ThK.Dbl.EisBL)
    (h_GlobalTheory_ThK_Dbl_SiegelWeilStd : GlobalTheory.ThK.Dbl.SiegelWeilStd)
    (h_Weil6_ThKG_Tow_WeilEx : PositivityTheory.ThKG.Tow.WeilEx) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching := by
  have h_GlobalTheory_ThK_EvZero : GlobalTheory.ThK.EvZero := (PositivityTheory.ThKF0.evaluation_at_zero_and_cone).1
  have h_GlobalTheory_ThK_EvCone : GlobalTheory.ThK.EvCone := (PositivityTheory.ThKF0.evaluation_at_zero_and_cone).2
  have h_GlobalTheory_ThK_StabEx : GlobalTheory.ThK.StabEx := (PositivityTheory.ThKG.Tow.stabEx)
  have h_GlobalTheory_ThK_TowerA : GlobalTheory.ThK.TowerA := (PositivityTheory.ThKG.Tow.towerA_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_TowerB : GlobalTheory.ThK.TowerB := (PositivityTheory.ThKG.Tow.towerB_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_FacNe : GlobalTheory.ThK.FacNe := (PositivityTheory.ThK.Close.facNe)
  have h_Weil6_KCo_DictX : PositivityTheory.KCo.DictX := (PositivityTheory.ThKG.StdDict.dictX)
  have h_Weil6_KCo_SecSt : PositivityTheory.KCo.SecSt := (PositivityTheory.KCo.section_statement)
  have h_Weil6_KCo_DictSt : PositivityTheory.KCo.DictSt := (PositivityTheory.KCo.dictSt_of h_Weil6_KCo_DictX h_Weil6_KCo_SecSt)
  have h_GlobalTheory_ThK_KCoinv : GlobalTheory.ThK.KCoinv := (hKCo h_Weil6_KCo_DictSt)
  have h_GlobalTheory_ThK_MatchEx : GlobalTheory.ThK.MatchEx := (PositivityTheory.ThKClose.matchEx_of h_GlobalTheory_ThK_KCoinv)
  have h_Weil6_ThKG_LeviEx : PositivityTheory.ThKG.LeviEx := (PositivityTheory.ThKG.Tow.leviEx)
  have h_Weil6_ThKG_PolDense : PositivityTheory.ThKG.PolDense := (GlobalTheory.ThK.Dbl.polDense)
  have h_GlobalTheory_ThK_ThetaBasic : GlobalTheory.ThK.ThetaBasic := (PositivityTheory.ThKF0.thetaBasic)
  have h_GlobalTheory_ThK_WeilConv : GlobalTheory.ThK.WeilConv := (PositivityTheory.ThKEst.weilConv hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_GlobalTheory_ThK_SoCont : GlobalTheory.ThK.SoCont := (PositivityTheory.ThKEst.soCont hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKG_MixW : PositivityTheory.ThKG.MixW := (PositivityTheory.Mix.mixW_closed)
  have h_Weil6_ThKG_MixX : PositivityTheory.ThKG.MixX := (PositivityTheory.Mix.mixX_closed)
  have h_Weil6_ThKG_Tow_PairEx : PositivityTheory.ThKG.Tow.PairEx := (PositivityTheory.ThKG.Tow.pairEx_of PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_Weil6_ThKG_Tow_PlaneHerm : PositivityTheory.ThKG.Tow.PlaneHerm := (PositivityTheory.ThKG.Tow.planeHerm)
  have h_Weil6_ThKEst_GrpTop : PositivityTheory.ThKEst.GrpTop := (PositivityTheory.ThKEst.grpTop_of)
  have h_Weil6_ThKEst_EpsOf : PositivityTheory.ThKEst.EpsOf := (PositivityTheory.ThKEst.epsOf_of)
  have h_Weil6_ThKEst_TriplePair : PositivityTheory.ThKEst.TriplePair := (PositivityTheory.ThKEst.Sq.triplePair_holds)
  have h_Weil6_ThKEst_DomWeilU : PositivityTheory.ThKEst.DomWeilU := (PositivityTheory.ThKEst.domWeilU hSiegelSet)
  have h_Weil6_ThKEst_DomWeil : PositivityTheory.ThKEst.DomWeil := (PositivityTheory.ThKClose.domWeil_of h_Weil6_ThKEst_DomWeilU)
  have h_Weil6_ThKEst_SoSemiU : PositivityTheory.ThKEst.SoSemiU := (PositivityTheory.ThKEst.soSemiU hSiegelSet)
  have h_Weil6_ThKEst_SoSemi : PositivityTheory.ThKEst.SoSemi := (PositivityTheory.ThKClose.soSemi_of h_Weil6_ThKEst_SoSemiU)
  have h_GlobalTheory_ThK_SoDecay : GlobalTheory.ThK.SoDecay := (PositivityTheory.ThKEst.soDecay hSiegelSet)
  have h_Weil6_ThKEst_FinVolU : PositivityTheory.ThKEst.FinVolU := (PositivityTheory.ThKEst.finVolU)
  have h_Weil6_ThKEst_SoFin : PositivityTheory.ThKEst.SoFin := (PositivityTheory.ThKEst.soFin_of)
  have h_Weil6_ThKCT_Ext : PositivityTheory.ThKCT.Ext := ⟨h_Weil6_ThKG_MixW, h_Weil6_ThKG_MixX, h_GlobalTheory_ThK_ThetaBasic, h_GlobalTheory_ThK_EvZero, h_GlobalTheory_ThK_EvCone, h_GlobalTheory_ThK_StabEx, h_Weil6_ThKG_Tow_PairEx, h_Weil6_ThKG_Tow_PlaneHerm, h_Weil6_ThKEst_GrpTop, h_Weil6_ThKEst_EpsOf, h_Weil6_ThKEst_TriplePair, h_GlobalTheory_ThK_WeilConv, h_Weil6_ThKEst_DomWeil, h_Weil6_ThKEst_SoSemi, h_GlobalTheory_ThK_SoDecay, h_Weil6_ThKEst_FinVolU, h_Weil6_ThKEst_SoFin⟩
  have h_GlobalTheory_ThK_SplitEx : GlobalTheory.ThK.SplitEx := (PositivityTheory.ThKCT.ct_all h_Weil6_ThKCT_Ext).2.1
  have h_Weil6_ThKCT_GenBig : PositivityTheory.ThKCT.GenBig := (PositivityTheory.ThKCT.Ext.genBig h_Weil6_ThKCT_Ext)
  have h_Weil6_ThKCT_GenAniso : PositivityTheory.ThKCT.GenAniso := (PositivityTheory.ThKCT.Ext.genAniso h_Weil6_ThKCT_Ext)
  have h_Weil6_ThKCT_KFinData : PositivityTheory.ThKCT.KFinData := (PositivityTheory.ThKCT.kFinData_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKCT_IwaEx : PositivityTheory.ThKCT.IwaEx := (PositivityTheory.ThKCT.iwaEx_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKCT_UnipEx : PositivityTheory.ThKCT.UnipEx := (PositivityTheory.ThKCT.unipEx_of)
  have h_GlobalTheory_ThK_CTBigZero : GlobalTheory.ThK.CTBigZero := (PositivityTheory.ThKCT.ctBigZero_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone h_Weil6_ThKCT_UnipEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTSmallZero : GlobalTheory.ThK.CTSmallZero := (PositivityTheory.ThKCT.ctSmallZero_of h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTBigCone : GlobalTheory.ThK.CTBigCone := (PositivityTheory.ThKCT.ctBigCone_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_KFinData h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_UnipEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTSmallCone : GlobalTheory.ThK.CTSmallCone := (PositivityTheory.ThKCT.ct_all h_Weil6_ThKCT_Ext).2.2.2.2.2
  have h_Weil6_ThKF_ILeft : PositivityTheory.ThKF.ILeft := (PositivityTheory.ThKF.iLeft h_GlobalTheory_ThK_ThetaBasic)
  have h_GlobalTheory_ThK_AnAll : GlobalTheory.ThK.AnAll := (PositivityTheory.ThKF.anAll_of h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_ILeft)
  have h_Weil6_ThKF_LocUPairEx : PositivityTheory.ThKF.LocUPairEx := (PositivityTheory.ThKH.Locpair.locUPairEx)
  have h_Weil6_ThKF_MaxFin : PositivityTheory.HoweDualityUnitaryAlt.MaxFinT := PositivityTheory.Sph.maxFinT_of hSph
  have h_Weil6_ThKF_ArchOp : PositivityTheory.ThKF.ArchOp := (PositivityTheory.ThKF.A.archOp)
  have h_Weil6_ThKF_ArchUniq : PositivityTheory.ThKF.ArchUniq := (PositivityTheory.ThKF.A.archUniq)
  have h_GlobalTheory_RealLift_DerEx : GlobalTheory.RealLift.DerEx := (PositivityTheory.RL.derEx)
  have h_GlobalTheory_RealLift_FockEx : GlobalTheory.RealLift.FockEx := (PositivityTheory.KRealA.i_fockex h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_ActsLaws : GlobalTheory.RealLift.ActsLaws := (PositivityTheory.KRealA.i_actslaws)
  have h_GlobalTheory_RealLift_VacLine : GlobalTheory.RealLift.VacLine := (PositivityTheory.KRealA.i_vacline h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_PolRange : GlobalTheory.RealLift.PolRange := (PositivityTheory.ThKEnd.Comp.PR.polRange_of h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine)
  have h_GlobalTheory_RealLift_LieFirst : GlobalTheory.RealLift.LieFirst := (PositivityTheory.RL.lieFirst h_GlobalTheory_RealLift_LieSecond)
  have h_Weil6_ThKR_JoinTri : PositivityTheory.ThKR.JoinTri := PositivityTheory.ThKR.Join.joinTri_of h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_PolRange h_GlobalTheory_RealLift_LieFirst h_GlobalTheory_RealLift_LieSecond
  have h_Weil6_ThKF_PolCount : PositivityTheory.ThKF.PolCount := (PositivityTheory.ThKF.polCount_of_derEx h_GlobalTheory_RealLift_DerEx)
  have h_Weil6_ThKF_CartanConj : PositivityTheory.ThKF.CartanConj := (PositivityTheory.ThKF.cartan_conjugacy_holds)
  have h_Weil6_ThKF_CartanMove : PositivityTheory.ThKF.CartanMove := (PositivityTheory.ThKF.cartanMove_of h_Weil6_ThKF_ArchOp)
  have h_GlobalTheory_ThK_PolRe : GlobalTheory.ThK.PolRe := (PositivityTheory.HoweDualityUnitaryAlt.polRe_of2T h_Weil6_ThKR_JoinTri h_Weil6_ThKF_MaxFin h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie h_Weil6_ThKF_ArchUniq h_Weil6_ThKF_PolCount h_Weil6_ThKF_CartanConj h_Weil6_ThKF_CartanMove h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_ILeft)
  have h_GlobalTheory_ThK_Dbl_LInt2 : GlobalTheory.ThK.Dbl.LInt2 := GlobalTheory.ThK.Dbl.lInt2
  have h_GlobalTheory_ThK_Dbl_HgtEx : GlobalTheory.ThK.Dbl.HgtEx := (GlobalTheory.ThK.Dbl.hgtEx)
  have h_GlobalTheory_ThK_Dbl_FrameConj : GlobalTheory.ThK.Dbl.FrameConj := (GlobalTheory.ThK.Dbl.frameConj)
  have h_GlobalTheory_ThK_Dbl_FinLevel : GlobalTheory.ThK.Dbl.FinLevel := (GlobalTheory.ThK.Dbl.finLevel)
  have h_GlobalTheory_ThK_Dbl_Stab2Cpt : GlobalTheory.ThK.Dbl.Stab2Cpt := (GlobalTheory.ThK.Dbl.stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWAnisoX : GlobalTheory.ThK.Dbl.SWAnisoX := (PositivityTheory.ThKClose.swAnisoX_of h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_FrameConj h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_EisContinues : GlobalTheory.ThK.Dbl.EisContinues := (GlobalTheory.ThK.Dbl.eisContinues_of h_GlobalTheory_ThK_Dbl_EisBL h_GlobalTheory_ThK_Dbl_FrameConj)
  have h_GlobalTheory_ThK_Dbl_BoxSecX : GlobalTheory.ThK.Dbl.BoxSecX := (GlobalTheory.ThK.Dbl.boxSecX_of h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWFullX : GlobalTheory.ThK.Dbl.SWFullX := (GlobalTheory.ThK.Dbl.swFullX_of h_GlobalTheory_ThK_Dbl_SWAnisoX h_GlobalTheory_ThK_Dbl_EisContinues h_GlobalTheory_ThK_Dbl_BoxSecX)
  have h_GlobalTheory_ThK_Dbl_DblX : GlobalTheory.ThK.Dbl.DblX := (GlobalTheory.ThK.Dbl.dblX)
  have h_GlobalTheory_ThK_Dbl_HgtInt : GlobalTheory.ThK.Dbl.HgtInt := (GlobalTheory.ThK.Dbl.hgtInt)
  have h_Weil6_ThKEst_SiegelAll : PositivityTheory.ThKEst.SiegelAll := (PositivityTheory.ThKEst.siegelAll_of hSiegelSet)
  have h_Weil6_ThKF_Unimod : PositivityTheory.ThKF.Unimod := (PositivityTheory.ThKF.unimodularity_holds)
  have h_GlobalTheory_ThK_Dbl_CptAll : GlobalTheory.ThK.Dbl.CptAll := (GlobalTheory.ThK.Dbl.cptAll_of h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_FinVolU h_Weil6_ThKF_Unimod)
  have h_GlobalTheory_ThK_Dbl_PolSch : GlobalTheory.ThK.Dbl.PolSch := (GlobalTheory.ThK.Dbl.polSch)
  have h_GlobalTheory_ThK_Dbl_NormZeta : GlobalTheory.ThK.Dbl.NormZeta := (GlobalTheory.ThK.Dbl.normZeta_of h_GlobalTheory_ThK_Dbl_SWFullX h_GlobalTheory_ThK_Dbl_BoxSecX h_GlobalTheory_ThK_Dbl_DblX h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_HgtInt h_GlobalTheory_ThK_Dbl_Stab2Cpt h_GlobalTheory_ThK_Dbl_CptAll h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_PolSch)
  have h_GlobalTheory_ThK_Dbl_EulerProd : GlobalTheory.ThK.Dbl.EulerProd := (GlobalTheory.ThK.Dbl.eulerProd)
  have h_GlobalTheory_ThK_Dbl_LocMeas : GlobalTheory.ThK.Dbl.LocMeas := (GlobalTheory.ThK.Dbl.locMeas)
  have h_GlobalTheory_ThK_Dbl_LocUnrSplit : GlobalTheory.ThK.Dbl.LocUnrSplit := (GlobalTheory.ThK.Dbl.locUnrSplit)
  have h_GlobalTheory_ThK_Dbl_LocUnrInert : GlobalTheory.ThK.Dbl.LocUnrInert := (GlobalTheory.ThK.Dbl.Inert.main)
  have h_GlobalTheory_ThK_Dbl_LocUnr : GlobalTheory.ThK.Dbl.LocUnr := (GlobalTheory.ThK.Dbl.locUnr_of h_GlobalTheory_ThK_Dbl_LocUnrSplit h_GlobalTheory_ThK_Dbl_LocUnrInert)
  have h_GlobalTheory_ThK_Dbl_BadFactor : GlobalTheory.ThK.Dbl.BadFactor := (GlobalTheory.ThK.Dbl.badFactor)
  have h_GlobalTheory_ThK_Dbl_RealInv : GlobalTheory.ThK.Dbl.RealInv := (GlobalTheory.ThK.Dbl.realInv_of h_Weil6_ThKF_ArchOp)
  have h_GlobalTheory_ThK_Dbl_DProd : GlobalTheory.ThK.Dbl.DProd := (GlobalTheory.ThK.Dbl.dProd)
  have h_GlobalTheory_ThK_Dbl_NonZeroBot : GlobalTheory.ThK.Dbl.NonZeroBot := (GlobalTheory.ThK.Dbl.nonZeroBottom_of_doubling_integral h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_Dbl_LInt2 h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_NormZeta h_GlobalTheory_ThK_Dbl_EulerProd h_GlobalTheory_ThK_Dbl_LocMeas h_GlobalTheory_ThK_Dbl_LocUnr h_GlobalTheory_ThK_Dbl_BadFactor h_GlobalTheory_ThK_Dbl_RealInv h_GlobalTheory_ThK_Dbl_DProd)
  have h_GlobalTheory_ThK_Dbl_SchToPol : GlobalTheory.ThK.Dbl.SchToPol := (GlobalTheory.ThK.Dbl.schToPol_of h_GlobalTheory_ThK_WeilConv)
  have h_GlobalTheory_ThK_Dbl_LeviEx : GlobalTheory.ThK.Dbl.LeviEx := (GlobalTheory.ThK.Dbl.leviEx)
  have h_Weil6_ThK_FinRam : PositivityTheory.ThK.FinRam := (hFinRam)
  have h_Weil6_ThK_FinSplit : PositivityTheory.ThK.FinSplit := (hFinSplit)
  have h_Weil6_ThK_FinInert : PositivityTheory.ThK.FinInert := (hFinInert)
  have h_GlobalTheory_ThK_KFin : GlobalTheory.ThK.KFin := (PositivityTheory.ThK.kFin_of h_Weil6_ThK_FinRam h_Weil6_ThK_FinSplit h_Weil6_ThK_FinInert)
  have h_GlobalTheory_ThK_Dbl_ToSo : GlobalTheory.ThK.Dbl.ToSo := (GlobalTheory.ThK.Dbl.toSo_of h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_KCoinv h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_CptAll)
  have h_GlobalTheory_ThK_NonZeroAn : GlobalTheory.ThK.NonZeroAn := (GlobalTheory.ThK.Dbl.nonZeroAn_of h_GlobalTheory_ThK_Dbl_NonZeroBot h_GlobalTheory_ThK_TowerA h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_CTBigZero h_GlobalTheory_ThK_CTSmallZero h_GlobalTheory_ThK_Dbl_SchToPol h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_LeviEx h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_Dbl_ToSo)
  have h_GlobalTheory_ThK_KDecay : GlobalTheory.ThK.KDecay := (PositivityTheory.ThKEst.kDecay hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEst_SqAll : PositivityTheory.ThKEst.SqAll := (PositivityTheory.ThKEst.sqAll)
  have h_Weil6_ThKEst_SqSo : PositivityTheory.ThKEst.SqSo := (PositivityTheory.ThKEst.sqSo)
  have h_Weil6_ThKEst_LatCpt : PositivityTheory.ThKEst.LatCpt := (PositivityTheory.ThKEst.latCpt_of)
  have h_Weil6_ThKEst_LatTor : PositivityTheory.ThKEst.LatTor := (PositivityTheory.ThKEst.latTor)
  have h_Weil6_ThKEst_LatFull : PositivityTheory.ThKEst.LatFull := (PositivityTheory.ThKEst.latFull)
  have h_GlobalTheory_ThK_SqInt : GlobalTheory.ThK.SqInt := (PositivityTheory.ThKEst.Sq.sqInt_of_leaves h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_SqAll h_Weil6_ThKEst_SqSo h_Weil6_ThKEst_SoFin h_Weil6_ThKEst_LatCpt h_Weil6_ThKEst_LatTor h_Weil6_ThKEst_LatFull)
  have h_Weil6_ThKF_ICont : PositivityTheory.ThKF.ICont := (PositivityTheory.ThKEst.iCont hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKF_RadMax : PositivityTheory.ThKF.RadMax := (PositivityTheory.ThKF.Unit.radMax_of h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_PolRange h_GlobalTheory_RealLift_LieFirst h_GlobalTheory_RealLift_LieSecond)
  have h_Weil6_ThK_LocPairEx : PositivityTheory.ThK.LocPairEx := (PositivityTheory.ThKH.Locpair.locPairEx)
  have h_Weil6_ThK_SiegelTransport : PositivityTheory.ThK.SiegelTransport := (PositivityTheory.ThK.siegel_transport)
  have h_Weil6_ThK_LinearAct : PositivityTheory.ThK.LinearAct := (PositivityTheory.ThK.split_character_fixes_evaluation)
  have h_Weil6_ThKF_SoCoinv : PositivityTheory.ThKF.SoCoinv := (hSo h_GlobalTheory_ThK_KFin)
  have h_Weil6_ThKF_Kills : PositivityTheory.ThKF.Kills := (PositivityTheory.Sph.theta_kills_cusp_forms_spherical h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_SoCont h_GlobalTheory_ThK_SqInt h_GlobalTheory_ThK_KDecay h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_ICont h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie h_Weil6_ThKF_ArchUniq h_Weil6_ThKF_RadMax hSph h_Weil6_ThKR_JoinTri h_Weil6_ThKF_SoCoinv)
  have h_GlobalTheory_ThK_Factor : GlobalTheory.ThK.Factor := (PositivityTheory.ThKF.factor_of h_GlobalTheory_ThK_KDecay h_Weil6_ThKF_Kills)
  have h_GlobalTheory_ThK_PolZero : GlobalTheory.ThK.PolZero := (PositivityTheory.ThKR.polynomial_vanishing_of_compactness h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_EisBL GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds h_GlobalTheory_ThK_NonZeroAn h_GlobalTheory_ThK_Factor h_GlobalTheory_ThK_MatchEx h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KDecay h_Weil6_ThKF_ICont h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_FinVolU h_Weil6_ThKF_Unimod)
  have h_Weil6_ThKCT_StabDec : PositivityTheory.ThKCT.StabDec := (PositivityTheory.ThKCT.stabDec_of)
  have h_Weil6_ThKG_Loc_SplitInv2 : PositivityTheory.ThKG.Loc.SplitInv2 := (PositivityTheory.ThKCT.splitInv2_of h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_StabDec h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_TriplePair h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKG_Loc_Hyp : PositivityTheory.ThKG.Loc.Hyp := (PositivityTheory.ThKG.Loc.hyp_of h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_SoCont h_GlobalTheory_ThK_KDecay h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_Kills h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie h_Weil6_ThKF_ArchUniq h_GlobalTheory_ThK_SplitEx h_Weil6_ThKG_Loc_SplitInv2 h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_FacNe)
  have h_Weil6_ThKG_Loc_MeasEx : PositivityTheory.ThKG.Loc.MeasEx := (PositivityTheory.ThKG.Loc.Cone.measEx_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKG_Loc_Cone_IdeleFub : PositivityTheory.ThKG.Loc.Cone.IdeleFub := (PositivityTheory.ThKG.Loc.Cone.ideleFub)
  have h_Weil6_ThKG_Loc_Cone_IdealId0 : PositivityTheory.ThKG.Loc.Cone.IdealId0 := (PositivityTheory.ThKG.Loc.Cone.Id.idealId0)
  have h_Weil6_ThKCT_ThetaExp : PositivityTheory.ThKCT.ThetaExp := (PositivityTheory.ThKCT.thetaExp)
  have h_Weil6_ThKCT_EvUniq : PositivityTheory.ThKCT.EvUniq := (PositivityTheory.ThKCT.evUniq_of h_Weil6_ThKCT_ThetaExp)
  have h_Weil6_ThKCT_MixAB : PositivityTheory.ThKCT.MixAB := (PositivityTheory.ThKCT.Ker.mixAB_of h_Weil6_ThKG_MixW h_Weil6_ThKG_MixX h_GlobalTheory_ThK_EvZero h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKCT_ThetaExp h_Weil6_ThKCT_EvUniq)
  have h_Weil6_ThKCT_SoStab : PositivityTheory.ThKCT.SoStab := (PositivityTheory.ThKCT.soStab_of)
  have h_Weil6_ThKCT_Low : PositivityTheory.ThKCT.Low := (PositivityTheory.ThKCT.low_of)
  have h_Weil6_ThKCT_SoEv : PositivityTheory.ThKCT.SoEv := (PositivityTheory.ThKCT.soEv_of' h_Weil6_ThKCT_Low)
  have h_Weil6_ThKCT_LinEx : PositivityTheory.ThKCT.LinEx := (PositivityTheory.ThKCT.linEx_of)
  have h_Weil6_ThKG_Loc_FLocB : PositivityTheory.ThKG.Loc.FLocB := (PositivityTheory.ThKG.Loc.FL.fLocB_of h_Weil6_ThKG_Loc_Cone_IdeleFub h_Weil6_ThKG_Loc_Cone_IdealId0 h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKCT_MixAB h_Weil6_ThKEst_TriplePair h_Weil6_ThKCT_SoStab h_Weil6_ThKCT_SoEv h_Weil6_ThKCT_LinEx)
  have h_Weil6_ThKCT_Slice : PositivityTheory.ThKCT.Slice := (PositivityTheory.ThKCT.slice_of)
  have h_Weil6_ThKCT_SchInt : PositivityTheory.ThKCT.SchInt := (PositivityTheory.ThKCT.schInt)
  have h_Weil6_ThKG_Loc_BumpA : PositivityTheory.ThKG.Loc.BumpA := (PositivityTheory.ThKG.Loc.Bump.bumpA_fin h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_Weil6_ThKCT_MixAB)
  have h_Weil6_ThKG_Loc_BumpB : PositivityTheory.ThKG.Loc.BumpB := (PositivityTheory.ThKG.Loc.Bump.bumpB_fin h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_Weil6_ThKCT_MixAB)
  have h_Weil6_ThKG_Loc_RealUniq : PositivityTheory.ThKG.Loc.RealUniq := (PositivityTheory.ThKG.CayleyTransformDarboux.realUniq)
  have h_Weil6_ThKG_Loc_H1Unr2 : PositivityTheory.ThKG.Loc.UnramifiedMultiplicityOneProportional := (PositivityTheory.ThKG.Loc.unramifiedProportional_holds)
  have h_Weil6_ThKG_Loc_H1Ram : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne := (hH1Ram)
  have h_Weil6_ThKG_Loc_H1Inf : PositivityTheory.ThKG.Loc.ArchimedeanMultiplicityOne := (PositivityTheory.ThKG.CayleyTransformDarboux.archimedean_multiplicity_one_of_lie h_GlobalTheory_RealLift_LieFirst h_GlobalTheory_RealLift_LieSecond)
  have h_Weil6_ThKG_Loc_Hyp2 : PositivityTheory.ThKG.Loc.Hyp2 := ⟨h_Weil6_ThKG_Loc_MeasEx, h_Weil6_ThKG_Loc_FLocB, h_Weil6_ThKG_Loc_BumpA, h_Weil6_ThKG_Loc_BumpB, h_Weil6_ThKG_Loc_RealUniq, h_Weil6_ThKG_Loc_H1Unr2, h_Weil6_ThKG_Loc_H1Ram, h_Weil6_ThKG_Loc_H1Inf, h_GlobalTheory_ThK_CTBigZero, h_GlobalTheory_ThK_CTSmallCone, h_GlobalTheory_ThK_CTBigCone, h_GlobalTheory_ThK_CTSmallZero⟩
  have h_GlobalTheory_ThK_ActsEx : GlobalTheory.ThK.ActsEx := (PositivityTheory.ThKF0.actsEx)
  have h_Weil6_Mix_PureSt : PositivityTheory.Mix.PureSt := (PositivityTheory.Mix.pure_tensor_estimates_holds)
  have h_Weil6_ThKG_Loc_Bump_ArchDict : PositivityTheory.ThKG.Loc.Bump.ArchDict := (PositivityTheory.ThKG.Loc.Bump.archDict_of)
  have h_Weil6_ThKG_Loc_Bump_ArchHeis : PositivityTheory.ThKG.Loc.Bump.ArchHeis := (PositivityTheory.ThKG.Loc.Bump.archHeis_of)
  have h_GlobalTheory_RealLift_FrameEx : GlobalTheory.RealLift.FrameEx := (PositivityTheory.KRealA.i_frameex)
  have h_Weil6_ThKCT_EvAdm : PositivityTheory.ThKCT.EvAdm := (PositivityTheory.ThKCT.evAdm_of)
  have h_Weil6_ThKG_Loc_Cone_ArchCone : PositivityTheory.ThKG.Loc.Cone.ArchCone := (PositivityTheory.ThKG.Loc.Bump.archCone_of h_Weil6_ThKG_Loc_Bump_ArchDict h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKG_Loc_Bump_ArchHeis h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_FrameEx h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_KFinData)
  have h_Weil6_ThKG_Loc_Cone_VacFixX : PositivityTheory.ThKG.Loc.Cone.VacFixX := (PositivityTheory.ThKG.Loc.Cone.vacFixX_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKG_Loc_ConeFacA : PositivityTheory.ThKG.Loc.ConeFacA := (PositivityTheory.ThKG.Loc.Cone.coneFac_all h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone h_Weil6_ThKG_Loc_Cone_VacFixX).2.1
  have h_Weil6_ThKG_Loc_StdA : PositivityTheory.ThKG.Loc.StdA := (PositivityTheory.ThKG.Std.stdA)
  have h_Weil6_ThKG_LocA_ : PositivityTheory.ThKG.LocA' := (PositivityTheory.ThKG.Loc.locA_of h_Weil6_ThKG_Loc_Hyp h_Weil6_ThKG_Loc_Hyp2 h_Weil6_ThKG_Loc_ConeFacA h_Weil6_ThKG_Loc_StdA)
  have h_Weil6_ThKG_Loc_ConeFacB : PositivityTheory.ThKG.Loc.ConeFacB := (PositivityTheory.ThKG.Loc.Cone.coneFac_all h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone h_Weil6_ThKG_Loc_Cone_VacFixX).2.2
  have h_Weil6_ThKG_Loc_StdB : PositivityTheory.ThKG.Loc.StdB := (PositivityTheory.ThKG.Std.stdB)
  have h_Weil6_ThKG_LocB_ : PositivityTheory.ThKG.LocB' := (PositivityTheory.ThKG.Loc.locB_of h_Weil6_ThKG_Loc_Hyp h_Weil6_ThKG_Loc_Hyp2 h_Weil6_ThKG_Loc_ConeFacB h_Weil6_ThKG_Loc_StdB)
  have h_GlobalTheory_ThK_EndA : GlobalTheory.ThK.EndA := (PositivityTheory.Sph.Tr.endAB_sph hSiegelSet h_Weil6_ThKG_Tow_WeilEx hKCo hFinRam hFinSplit hFinInert h_GlobalTheory_RealLift_LieSecond h_Weil6_ThKF_ArchLie h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_EisBL).1
  have h_Weil6_ThKG_EndA_ : PositivityTheory.ThKG.EndA' := (PositivityTheory.ThKG.endA'_of h_GlobalTheory_ThK_EndA)
  have h_GlobalTheory_ThK_EndB : GlobalTheory.ThK.EndB := (PositivityTheory.Sph.Tr.endAB_sph hSiegelSet h_Weil6_ThKG_Tow_WeilEx hKCo hFinRam hFinSplit hFinInert h_GlobalTheory_RealLift_LieSecond h_Weil6_ThKF_ArchLie h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_EisBL).2
  have h_Weil6_ThKG_EndB_ : PositivityTheory.ThKG.EndB' := (PositivityTheory.ThKG.endB'_of h_GlobalTheory_ThK_EndB)
  have h_Weil6_ThKG_Leaves : PositivityTheory.ThKG.Leaves := ⟨h_GlobalTheory_ThK_EvZero, h_GlobalTheory_ThK_EvCone, h_GlobalTheory_ThK_StabEx, h_GlobalTheory_ThK_TowerA, h_GlobalTheory_ThK_TowerB, h_GlobalTheory_ThK_FacNe, h_GlobalTheory_ThK_MatchEx, h_Weil6_ThKG_LeviEx, h_Weil6_ThKG_PolDense, h_GlobalTheory_ThK_WeilConv, h_GlobalTheory_ThK_SoCont, h_GlobalTheory_ThK_SplitEx, h_GlobalTheory_ThK_CTBigZero, h_GlobalTheory_ThK_CTSmallZero, h_GlobalTheory_ThK_CTBigCone, h_GlobalTheory_ThK_CTSmallCone, h_GlobalTheory_ThK_AnAll, h_GlobalTheory_ThK_PolRe, h_GlobalTheory_ThK_NonZeroAn, h_GlobalTheory_ThK_PolZero, h_Weil6_ThKG_LocA_, h_Weil6_ThKG_LocB_, h_Weil6_ThKG_EndA_, h_Weil6_ThKG_EndB_, h_GlobalTheory_ThK_KReal, h_GlobalTheory_ThK_KFin⟩
  exact PositivityTheory.ThKG.agree_of_leaves h_Weil6_ThKG_Leaves h_GlobalTheory_ThK_KDecay h_GlobalTheory_ThK_KCoinv
