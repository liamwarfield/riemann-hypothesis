module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem exists_integral_cell : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (A : ValuationSubring K) (M : ℕ)
    (c u : Let m → Fin (M + 1) → K), InBlock c u → (∀ τ, LinearIndependent K fun j : Fin (m τ) => u ⟨τ, j⟩) →
    ∃ (w : Pm m) (x : CellVar m → K) (d : Let m → K), (∀ v, x v ∈ A) ∧ (∀ z, d z ≠ 0) ∧
      Tri (cellVec c w x) u d := by
  intro T m K _ A M c u hin hli
  have hg : ∀ z : Let m, ∃ a : Fin (m z.1) → K, ∑ i, a i • c ⟨z.1, i⟩ = u z := fun z =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hin z)
  choose a ha using hg
  let g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) K := fun τ i j => a ⟨τ, j⟩ i
  have hu : ∀ τ j, u ⟨τ, j⟩ = ∑ i, g τ i j • c ⟨τ, i⟩ := fun τ j => (ha ⟨τ, j⟩).symm
  have hgli : ∀ τ, LinearIndependent K (g τ).transpose := by
    intro τ
    refine Fintype.linearIndependent_iff.2 fun s hs => ?_
    have hs' : ∀ i, ∑ j, s j * g τ i j = 0 := fun i => by
      have := congrFun hs i
      simpa [Finset.sum_apply, Matrix.transpose_apply] using this
    have h0 : ∑ j, s j • u ⟨τ, j⟩ = 0 := by
      simp_rw [hu, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      simp [hs']
    exact Fintype.linearIndependent_iff.1 (hli τ) s h0
  have hdec := fun τ => GlobalTheory.exists_integral_pivot_decomposition K A _ _ (g τ) (hgli τ)
  choose ι u0 b huA hu0 hu1 hbt hbd hgub using hdec
  have hbij : ∀ τ, Function.Bijective (ι τ) := fun τ => Finite.injective_iff_bijective.1 (ι τ).injective
  let w : Pm m := fun τ => Equiv.ofBijective _ (hbij τ)
  let x : CellVar m → K := fun v => u0 v.1 (ι v.1 v.2.1.1) v.2.1.2
  refine ⟨w, x, fun z => b z.1 z.2 z.2, fun v => huA _ _ _, fun z => hbd _ _, ?_⟩
  have hcell : ∀ τ i j, cell x τ i j = u0 τ (ι τ i) j := by
    intro τ i j
    unfold cell
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hu1 τ i).symm
    · have : i < j := lt_of_le_of_ne (not_lt.1 h1) h2
      exact (hu0 τ i j this).symm
  have hv : ∀ τ j, cellVec c w x ⟨τ, j⟩ = ∑ k, u0 τ k j • c ⟨τ, k⟩ := by
    intro τ j
    simp only [cellVec, hcell]
    exact Equiv.sum_comp (w τ) (fun k => u0 τ k j • c ⟨τ, k⟩)
  have hexp : ∀ τ j, u ⟨τ, j⟩ = ∑ l, b τ l j • cellVec c w x ⟨τ, l⟩ := by
    intro τ j
    rw [hu]
    simp_rw [hv, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [show g τ i j = (u0 τ * b τ) i j from by rw [← hgub τ], Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rintro ⟨τ, j⟩
  show u ⟨τ, j⟩ - b τ j j • cellVec c w x ⟨τ, j⟩ ∈ _
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun l hl => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, h, rfl⟩)
  · rw [hbt τ h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedFieldStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_flagCell_of_valuedField : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (A : ValuationSubring K) (M : ℕ) (c u : Let m → Fin (M + 1) → K), InBlock c u → (∀ τ, LinearIndependent K fun j : Fin (m τ) => u ⟨τ, j⟩) → ∃ (w : Pm m) (x : CellVar m → K) (d : Let m → K), (∀ v, x v ∈ A) ∧ (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.exists_integral_cell | exact GlobalTheory.FlagEmb.exists_integral_cell | (intros; apply GlobalTheory.FlagEmb.exists_integral_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart sp fB)

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem exists_univChart_pullback {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    ∃ xc : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ (Over.pullback x).obj t.G, IsUnivChart _ n xc ∧
      ∀ cc : Fin n → A, LieLocBasis.vec t x xc cc = (tvec (x := y) cc).left ≫ ψ := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback t.G x)
  refine ⟨fun m => y m ≫ e.hom, gfp_chart_iso e hy, fun cc => ?_⟩
  have key : (tvec (x := fun m => y m ≫ e.hom) cc).left = (tvec (x := y) cc).left ≫ e.hom.left := by
    show (_ ≫ y 1 ≫ e.hom).left = (_ ≫ y 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => y m ≫ e.hom) cc).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ]

theorem isTanBasis_of_chart {A : Type} [CommRing A] (x : Sp A ⟶ X) {G₁ : Over (Spec (CommRingCat.of A))}
    [GrpObj G₁] {ψ : G₁.left ⟶ t.G.left} (h : IsGrpPullback G₁ t.G x ψ) (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart G₁) {n : ℕ}
    {y : ∀ m : ℕ, sp (R₀ := A) (ReciprocityTheory.ChartRestriction.G.Chart.JetR A (Fin n) m) ⟶ G₁} (hy : IsUnivChart G₁ n y) :
    IsTanBasis t x fun j => (tvec (x := y) (Pi.single j 1)).left ≫ ψ := by
  refine ⟨fun j => ?_, fun S' _ φ w hw => ?_⟩
  · obtain ⟨xc, hx, hv⟩ := exists_univChart_pullback t x h hy
    have h1 := LieLocBasis.vec_tan hx (Pi.single j 1)
    rw [hv] at h1
    exact h1
  let _ : Algebra A S' := φ.toAlgebra
  obtain ⟨y', hy', e'⟩ := LieChart.univChart_baseChange_of_chart (R' := S') G₁ C n y hy
  obtain ⟨xc', hx', hv⟩ := exists_univChart_pullback t (spMap φ ≫ x)
    ((isGrpPullback_pullback G₁ (fB A S')).comp h) hy'
  obtain ⟨cc, rfl⟩ := LieLocBasis.vec_exists hx' w hw
  have hD : (fun j => spMap (dualMap φ) ≫ (tvec (x := y) (Pi.single j 1)).left ≫ ψ) =
      fun j => LieLocBasis.vec t (spMap φ ≫ x) xc' (Pi.single j 1) := by
    funext j
    have h1 : (Pi.single j 1 : Fin n → S') = algebraMap A S' ∘ (Pi.single j 1 : Fin n → A) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Pi.single_eq_of_ne hi]
    rw [hv, h1, ← Category.assoc (tvec (x := y') _).left, e', Category.assoc]
    rfl
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (LieLocBasis.comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((LieLocBasis.comb_iff hx' _ _ _).1 ha).symm

theorem exists_affine_isTanBasis (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Scheme.{0}) (ρ : S ⟶ X) (z : S) :
    ∃ (V : S.affineOpens) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(S, V.1)) ⟶ t.G.left)),
      z ∈ V.1 ∧ IsTanBasis t (R := Γ(S, V.1)) (V.2.fromSpec ≫ ρ) e := by
  let G : Over S := (Over.pullback ρ).obj t.G
  have : Smooth G.hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom ρ)
    infer_instance
  obtain ⟨U, hU, V, hV, e, hxU, -, hs, h⟩ :=
    LieChart.exists_isStandardSmooth_section G.hom (η[G]).left (Over.w η[G]) z ⊤ trivial
  let i : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  let G₀ : Over (Spec (CommRingCat.of Γ(S, U))) := (Over.pullback i).obj G
  have hφ₀ : IsGrpPullback G₀ G i (pullback.fst G.hom i) := isGrpPullback_pullback G i
  obtain ⟨C, hC⟩ := LieChart.exists_chart_pullback G hU hV e hs h G₀ _ hφ₀
  obtain ⟨n, y, hy⟩ := LieChart.univChart_of_chart G₀ C hC
  exact ⟨⟨U, hU⟩, n, _, hxU,
    isTanBasis_of_chart t (i ≫ ρ) (hφ₀.comp (isGrpPullback_pullback t.G ρ)) C hy⟩

end GlobalTheory.LineNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
noncomputable section

namespace GlobalTheory.Mem.SRe.SxPass

section Mv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl Formalism.L2.SG.ColDict Formalism.L2.SG.HidaSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {F F' : ∀ u, Forms0 D u}

set_option maxHeartbeats 4000000 in
def trCar (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) : Transport X u (F' u) :=
  { t with
    hc_rep := fun c => by rw [(h u).2.2.2.1]; exact t.hc_rep c
    J_isom := fun c ξ η => by rw [(h u).2.2.2.2]; exact t.J_isom c ξ η }

set_option maxHeartbeats 4000000 in
theorem colDictL_car (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) (hK : X.LevelSubgroupCharacter) :
    colDictL X (trCar h t) hK = colDictL X t hK := by
  refine LinearMap.ext fun T => funext fun c => funext fun z => ?_
  exact congrArg (fun e => t.J (shP X u T.1 (t.hc c)) (e z)) (congrArg DFunLike.coe (h u).2.2.2.2)

theorem chi_of_heq {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} (e : U' = U) (h : HEq chi' chi)
    (x : G) (hx : x ∈ U') : chi' ⟨x, hx⟩ = chi ⟨x, e ▸ hx⟩ := by
  subst e
  rw [eq_of_heq h]

set_option maxHeartbeats 4000000 in
theorem lev_car (h : SameCar F F') {X : HidaSetting D} {u} {t : Transport X u (F u)} {hK : X.LevelSubgroupCharacter} (l : LevelMatch X t hK) :
    LevelMatch X (trCar h t) hK := by
  refine ⟨fun x => ?_, fun g y hr => ⟨?_, fun hk hy => ?_⟩⟩
  · rw [(h u).1]; exact l.1 x
  · rw [(h u).2.1]; exact (l.2 g y hr).1
  · rw [chi_of_heq (h u).2.1 (h u).2.2.1]; exact (l.2 g y hr).2 hk _

set_option maxHeartbeats 4000000 in
def packCar (h : SameCar F F') (P : SPack D F) : SPack D F' :=
  { P with
    tr := fun u => trCar h (P.tr u)
    into := fun u T => by rw [colDictL_car]; exact P.into u T
    bij := fun u => by unfold ColDictBij; rw [colDictL_car]; exact P.bij u
    lev := fun u => lev_car h (P.lev u)
    isom := fun u a b => by rw [colDictL_car]; exact P.isom u a b }

set_option maxHeartbeats 4000000 in
def restCar (h : SameCar F F') {P : SPack D F} (S : SRest P) : SRest (packCar h P) where
  hI := S.hI
  autTie := S.autTie
  colPin := fun u x => Subtype.ext ((LinearMap.congr_fun (colDictL_car h (P.tr u) P.Y.hK) _).trans (congrArg Subtype.val (S.colPin u x)))
  j := S.j
  rowPin := S.rowPin
  locTied := S.locTied

set_option maxHeartbeats 4000000 in
def satCar (h : SameCar F F') (p : RowPk D) (s : p.SAt F) : p.SAt F' :=
  { P := packCar h s.P, S := restCar h s.S, t := s.t, c := s.c, c_pos := s.c_pos, see := s.see, ev := s.ev, rowJ := s.rowJ }

end Mv

section Slot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 8000000 in
theorem sxMv : SxMv := by
  intro K B f T w Z Wt p0 r col N h p0' t col' e ⟨s⟩
  obtain ⟨F₁, hF⟩ := exists_sameF_ofDiv (D := Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) fun u => (col.C.forms u).to0
  obtain ⟨s', -⟩ := GlobalTheory.T.spectralComparison_transported_divisionLatticeChange B w.C Z (pkOf r).G' (pkOf r).Pl0 (pkOf r).T (pkOf r).A (pkOf r).Ks (pkOf r).R (pkOf r).F
    (fun u => (col.C.forms u).to0) (pkOf r).eE (cast (sx_eq r col) s) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have c := StdUnique.sameStd B f T w Z (New.ofDiv (Late.D Z) ((by with_unfolding_all exact (N :))) ((by with_unfolding_all exact (h :)))) col ((by with_unfolding_all exact (col' :))) ((by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (hF :)))
  have e' : pkOf t = (pkOf r).up Z Z.S N h := eq_of_heq e
  rw [sx_eq t col', e']
  exact ⟨satCar (D := Late.D (upL Z Z.S N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) ((pkOf r).up Z Z.S N h) ((by with_unfolding_all exact (s' :)))⟩

end Slot

end GlobalTheory.Mem.SRe.SxPass

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeightsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralStageData_transfer_lattices_heights : GlobalTheory.Mem.SRe.SxMv := by
  first | exact @GlobalTheory.Mem.SRe.SxPass.sxMv | exact GlobalTheory.Mem.SRe.SxPass.sxMv | (intros; apply GlobalTheory.Mem.SRe.SxPass.sxMv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionPullbackThetaValue
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayEv

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

theorem formEq_term {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] {oa : D.OAct O} (Y : Ray oa) (k : ℕ) (α : D.X) :
    FormEq (Sum.elim (fun i => Y.q.left ≫ DegPre.famφB D α i) (DegPre.gtφT D Y.H Y.q α))
      (Sum.elim (DegPre.famε k) DegPre.gtε) (K' := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) := by
  have e1 : Y.q ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α) = padd D.P.A (DegPre.cT D Y.H α) Y.q := by
    simp only [padd, comp_lift_assoc, Category.comp_id]
    rw [← Hom.mul_def, ← Hom.mul_def, mul_comm, comp_toUnit_assoc]
  have e2 : Y.q.left ≫ (toUnit D.P.A ≫ D.c α).left = (DegPre.cT D Y.H α).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e3 : Y.q.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (DegPre.zeroT D Y.H).left := by
    rw [← Over.comp_left, comp_toUnit_assoc]
  have e0 : Y.q.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left =
      (padd D.P.A (DegPre.cT D Y.H α) Y.q).left := by
    rw [← Over.comp_left, e1]
  intro U _ h
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp only [DegPre.famφB, DegPre.famε, DegPre.gtφT, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e0, e2, e3]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem exists_sec_fourierTerm (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (Y : Ray oa) (k : ℕ) (α : D.X) (σ : D.SecB k α) : ∃ τ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (k : ℤ)), ∀ (T : Over (Sp R)) (x : T ⟶ Y.H) y J, Good D.P.L y J → sval τ x.left y J = sval σ (x ≫ Y.q).left y J * (val ((Y.Φ T x).s α) (𝟙 _) y J).val := by
  obtain ⟨τ, hτ⟩ := exists_sec D.P.isLB (formEq_term Y k α)
    (pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α))
  refine ⟨τ, fun T x y J hJ => ?_⟩
  refine (hτ _ _ y J hJ).trans ((sval_pullMulSec σ Y.q.left ((Y.Φ Y.H (𝟙 _)).s α) ((Y.Φ Y.H (𝟙 _)).isGen α)
    x.left y hJ).trans ?_)
  obtain ⟨-, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))
  have e := h₂ α y J hJ
  rw [Category.comp_id] at e
  rw [Over.comp_left]
  exact congrArg _ (congrArg Units.val e.symm)

end GlobalTheory.RayEv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad.Pull

open Cardinal

theorem exists_scf_embedding_dvd :
    ∀ (p : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], p.Prime → (p : V) ∈ IsLocalRing.maximalIdeal V → Cardinal.mk V ≤ Cardinal.continuum → ∃ (C : SCF p) (φ : V →+* ↥(intO ↥C.S)), Function.Injective φ ∧ ∀ a b : V, ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ ≤ ‖((φ b : ↥(intO ↥C.S)) : ↥C.S)‖ → b ∣ a := by
  intro p V _ _ _ _ hp hpm hV
  let K := FractionRing V
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V K hp0 hpm
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  have hK : #K ≤ 𝔠 :=
    (IsLocalization.cardinalMk_le (nonZeroDivisors V)).trans hV
  have hx : 1 < ‖algebraMap K C (algebraMap V K p)⁻¹‖ := by
    rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
  obtain ⟨L, hKL, hcl, hac, hL⟩ := GlobalTheory.SmallClosedField.exists_small_closed_subfield hK hx
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  haveI : CharZero K := charZero_of_injective_ringHom (IsFractionRing.injective V K)
  let i : K →+* L := (algebraMap K C).codRestrict L hKL
  have hi : ∀ y, ‖i y‖ = ‖algebraMap K C y‖ := fun _ => rfl
  haveI : CharZero L := charZero_of_injective_ringHom i.injective
  have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast i, hi, ← map_natCast (algebraMap V K), hCp]
  obtain ⟨D, e, he⟩ := GlobalTheory.SmallClosedField.exists_scf_isometry hLp hL
  let g : V →+* D.S := (e.comp i).comp (algebraMap V K)
  have hg : ∀ a : V, ‖g a‖ = ‖algebraMap K C (algebraMap V K a)‖ := fun a => by
    simp only [g, RingHom.comp_apply, he, hi]
  have hle : ∀ a : V, g a ∈ intO D.S := fun a => by
    change ‖g a‖ ≤ 1
    rw [hg]; exact (hC _).2 ⟨a, rfl⟩
  refine ⟨D, g.codRestrict _ hle, fun a b hab => ?_, fun a b hab => ?_⟩
  · have h := congrArg Subtype.val hab
    exact IsFractionRing.injective V K (i.injective (e.injective h))
  · change ‖g a‖ ≤ ‖g b‖ at hab
    rw [hg, hg] at hab
    by_cases hb : b = 0
    · subst hb
      have : algebraMap K C (algebraMap V K a) = 0 := by
        rw [map_zero, map_zero, norm_zero] at hab
        exact norm_le_zero_iff.1 hab
      rw [(map_eq_zero_iff _ (algebraMap K C).injective).1 this |>
        (map_eq_zero_iff _ (IsFractionRing.injective V K)).1]
    · have hb' : algebraMap V K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hb
      have hbC : 0 < ‖algebraMap K C (algebraMap V K b)‖ :=
        norm_pos_iff.2 ((map_ne_zero_iff _ (algebraMap K C).injective).2 hb')
      obtain ⟨c, hc⟩ := (hC (algebraMap V K a / algebraMap V K b)).1 (by
        rw [map_div₀, norm_div]; exact div_le_one_of_le₀ hab hbC.le)
      refine ⟨c, IsFractionRing.injective V K ?_⟩
      rw [map_mul, hc, mul_div_cancel₀ _ hb']

end GlobalTheory.ShFam.Pad.Pull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramePointCombinationMatrix
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.FramePairGram

attribute [local instance] Over.cartesianMonoidalCategory

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
  {t : SAB H X} {t' : SAB H X'} {S : Type} [CommRing S] {f : X' ⟶ X}

theorem left_pushE_symm_congr (m : SABMap t' t f) {q q' : Sp S ⟶ X'} (e : q = q') {x₀ x₀' : Sp S ⟶ X}
    (hq : q ≫ f = x₀) (hq' : q' ≫ f = x₀') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x₀ v)
    (hv' : IsTanAtG t x₀' v) :
    (tv ((pushE m q hq).symm (tanOf hv))).left = (tv ((pushE m q' hq').symm (tanOf hv'))).left := by
  subst e
  subst hq
  subst hq'
  rfl

end Generic

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem ptF_eq_of_x_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x) :
    GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF y' :=
  pullback.hom_ext ((ptF_fst y).trans (h.trans (ptF_fst y').symm)) ((ptF_snd y).trans (ptF_snd y').symm)

theorem ofFrPt_v_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x)
    {x : Sp S ⟶ Z.X} (hx : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ genι Z = x) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (hv : IsTanAtG Xo.univ.t y'.x (y.u τ i)) :
    (EigFrame.ofFrPt Z y hx).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  show (tv (pushE Z.m (GlobalTheory.AllWt.ptF y) hx
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).symm (tanOf (t := Xo.univ.t) (y.tan τ i))))).left =
    (tv (pushE Z.m (GlobalTheory.AllWt.ptF y') hx'
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y') (ptF_fst y')).symm (tanOf hv)))).left
  rw [left_pushE, left_pushE,
    left_pushE_symm_congr Z.m0.toSABMap (ptF_eq_of_x_eq h) (ptF_fst y) (ptF_fst y') (y.tan τ i) hv]

theorem isComb_ofFrPt {S : Type} [CommRing S] [Algebra c.F S] (y' : FrPt Xo c S) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → S)
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAtG Xo.univ.t y'.x w)
    (hc : IsCombAtG Xo.univ.t y'.x (y'.u τ) a w) :
    IsCombAtG Z.t x' ((EigFrame.ofFrPt Z y' hx').v τ) a (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  have e := (isComb_iff (t := Xo.univ.t) (x := y'.x) (fun b => tanOf (t := Xo.univ.t) (y'.tan τ b)) a (tanOf hv)).1 hc
  refine (isComb_iff (t := Z.t) (x := x') (fun b => lieEquiv Z y' hx' (tanOf (t := Xo.univ.t) (y'.tan τ b))) a
    (lieEquiv Z y' hx' (tanOf hv))).2 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  simp only [map_smul]

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

end Main

end GlobalTheory.FramePairGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem coreCharacter_fieldInclusion_eq_columnHeckeChar {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {h : B.fields.Ok} {W : Set B.places.Pl}
    (z : Dat (w.st Z) w.I h T W) (j : Fin B.R.m) :
    ChrEq (z.core.chiW ((j : ℕ) + 1) z.core.toCore.σ₀) (w.I.C.mu0 j) := by
  have e := Formalism.IndefR.FWT.chiTie_of_chiR z.core z.R.toRealDat z.geo.fw.alg_eq z.geo.fw.laws.pins.2.2.1 z.geo.fw.chiR j
  rw [e]
  have h1 := z.lev.is.mu0 j
  rw [z.lev.C] at h1
  exact h1

theorem embLL_chi {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : Fin B.R.m)
    (p : {p // p ∈ (B.primes w.px).vGs}) (c : (𝓞 B.fields.E ⧸ p.1.asIdeal)ˣ) (y : 𝓞 B.fields.E) (x : B.fields.Eˣ)
    (hx : (x : B.fields.E) = y) (hc : (c : 𝓞 B.fields.E ⧸ p.1.asIdeal) = Ideal.Quotient.mk p.1.asIdeal y) :
    B.embLL ((w.I.Ch.chi j p c : B.fields.Kˣ) : B.fields.K) = (((w.I.C.mu0 j).locK p.1 x : ℂˣ) : ℂ)⁻¹ := by
  have h1 := (w.ok.ch_tied.mu0 j).atg p x y c hx hc
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem app_chiW {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Type} [Monoid A]
    {H₁ H₂ : Host E} {l₁ : Level H₁} {l₂ : Level H₂} {c₁ : Coeff l₁} {c₂ : Coeff l₂}
    {χ₁ : ℕ → (c₁.F →+* ℂ) → A →* Circle} {χ₂ : ℕ → (c₂.F →+* ℂ) → A →* Circle}
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hχ : HEq χ₂ χ₁) (n : ℕ) :
    χ₂ n c₂.F.val.toRingHom = χ₁ n c₁.F.val.toRingHom := by
  cases hH; cases hl; cases hc; cases hχ; rfl

end GlobalTheory.Mem.R3.Rw.ChiTr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem embLL_chi_ext : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX j₁ j₂ hj p₁ p₂ hp c₁ c₂ hc
  have A₁ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₁ j₁
  have A₂ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₂ j₂
  have eH := hX.H
  have el := hX.l
  have ec := hX.c
  have eχ := hX.chiW
  obtain ⟨hP, -⟩ := hE
  clear hX
  rcases B₂ with ⟨P₂⟩
  change P₂ = B₁.toPre at hP
  subst hP
  have ec₀ := app_chiW eH el ec eχ ((j₁ : ℕ) + 1)
  rw [← hj] at A₂
  have A₂' : ChrEq (D := (w₁.st Z₁).toD7) (z₁.core.chiW ((j₁ : ℕ) + 1) z₁.core.Q.c.F.val.toRingHom) (w₂.I.C.mu0 j₂) := by
    rw [← ec₀]
    exact A₂
  have hχ : w₁.I.C.mu0 j₁ = w₂.I.C.mu0 j₂ := (GlobalTheory.ChrEqUnique.chrEq_unique _).1 _ _ _ A₁ A₂'
  rcases p₂ with ⟨q₂, hq₂⟩
  have eq : q₂ = p₁.1 := eq_of_heq hp
  subst eq
  have ecc : c₂ = c₁ := eq_of_heq hc
  subst ecc
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c₂ : 𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)
  have hy0 : ((y : 𝓞 B₁.fields.E) : B₁.fields.E) ≠ 0 := by
    intro h0
    have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
    rw [h0', map_zero] at hy
    exact c₂.ne_zero hy.symm
  rw [embLL_chi w₂ j₂ _ c₂ y (Units.mk0 _ hy0) rfl hy.symm, embLL_chi w₁ j₁ p₁ c₂ y (Units.mk0 _ hy0) rfl hy.symm, hχ]

end GlobalTheory.Mem.R3.Rw.ChiTr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtensionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameCharacters_typePrimes_eq_of_extension : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K) := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext | exact GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext | (intros; apply GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrArcExtensionMonoBase
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcExt

theorem exists_ramified_ext (T : CDVR) {Ω : Type} [Field Ω] [Algebra T.Fr Ω] [Algebra.IsAlgebraic T.Fr Ω] [IsAlgClosed Ω]
    (M : IntermediateField T.Fr Ω) [FiniteDimensional T.Fr M] (N : ℕ) (hN : 0 < N) (ϖ₀ : T.V) (h₀ : Irreducible ϖ₀) :
    ∃ (T' : CDVR) (g : T.V →+* T'.V) (κ : M →+* T'.Fr) (e : ℕ) (ϖ : T'.V),
      Function.Injective g ∧ IsLocalHom g ∧ Irreducible ϖ ∧
      (∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap T'.V T'.Fr (g v)) ∧
      N ∣ e ∧ Associated (g ϖ₀) (ϖ ^ e) := by
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap T.Fr Ω (algebraMap T.V T.Fr ϖ₀)) hN
  let A := IntermediateField.adjoin T.Fr ({α} : Set Ω)
  have : FiniteDimensional T.Fr A := IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  let L : IntermediateField T.Fr Ω := M ⊔ A
  have : FiniteDimensional T.Fr L := inferInstance
  obtain ⟨W, _, _, _, _, _, _, _, hc, -, hinj, hloc, -, -⟩ := GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  have : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := fun w =>
    (FractionRing.algEquiv W L).symm.commutes w
  let κ : M →+* FractionRing W := ψ.toRingHom.comp (IntermediateField.inclusion (le_sup_left : M ≤ L)).toRingHom
  have hκ : ∀ v, κ (algebraMap T.Fr M (algebraMap T.V T.Fr v)) = algebraMap W (FractionRing W) (algebraMap T.V W v) := by
    intro v
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr v) = algebraMap W L (algebraMap T.V W v) :=
      (RingHom.congr_fun hc v).symm
    rw [← hψ, ← h1]
    rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hg0 : algebraMap T.V W ϖ₀ ≠ 0 := fun h => h₀.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hϖ
  have hαL : α ∈ L := (le_sup_right : A ≤ L) (IntermediateField.mem_adjoin_simple_self T.Fr α)
  let b : FractionRing W := ψ ⟨α, hαL⟩
  have hb : b ^ N = algebraMap W (FractionRing W) (algebraMap T.V W ϖ₀) := by
    have h1 : (⟨α, hαL⟩ : L) ^ N = algebraMap W L (algebraMap T.V W ϖ₀) := by
      apply Subtype.ext
      have h2 := RingHom.congr_fun hc ϖ₀
      refine hα.trans ?_
      exact (congrArg (L.val) h2.symm)
    rw [← hψ, ← h1, map_pow]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow hN.ne'] at hb
    exact hg0 ((IsFractionRing.injective W (FractionRing W)) (by rw [← hb, map_zero]))
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := W) b
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [← hxy, map_zero, zero_div])
  obtain ⟨m, v₁, hv₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n, v₂, hv₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hW : x ^ N = algebraMap T.V W ϖ₀ * y ^ N := by
    apply IsFractionRing.injective W (FractionRing W)
    have hy' : algebraMap W (FractionRing W) y ≠ 0 := by
      simpa using hy0
    rw [map_pow, map_mul, map_pow, ← hb, ← hxy, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hy')]
  have he : m * N = e + n * N := by
    rw [hv₁, hv₂, hu, mul_pow, mul_pow, ← pow_mul, ← pow_mul] at hW
    have : ((v₁ ^ N : Wˣ) : W) * ϖ ^ (m * N) = ((u * v₂ ^ N : Wˣ) : W) * ϖ ^ (e + n * N) := by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hW, pow_add]
      ring
    exact IsDiscreteValuationRing.unit_mul_pow_congr_pow hϖ hϖ _ _ _ _ this
  refine ⟨T', algebraMap T.V W, κ, e, ϖ, hinj, hloc, hϖ, hκ, ?_, ?_⟩
  · have : N ∣ e + n * N := ⟨m, by rw [← he, mul_comm]⟩
    exact (Nat.dvd_add_left (Dvd.intro_left n rfl)).1 this
  · exact ⟨u⁻¹, by
      show algebraMap T.V W ϖ₀ * ((u⁻¹ : Wˣ) : W) = ϖ ^ e
      rw [hu, mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩

section Level

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Level

section Level2

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Level2
section Main

open GlobalTheory.TorusExt GlobalTheory.QkNumberField GlobalTheory.ArcPull

end Main

end GlobalTheory.ArcExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstIntegralCoordsLatticeSection
set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

set_option autoImplicit false in
private theorem exists_pos_int_combination_eq_zero_near_of_linearIndependent {g r : ℕ} {l₁ : Fin r → Fin g → ℂ}
    (hl : LinearIndependent ℝ l₁) :
    ∃ δ > 0, ∀ l : Fin r → Fin g → ℂ, ‖l - l₁‖ < δ → ∀ c : Fin r → ℤ,
      ‖∑ j, c j • l j‖ < δ → c = 0 := by
  set L : (Fin r → ℝ) →ₗ[ℝ] (Fin g → ℂ) := Fintype.linearCombination ℝ l₁ with hL
  have hLapp : ∀ x, L x = ∑ j, x j • l₁ j := fun x => by
    simp [hL, Fintype.linearCombination_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact funext (Fintype.linearIndependent_iff.1 hl x (by rw [← hLapp]; exact hx))
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  set k : ℝ := (K : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  have hbound : ∀ x, ‖x‖ ≤ k * ‖L x‖ := fun x => by
    have h := hK.le_mul_dist x 0
    simp only [map_zero, dist_zero_right] at h
    nlinarith [norm_nonneg (L x)]
  refine ⟨1 / (2 * k * ((r : ℝ) + 1)), by positivity, fun l hl c hc => ?_⟩
  set δ : ℝ := 1 / (2 * k * ((r : ℝ) + 1)) with hδ
  set x : Fin r → ℝ := fun j => (c j : ℝ) with hx
  have hcx : ∑ j, c j • l j = ∑ j, x j • l j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hx, Int.cast_smul_eq_zsmul]
  have hsplit : L x = ∑ j, x j • l j - ∑ j, x j • (l j - l₁ j) := by
    rw [hLapp]
    simp [smul_sub, Finset.sum_sub_distrib]
  have hsum : ‖∑ j, x j • (l j - l₁ j)‖ ≤ r * (‖x‖ * ‖l - l₁‖) := by
    calc ‖∑ j, x j • (l j - l₁ j)‖ ≤ ∑ j, ‖x j • (l j - l₁ j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin r, ‖x‖ * ‖l - l₁‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm x j) (by simpa using norm_le_pi_norm (l - l₁) j)
          (norm_nonneg _) (norm_nonneg _)
      _ = r * (‖x‖ * ‖l - l₁‖) := by simp
  have hLx : ‖L x‖ < δ + r * (‖x‖ * δ) := by
    rw [hsplit]
    calc ‖∑ j, x j • l j - ∑ j, x j • (l j - l₁ j)‖
        ≤ ‖∑ j, x j • l j‖ + ‖∑ j, x j • (l j - l₁ j)‖ := norm_sub_le _ _
      _ < δ + r * (‖x‖ * δ) := by
        have h1 : ‖∑ j, x j • l j‖ < δ := by rw [← hcx]; exact hc
        have h2 : r * (‖x‖ * ‖l - l₁‖) ≤ r * (‖x‖ * δ) := by
          gcongr
        linarith
  have hkδ : k * δ * ((r : ℝ) + 1) = 1 / 2 := by
    rw [hδ]; field_simp
  have hxlt : ‖x‖ < 1 := by
    have hb := hbound x
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hxn := norm_nonneg x
    have hδ0 : 0 < δ := by positivity
    have : ‖x‖ < k * δ + k * δ * r * ‖x‖ := by
      calc ‖x‖ ≤ k * ‖L x‖ := hb
        _ < k * (δ + r * (‖x‖ * δ)) := mul_lt_mul_of_pos_left hLx hk0
        _ = k * δ + k * δ * r * ‖x‖ := by ring
    have hkδ0 : 0 < k * δ := mul_pos hk0 hδ0
    have hkδ' : k * δ * r + k * δ = 1 / 2 := by rw [← hkδ]; ring
    have ha : k * δ * r ≤ 1 / 2 := by linarith
    have ha2 : k * δ ≤ 1 / 2 := by nlinarith
    have hm : k * δ * r * ‖x‖ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right ha hxn
    linarith
  funext j
  have hj : ‖x j‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm x j) hxlt
  have hj' : |(c j : ℝ)| < 1 := by simpa [hx] using hj
  have : |c j| < 1 := by exact_mod_cast hj'
  simpa using Int.abs_lt_one_iff.1 this

set_option autoImplicit false in
theorem _root_.GlobalTheory.ShFam.Hor.LogCh.exists_const_coords (n g r : ℕ) (B : Set (Fin n → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ)
    (hB : IsPreconnected B) (hlam : ContinuousOn lam B) (hζ : ContinuousOn ζ B)
    (hbas : ∀ b ∈ B, _root_.GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (K b) (lam b)) (hmem : ∀ b ∈ B, ζ b ∈ K b)
    (hb₀ : b₀ ∈ B) :
    ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  classical
  have hex : ∀ b ∈ B, ∃ m : Fin r → ℤ, ζ b = ∑ j, m j • lam b j :=
    fun b hb => ((hbas b hb).2 (ζ b)).1 (hmem b hb)
  let F : (Fin n → ℂ) → Fin r → ℤ := fun b => if hb : b ∈ B then (hex b hb).choose else 0
  have hF : ∀ b ∈ B, ζ b = ∑ j, F b j • lam b j := by
    intro b hb
    simp only [F, dite_eq_left hb]
    exact (hex b hb).choose_spec
  have hloc : ∀ b₁ ∈ B, ∀ᶠ b in 𝓝[B] b₁, F b = F b₁ := by
    intro b₁ hb₁
    obtain ⟨δ, hδ, hkey⟩ := exists_pos_int_combination_eq_zero_near_of_linearIndependent (hbas b₁ hb₁).1
    have h1 : ∀ᶠ b in 𝓝[B] b₁, ‖lam b - lam b₁‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖lam b - lam b₁‖) B b₁ :=
        ((hlam b₁ hb₁).sub continuousWithinAt_const).norm
      exact hc.eventually (eventually_lt_nhds (by simpa using hδ))
    have hcomb : Continuous (fun l : Fin r → Fin g → ℂ => ∑ j, F b₁ j • l j) :=
      continuous_finsetSum _ fun j _ => (continuous_apply j).const_smul (F b₁ j)
    have h2 : ∀ᶠ b in 𝓝[B] b₁, ‖ζ b - ∑ j, F b₁ j • lam b j‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖ζ b - ∑ j, F b₁ j • lam b j‖) B b₁ :=
        ((hζ b₁ hb₁).sub (hcomb.continuousAt.comp_continuousWithinAt (hlam b₁ hb₁))).norm
      refine hc.eventually (eventually_lt_nhds ?_)
      show ‖ζ b₁ - ∑ j, F b₁ j • lam b₁ j‖ < δ
      rw [← hF b₁ hb₁, sub_self, norm_zero]
      exact hδ
    filter_upwards [h1, h2, self_mem_nhdsWithin] with b hb1 hb2 hbB
    have hdiff : ∑ j, (F b - F b₁) j • lam b j = ζ b - ∑ j, F b₁ j • lam b j := by
      rw [hF b hbB]
      simp [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.1 (hkey (lam b) hb1 (F b - F b₁) (by rw [hdiff]; exact hb2))
  have hcont : ContinuousOn F B := fun b₁ hb₁ =>
    continuousWithinAt_const.congr_of_eventuallyEq (hloc b₁ hb₁) rfl
  refine ⟨F b₀, fun b hb => ?_⟩
  rw [← hB.constant hcont hb hb₀]
  exact hF b hb

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.AmpleFibres

theorem relAmple_restrict {S : Scheme.{0}} (U : S.Opens) [IsAffine U.toScheme] (B : Over S) {L : LB B.left}
    (hL : L.IsLB)
    (h : ReciprocityTheory.ChartRestriction.G.Out.RelAmple ((Over.pullback U.ι).obj B) (L.pull (pullback.fst B.hom U.ι))) :
    ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk (B.hom ∣_ U)) (L.pull (B.hom ⁻¹ᵁ U).ι) := by
  have hφ : (pullbackRestrictIsoRestrict B.hom U).inv ≫ pullback.fst B.hom U.ι = (B.hom ⁻¹ᵁ U).ι :=
    pullbackRestrictIsoRestrict_inv_fst B.hom U
  have hsq : IsPullback (pullbackRestrictIsoRestrict B.hom U).inv (Over.mk (B.hom ∣_ U)).hom
      ((Over.pullback U.ι).obj B).hom (𝟙 U.toScheme) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    simp [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hL₁ : (L.pull (pullback.fst B.hom U.ι)).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hL₂ : (L.pull (B.hom ⁻¹ᵁ U).ι).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hw : LBIso (L.pull (B.hom ⁻¹ᵁ U).ι)
      ((L.pull (pullback.fst B.hom U.ι)).pull (pullbackRestrictIsoRestrict B.hom U).inv) := by
    exact GenSpread.lbIso_pull_pull hL (pullbackRestrictIsoRestrict B.hom U).inv hφ.symm
  exact GlobalTheory.AmpleLocalBase.relAmple_baseChange hsq hL₁ hL₂ hw h

end GlobalTheory.AmpleFibres
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaScaledThreeValue
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayRosEx.ThetaPull

section Jets

variable {S : Type} [CommRing S] {ρ : Type}

end Jets

section Vals

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans
      (gm_val (κ ≫ r) w _ h _).symm))

end Vals

end GlobalTheory.RayRosEx.ThetaPull
end
end
