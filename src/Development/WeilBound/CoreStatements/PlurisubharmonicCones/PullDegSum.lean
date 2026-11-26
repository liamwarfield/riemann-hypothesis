module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ProdSqrtLead
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDatumDegreeSum
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.HtLabelCongr
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Lat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V]

theorem patch_congr' (T : Finset ℕ) (L₀ : Lat ξ V) (Lp Lp' : ℕ → Lat ξ V)
    (h : ∀ p ∈ T, ∀ q, InFibre ξ p q → Lp p q = Lp' p q) : Lat.patch T L₀ Lp = Lat.patch T L₀ Lp' := by
  funext q
  simp only [Lat.patch]
  split_ifs with hF
  · refine iInf_congr fun p => iInf_congr fun hp => iInf_congr fun hq => ?_
    rw [h p hp q hq]
  · rfl

theorem vbOn_congr {L L' : Lat ξ V} {T : Set (Cpt ξ)} {r : ℕ} {U : Submodule Ω V} (h : ∀ q ∈ T, L q = L' q)
    (hL : L.IsVBOn T r U) : L'.IsVBOn T r U := by
  intro p hp
  obtain ⟨W, hW, b, hb, hf⟩ := hL p hp
  exact ⟨W, hW, b, hb, fun q hq hqW => ⟨(hf q hq hqW).1, (h q hq).symm.trans (hf q hq hqW).2⟩⟩

end Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem htLabel_congr {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) {n n' : ℕ}
    (ρ : 𝓞 E →+* Module.End Ω Li) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) (s : CMType H ⊕ CMType H) {q : Cpt ξ}
    (h : M.htOm L n q = M.htOm L n' q) : htLabel M L n ρ σ s q = htLabel M L n' ρ σ s q := by
  rcases s with τ | τ
  · simp only [htLabel, LieModel.htW, LieModel.htDual, h]
  · simp only [htLabel, LieModel.htDual, h]

section Level

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S₀ y) (S : Finset ℕ)

theorem patch_four (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q)
    (s : CMType H ⊕ CMType H) :
    Lat.patch S (𝔐.dR s) (fun p => htLabel 𝔐.M 𝔐.t.PP.L (p ^ 4) 𝔐.ρ 𝔐.emb s) = 𝔐.VS S s :=
  patch_congr' _ _ _ _ fun p hp q hq => htLabel_congr _ _ _ _ _ (h p hp q hq)

def levFour (hp : ∀ p ∈ S, p.Prime) (hR : ∀ p ∈ S, 4 ≤ 𝔐.R p) (ht : ∀ p ∈ S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p))
    (hvb : ∀ s, (𝔐.VS S s).IsVB (labelRk D s) (𝔐.Vgen s))
    (h : ∀ p ∈ S, ∀ q, InFibre 𝔐.ξ p q → 𝔐.M.htOm 𝔐.t.PP.L (p ^ 4) q = 𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p) q) :
    HodgeCpt Y S y :=
  { 𝔐 with
    S_prime := hp
    R := fun _ => 4
    R_ge := fun _ _ => le_rfl
    tors := fun p hpS k _ i g hg => ht p hpS k i g (by
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (hR p hpS)
      rw [hn, pow_add, pow_mul, hg, _root_.one_pow])
    vb := fun s => by
      have h1 := hvb s
      rw [← patch_four 𝔐 S h s] at h1
      exact h1 }

end Level

theorem pull_on {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω Ω' : Type} [Field Ω] [Field Ω'] {i : Ω →+* Ω'}
    {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
    {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'} (B : HodgeCpt Y S y) (A : HodgeCpt Y S y') (g : A.X ⟶ B.X)
    (x : Sp Ω ⟶ Xo.XF c) (hx : B.ξ ≫ B.f = x ≫ Y.j) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S)
    (hvb : ∀ p ∈ S, ∀ s, ((B.M.htOm B.t.PP.L (p ^ B.R p)).map (B.Vgen s).dualRestrict).IsVBOn {q | InFibre B.ξ p q}
      (labelRk D s) ⊤)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ B.ξ g i) (hf : g ≫ B.f = A.f) (hR : ∀ p ∈ S, A.R p = B.R p) :
    ∃ (j : B.Li →+ A.Li) (m : SABMap A.t B.t g), IsExtOver i j ∧
      (∀ a, (A.M.pt (j a)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (B.M.pt a).left) ∧
      ∀ s, A.V s = (B.V s).pull A.ξ g j := by
  obtain ⟨A', e, j', m', p1, p2, p3, p4, p5, p6, p7, -, p9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω' i K K' J J' y y' B x A.X A.ξ g hx hdisc hvb A.all A.tie (fun x => ⟨A.normal.1 x, A.normal.2 x⟩) hd
  have he : A.ξ ≫ e.symm.hom = A'.ξ := by
    rw [← p1]
    simp
  have hf' : e.symm.hom ≫ A'.f = A.f := by
    rw [p2, ← hf]
    simp
  have hc : A'.cst = A.cst := by
    refine OrLinked.ringHom_ext_int c (OrLinked.spMap_inj' ?_)
    rw [← A'.cst_over, ← A.cst_over, ← hf', ← he]
    simp only [Category.assoc]
  obtain ⟨φ, φt, -, φr, φp⟩ := OrLinked.same_base_cmp A' A e.symm he hf' hc
  have ha : (FrameRebase.sabRebase A.m hf.symm).φ = A.m.φ := FrameRebase.sabRebase_φ _ _
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t B.t A.t B.f g B.m (FrameRebase.sabRebase A.m hf.symm)
  rw [ha] at hk
  let j : B.Li →+ A.Li := φ.toLinearMap.toAddMonoidHom.comp j'
  have hjd : ∀ a, j a = φ (j' a) := fun _ => rfl
  have hj : IsExtOver i j := ⟨fun a v => by rw [hjd, hjd, p6.1, map_smul], fun n b hb =>
    (p6.2 n b hb).map' φ.toLinearMap φ.ker⟩
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ B.ξ (e.hom ≫ g) i := by
    show A'.ξ ≫ e.hom ≫ g = _
    rw [← Category.assoc, p1]
    exact hd
  refine ⟨j, k, hj, fun a => B.m.cart.1.hom_ext ?_ ?_, fun s => ?_⟩
  · show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.m.φ = _
    rw [Category.assoc, ← hk, φt, p3, ← Category.assoc, p7]
  · have w1 := Over.w (A'.M.pt (j' a))
    have w2 := Over.w (A.M.pt (φ (j' a)))
    have w3 : (A'.M.pt (j' a)).left ≫ A'.t.G.hom ≫ e.hom = (A.M.pt (φ (j' a))).left ≫ A.t.G.hom := by
      rw [← Category.assoc, w1, w2, ← p1]
      exact Category.assoc _ _ _
    show ((A.M.pt (φ (j' a))).left ≫ k.φ) ≫ B.t.G.hom = _
    rw [← p7, Category.assoc, Category.assoc, k.cart.1.w, m'.cart.1.w, ← Category.assoc, ← w3]
    simp only [Category.assoc]
  · funext q
    obtain ⟨hq, -, -⟩ := RegAtDom.regAt_dominates _ _ _ _ _ _ g i hd q
    obtain ⟨U, hU, b, -, hb⟩ := B.vb s ⟨g q.1, hq⟩ trivial
    have hb1 : (B.V s).IsFrameAt b ⟨g q.1, hq⟩ := hb _ trivial hU
    have h' := OrLinked.genPt_spec e.symm he q
    have e1 : (e.hom ≫ g) (e.symm.hom q.1) = g q.1 := by simp
    have hq' : genPt B.ξ ⤳ (e.hom ≫ g) (e.symm.hom q.1) := e1 ▸ hq
    have hb2 : (B.V s).IsFrameAt b ⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ := by
      have : (⟨(e.hom ≫ g) (e.symm.hom q.1), hq'⟩ : Cpt B.ξ) = ⟨g q.1, hq⟩ := Subtype.ext e1
      rw [this]
      exact hb1
    have hb3 := FlagPull.pull_isFrameAt hd' p6 ⟨e.symm.hom q.1, h'⟩ hq' hb2
    rw [← p9] at hb3
    have hb4 : (A.V s).IsFrameAt (fun k => φ (j' (b k))) q :=
      OrLinked.frame_tr φ (φr q h') (φp S (fun p hp => by rw [p5]; exact hR p hp) s q h') hb3
    exact hb4.2.trans (FlagPull.pull_isFrameAt hd hj q hq hb1).2.symm

end LevelTowerAlt.Comparison₂
end
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.RootIdxLast
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Det

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] {j : V →+ V'}

theorem map_comb (hj : IsExtOver i j) {r : ℕ} {s c : Fin r → V} {b₀ : Fin r → V'} {T : Matrix (Fin r) (Fin r) Ω}
    {T₁ : Matrix (Fin r) (Fin r) Ω'} (hT : ∀ k, c k = ∑ l, T l k • s l) (hT₁ : ∀ k, j (s k) = ∑ l, T₁ l k • b₀ l) (k : Fin r) :
    j (c k) = ∑ l, (T₁ * i.mapMatrix T) l k • b₀ l := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hT k, map_sum]
  simp only [hj.1, hT₁, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem det_pull' {L : Lat ξ V} {r : ℕ} {s : Fin r → V} {U : Submodule Ω V} (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i)
    (hj : IsExtOver i j) (hs : LinearIndependent Ω s) (hsU : ∀ k, s k ∈ U) (hL : L.IsVB r U)
    {b₀ : Fin r → V'} (hb₀ : LinearIndependent Ω' b₀) (hF : (L.pull ξ' f j).IsFlagVBOn Set.univ b₀) :
    ∃ T₁ : Matrix (Fin r) (Fin r) Ω', (∀ k, j (s k) = ∑ l, T₁ l k • b₀ l) ∧ T₁.det ≠ 0 ∧
      ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
        (detLat (L.pull ξ' f j) b₀).IsGenAt q (T₁.det * i t) := by
  let g : Cpt ξ' := ⟨genPt ξ', specializes_rfl⟩
  obtain ⟨hg, hgreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd g
  obtain ⟨U₀, hU₀, b, hb, hfr⟩ := hL ⟨f g.1, hg⟩ trivial
  have hbf := hfr _ trivial hU₀
  have hsU' : Submodule.span Ω (Set.range s) = U := by
    have : FiniteDimensional Ω U := hb ▸ FiniteDimensional.span_of_finite _ (Set.finite_range _)
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hsU k)) ?_
    rw [finrank_span_eq_card hs, ← hb, finrank_span_eq_card hbf.1]
  have hjb : ∀ k, j (b k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨U₁, hU₁, b', hb', hfr'⟩ := hF g trivial
    have e1 : ∀ c : Fin r → V', flagStep Ω' c r = Submodule.span Ω' (Set.range c) := fun c => by
      unfold flagStep
      congr 1
      ext x
      simp
    rw [← e1, ← hb', e1]
    have h1 : j (b k) ∈ (L.pull ξ' f j) g := by
      rw [(FlagPull.pull_isFrameAt hd hj g hg hbf).2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [(hfr' g trivial hU₁).2] at h1
    exact Submodule.span_le_restrictScalars (regAt ξ' g) Ω' _ h1
  have hjs : ∀ k, j (s k) ∈ Submodule.span Ω' (Set.range b₀) := by
    intro k
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := s) (s := b) fun k => by rw [hb]; exact hsU k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT k, map_sum]
    exact Submodule.sum_mem _ fun k' _ => by rw [hj.1]; exact Submodule.smul_mem _ _ (hjb k')
  obtain ⟨T₁, hT₁⟩ := exists_mat hjs
  have main : ∀ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (detLat L s).IsGenAt ⟨f q.1, h⟩ t ∧
      (detLat (L.pull ξ' f j) b₀).IsGenAt q (T₁.det * i t) := by
    intro q h
    obtain ⟨U₂, hU₂, c, hc, hcf⟩ := hL ⟨f q.1, h⟩ trivial
    have hcf' := hcf _ trivial hU₂
    obtain ⟨T, hT⟩ := exists_mat (Ω := Ω) (b := c) (s := s) fun k => by
      rw [hsU', ← hc]; exact Submodule.subset_span ⟨k, rfl⟩
    refine ⟨T.det, GlobalTheory.T.det_lattice_frame_gen X Ω ξ V L r s c T _ hs hcf' hT, ?_⟩
    have h2 := GlobalTheory.T.det_lattice_frame_gen X' Ω' ξ' V' (L.pull ξ' f j) r b₀ (fun k => j (c k)) (T₁ * i.mapMatrix T) q hb₀
      (FlagPull.pull_isFrameAt hd hj q h hcf') (map_comb hj hT hT₁)
    rwa [Matrix.det_mul, ← RingHom.map_det] at h2
  obtain ⟨t, -, ht⟩ := main g hg
  exact ⟨T₁, hT₁, left_ne_zero_of_mul ht.1, main⟩

variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)]
  {κ : K → K'} {v : (Σ k, J k) → Σ k, J' k} {y : (Σ k, J k) → Ω} {y' : (Σ k, J' k) → Ω'}

theorem deg_pull' {I : Type} [Fintype I] {Λ : I → Lat ξ Ω} {Λ' : I → Lat ξ' Ω'} {u : I → Ω'} (hu : ∀ τ, u τ ≠ 0)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hg' : IsCptGen ξ')
    (hcov : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p)
    (hΛ : ∀ τ (q : Cpt ξ') (h : genPt ξ ⤳ f q.1), ∃ t, (Λ τ).IsGenAt ⟨f q.1, h⟩ t ∧ (Λ' τ).IsGenAt q (u τ * i t))
    (hv : IsBlockMap κ v) (hy : ∀ q, y' (v q) = i (y q)) {a : K → ℤ} {e₀ : Ω}
    (h : (Lat.tens Λ fun _ => -1).IsDegOn Set.univ y a e₀) :
    (Lat.tens Λ' fun _ => -1).IsDegOn Set.univ y' (pullDeg κ a) ((∏ τ, u τ)⁻¹ * i e₀) := by
  have hU : ∏ τ, u τ ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hu τ
  refine ⟨mul_ne_zero (inv_ne_zero hU) ((map_ne_zero i).2 h.1), fun q _ c' hc' => ?_⟩
  obtain ⟨hq, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q
  obtain ⟨d, hdv⟩ := FlagPull.exists_chart hv c'
  obtain ⟨r1, r2⟩ := FlagPull.ratio_reg hv hy hc' hdv
  have hc := FlagPull.inChart_of_pull hd hg' hcov q hq r1 r2
  choose t ht ht' using fun τ => hΛ τ q hq
  have g1 := uMap hreg (gen_unit (deg_gen h hc) (Flag.tens_gen Λ (fun _ => -1) _ t ht))
  have g2 := Flag.tens_gen Λ' (fun _ => -1) q _ ht'
  refine (gen_of_unit (s := (∏ k', y' ⟨k', c' k'⟩ ^ pullDeg κ a k') * ((∏ τ, u τ)⁻¹ * i e₀)) g2 ?_).2
  convert g1 using 1
  rw [FlagPull.monomial_pull hv hy a hdv]
  simp only [_root_.zpow_neg_one, mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib, map_div₀, map_mul, map_inv₀, map_prod i (s := Finset.univ (α := I))]
  field_simp

end Det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

def lastRoot (D : Datum H) (a : CMType H × Fin D.q) : CMType H × Fin (D.p + D.q) := (a.1, Fin.natAdd D.p a.2.rev)

theorem rootIdx_last (a : CMType H × Fin D.q) : HodgeCpt.rootIdx D (lastRoot D a) = ⟨.inr a.1, a.2⟩ := by
  unfold HodgeCpt.rootIdx lastRoot
  rw [dite_eq_right (by simp)]
  congr 1
  apply Fin.ext
  have := a.2.2
  simp only [Fin.val_natAdd, Fin.val_rev]
  omega

theorem rootSgn_last (a : CMType H × Fin D.q) : HodgeCpt.rootSgn D (lastRoot D a) = -1 := by
  simp [HodgeCpt.rootSgn, lastRoot]

theorem core (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (hB : Birational y) {e : CMType H × Fin (D.p + D.q) → Ω}
    (L : CMType H × Fin (D.p + D.q) → HermLine J) (hR : Fl.RootLines (fun r => (L r).a) e)
    (hH : ∀ r, Fl.IsHodgeLine r (e r) (L r))
    {X₂ : Scheme.{0}} (t₂ : SAB H X₂) {Ω₂ : Type} [Field Ω₂] {ξ₂ : Sp Ω₂ ⟶ X₂} (hξ₂ : IsCptGen ξ₂)
    {K₂ : Type} [Fintype K₂] {J₂ : K₂ → Type} [∀ k, Fintype (J₂ k)] {y₂ : (Σ k, J₂ k) → Ω₂}
    (hcov : ∀ p : Cpt ξ₂, ∃ c, InChart ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) c p)
    {Li₂ : Type} [AddCommGroup Li₂] [Module Ω₂ Li₂] (M₂ : LieModel t₂.G ξ₂ Li₂) (V₂ : CMType H → Lat ξ₂ Li₂)
    {g : 𝔐.X ⟶ X₂} {i : Ω₂ →+* Ω} (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ ξ₂ g i) (m : SABMap 𝔐.t t₂ g) (j : Li₂ →+ 𝔐.Li)
    (hj : IsExtOver i j)
    (hpt : ∀ a, (𝔐.M.pt (j a)).left ≫ m.φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M₂.pt a).left)
    (hV : ∀ τ, 𝔐.V (.inr τ) = (V₂ τ).pull 𝔐.ξ g j) (U : CMType H → Submodule Ω₂ Li₂) (hvb : ∀ τ, (V₂ τ).IsVB D.q (U τ))
    {n : ℕ} (hn : n = D.q) (s : CMType H → Fin n → Li₂) (hs : ∀ τ, LinearIndependent Ω₂ (s τ)) (hsU : ∀ τ k, s τ k ∈ U τ)
    (A₂ : HermLine J₂) (e₀ : Ω₂)
    (hdeg : (Lat.tens (fun τ => detLat (V₂ τ) (s τ)) fun _ => -1).IsDegOn Set.univ y₂ A₂.a e₀)
    {κ : K₂ → K} {v : (Σ k, J₂ k) → Σ k, J k} (hv : IsBlockMap κ v) (hy : ∀ q, y (v q) = i (y₂ q))
    (hmet : ∀ (z : Sp ℂ ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      ∃ (h : genPt ξ₂ ⤳ centre (z ≫ g)) (b : CMType H → Fin n → Li₂) (T : CMType H → Matrix (Fin n) (Fin n) Ω₂)
        (Γ : CMType H → Matrix (Fin n) (Fin n) ℂ),
        (∀ τ, (V₂ τ).IsFrameAt (b τ) ⟨centre (z ≫ g), h⟩ ∧ (∀ k, b τ k = ∑ k', T τ k' k • s τ k') ∧
          M₂.GramAt t₂.PP.L (z ≫ g) (b τ) (Γ τ) ∧ (Γ τ).PosDef) ∧
        SecNorm ξ₂ y₂ A₂ e₀ (z ≫ g) (fun p => w (v p)) (∏ τ, (T τ).det)⁻¹ (∏ τ, Real.sqrt (Γ τ).det.re)⁻¹)
    (A A' : HermLine J) (ha : A.a = ∑ a, (L (lastRoot D a)).a) (hh : ∀ w, A.h w = ∏ a, (L (lastRoot D a)).h w)
    (hA' : IsPullHerm κ v A₂ A') :
    IsoLineOn (mCoordIdeal y) {w | ∃ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z} A A' := by
  classical
  subst hn
  have hb₀ : ∀ σ, LinearIndependent Ω (Fl.b σ) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  choose T₁ hT₁ hu hmain using fun τ => det_pull' (L := V₂ τ) hd hj (hs τ) (hsU τ) (hvb τ) (hb₀ (.inr τ))
    (by rw [← hV]; exact Fl.sub _)
  have D2 := deg_pull' hu hd 𝔐.tie.gen hcov hmain hv hy hdeg
  simp only [← hV] at D2
  rw [← hA'.1] at D2
  have hU : ∏ τ, (T₁ τ).det ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hu τ
  have he₁ : ∏ a, e (lastRoot D a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => (hR _).1
  have D1 : (Lat.tens (fun τ => detLat (𝔐.V (.inr τ)) (Fl.b (.inr τ))) fun _ => -1).IsDegOn Set.univ y A.a
      (∏ a, e (lastRoot D a)) := by
    refine ⟨he₁, fun q _ ch hch => ?_⟩
    have g1 : ∀ τ k, ((𝔐.V (.inr τ)).gr (Fl.b (.inr τ)) k).IsGenAt q
        (((∏ b, y ⟨b, ch b⟩ ^ (L (lastRoot D (τ, k))).a b) * e (lastRoot D (τ, k))) ^ (-1 : ℤ)) := fun τ k => by
      have h := deg_gen (hR (lastRoot D (τ, k))) hch
      unfold HodgeCpt.Flag.rootLat at h
      rw [rootIdx_last, rootSgn_last] at h
      exact gen_untens (by norm_num) h
    have g2 := Flag.tens_gen (fun τ => detLat (𝔐.V (.inr τ)) (Fl.b (.inr τ))) (fun _ => -1) q _ fun τ => by
      rw [GlobalTheory.T.det_lattice_flag_tensor _ _ _ _ _ _ _ (hb₀ _) (Fl.sub _)]
      exact Flag.tens_gen _ _ q _ (g1 τ)
    rw [g2.2, ha, mono_sum _ (chart_ne hch), smul_eq_mul, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]
    simp only [_root_.zpow_neg_one, zpow_one, Finset.prod_inv_distrib, inv_inv]
    rfl
  set ρ : Ω := (∏ τ, (T₁ τ).det)⁻¹ * i e₀ / ∏ a, e (lastRoot D a) with hρ
  have hρe : ρ * ∏ a, e (lastRoot D a) = (∏ τ, (T₁ τ).det)⁻¹ * i e₀ := div_mul_cancel₀ _ he₁
  have hne : ∀ k, ∃ a, y ⟨k, a⟩ ≠ 0 := by
    obtain ⟨ch, hc⟩ := 𝔐.tie.cover ⟨genPt 𝔐.ξ, specializes_rfl⟩
    exact fun k => ⟨ch k, chart_ne hc k⟩
  obtain ⟨f₁, f₂, hfg, hval⟩ := GlobalTheory.T.degree_lattice_quotient_forms _ Ω 𝔐.ξ K J y Ω _ A.a A'.a _ ρ 𝔐.tie hB hne D1
    (by rw [smul_eq_mul, hρe]; exact D2)
  refine ⟨f₁, f₂, hfg, ?_⟩
  rintro w ⟨z, hzw, hzI⟩ u₁ u₂ huv hu₁
  have hq : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  obtain ⟨hp, b, T, Γ, hb, hsec⟩ := hmet z w hzw hzI
  obtain ⟨φ, hφ, hup⟩ := gram_up m hξ₂ 𝔐.tie.gen hd M₂ 𝔐.M j hpt z hq hp
  have hfl : ∀ τ, ∃ cc : Fin D.q → 𝔐.Li, (∀ k, flagStep Ω cc k = flagStep Ω (Fl.b (.inr τ)) k) ∧
      (𝔐.V (.inr τ)).IsFrameAt cc ⟨centre z, hq⟩ := fun τ => by
    obtain ⟨U₁, hU₁, cc, h1, h2⟩ := Fl.sub (.inr τ) ⟨centre z, hq⟩ trivial
    exact ⟨cc, h1, h2 _ trivial hU₁⟩
  choose cc hcf hcv using hfl
  have hjb : ∀ τ, (𝔐.V (.inr τ)).IsFrameAt (fun k => j (b τ k)) ⟨centre z, hq⟩ := fun τ => by
    rw [hV]
    exact FlagPull.pull_isFrameAt hd hj ⟨centre z, hq⟩ hp (hb τ).1
  choose P hP hPu using fun τ => frame_mat (regAt 𝔐.ξ ⟨centre z, hq⟩) (hcv τ).1 ((hjb τ).2.symm.trans (hcv τ).2)
  have hCd : ∀ τ, ((P τ).map φ).det ≠ 0 := fun τ => by
    have := ((hPu τ).map φ).ne_zero
    rwa [RingHom.map_det] at this
  have hpd : ∀ τ, (((P τ).map φ)ᴴ * Γ τ * (P τ).map φ).PosDef := fun τ =>
    (hb τ).2.2.2.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hCd τ))))
  choose tt htt using fun τ (k : Fin D.q) => GrNorm.exists_sub_mem_flagStep (b := Fl.b (.inr τ)) k (x := cc τ k) (by
    rw [← hcf]
    exact Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩)
  let ν : CMType H × Fin D.q → ℝ := fun a => Real.sqrt (leadMinor (((P a.1).map φ)ᴴ * Γ a.1 * (P a.1).map φ) (a.2 + 1) /
    leadMinor (((P a.1).map φ)ᴴ * Γ a.1 * (P a.1).map φ) a.2)
  have s0 : ∀ a : CMType H × Fin D.q, SecNorm 𝔐.ξ y (L (lastRoot D a)) (e (lastRoot D a)) z w (tt a.1 a.2)⁻¹ (ν a)⁻¹ := by
    intro a
    have h := hH (lastRoot D a) z w hzw hzI (tt a.1 a.2) (ν a)
    rw [rootIdx_last, rootSgn_last, _root_.zpow_neg_one, _root_.zpow_neg_one] at h
    exact h ⟨hq, cc a.1, _, hcf a.1, hcv a.1, htt a.1 a.2, hup _ _ _ _ _ (hb a.1).2.2.1 (hP a.1), hpd a.1, rfl⟩
  have s1 := secNorm_prod hq hzw s0 ha (hh w)
  have hcval : ValAt 𝔐.ξ z (∏ τ, ((P τ).det : Ω)) (∏ τ, ((P τ).map φ).det) := valAt_prod hq _ fun τ => by
    have := hφ (P τ).det
    rwa [RingHom.map_det] at this
  have s2 := RootIso.secNorm_scale (HodgePull.secNorm_pull hd hv hy hA' hq hzw hsec hcval
    (Finset.prod_ne_zero_iff.2 fun τ _ => hCd τ) (-1)) (inv_ne_zero hU)
  have et : ∀ τ, ∏ k, tt τ k = (T₁ τ).det * i (T τ).det * ((P τ).det : Ω) := fun τ => by
    have hm := map_comb hj (hb τ).2.1 (hT₁ τ)
    refine (det_tri (r := D.q) (hb₀ (.inr τ)) (htt τ)
      (T₁ τ * i.mapMatrix (T τ) * (regAt 𝔐.ξ ⟨centre z, hq⟩).subtype.mapMatrix (P τ)) fun k => ?_).symm.trans ?_
    swap
    · rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]
      rfl
    · rw [hP τ k]
      simp only [hm, Finset.smul_sum, smul_smul, Matrix.mul_apply (N := (regAt 𝔐.ξ ⟨centre z, hq⟩).subtype.mapMatrix (P τ)),
        Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
      rw [mul_comm]
      rfl
  have eν : ∀ τ, ∏ k, ν (τ, k) = ‖((P τ).map φ).det‖ * Real.sqrt (Γ τ).det.re := fun τ =>
    (prod_sqrt_lead (hpd τ)).trans (sqrt_det_conj _ _)
  have e1 : ∏ a : CMType H × Fin D.q, (tt a.1 a.2)⁻¹ =
      (∏ τ, (T₁ τ).det)⁻¹ * ((∏ τ, ((P τ).det : Ω)) ^ (-1 : ℤ) * i (∏ τ, (T τ).det)⁻¹) := by
    rw [Finset.prod_inv_distrib, Fintype.prod_prod_type]
    simp only [et, Finset.prod_mul_distrib, map_inv₀, map_prod, _root_.zpow_neg_one, mul_inv]
    ring
  have e2 : ∏ a, (ν a)⁻¹ = ‖∏ τ, ((P τ).map φ).det‖ ^ (-1 : ℤ) * (∏ τ, Real.sqrt (Γ τ).det.re)⁻¹ := by
    rw [Finset.prod_inv_distrib, Fintype.prod_prod_type]
    simp only [eν, Finset.prod_mul_distrib, norm_prod, _root_.zpow_neg_one, mul_inv]
  rw [← e1, ← e2, ← hρe] at s2
  have hνpos : 0 < ∏ a, (ν a)⁻¹ := Finset.prod_pos fun a _ => inv_pos.2 (Real.sqrt_pos.2
    (div_pos (leadMinor_pos_of_posDef (hpd a.1) a.2.2) (leadMinor_pos_of_posDef (hpd a.1) a.2.2.le)))
  have key := GlobalTheory.T.section_norm_isomorphic_lines _ Ω _ K J y A A' _ ρ _ f₁ f₂ u₁ u₂ _ w _ 𝔐.tie.gen hzw he₁ hfg hval s1 s2 hνpos huv hu₁
  have hA := A.pos w fun k => (hzw.1 k).imp fun _ hc => hc.ne_zero
  have hu' : ‖evC w u₁‖ ≠ 0 := norm_ne_zero_iff.2 hu₁
  show (0 : ℝ) = Real.log (‖evC w u₂‖ / ‖evC w u₁‖ * A'.h w / A.h w)
  have : ‖evC w u₂‖ / ‖evC w u₁‖ * A'.h w / A.h w = 1 := by
    rw [div_mul_eq_mul_div, key]
    field_simp
  rw [this, Real.log_one]

end LevelTowerAlt.Comparison₂
end
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.JoinNormal
open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (blockFnField)
open PositivityTheory.UnitarySelfGeneration.JN

namespace LevelTowerAlt.Comparison₂

theorem join_normal {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₁ Ω₂ Ω : Type} [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω)
    (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) {X₁ X₂ : Scheme.{0}}
    (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂) (ha₁ : IsArithVar (mCoordIdeal y₁) d)
    (hb₁ : Birational y₁) (hf₁ : FiniteDimensional i₁.fieldRange Ω) (hg₁ : ∀ q : X₁, genPt ξ₁ ⤳ q)
    (hg₂ : ∀ q : X₂, genPt ξ₂ ⤳ q) (ht₁ : CoordTie ℤ ξ₁ fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩)
    (ht₂ : CoordTie ℤ ξ₂ fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) :
    ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, J k)
      (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, J k) (y : (Σ k, J k) → Ω) (Z : Scheme.{0})
      (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧
      (∀ p, y (v₁ p) = i₁ (y₁ p)) ∧ (∀ p, y (v₂ p) = i₂ (y₂ p)) ∧ mCoordIdeal (y ∘ v₁) = mCoordIdeal y₁ ∧
      mCoordIdeal (y ∘ v₂) = mCoordIdeal y₂ ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧
      CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧
      GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0 := by
  obtain ⟨m, w, y, Z, ξ, h₁, h₂, e₁, e₂, -, hg, ht, hN, hd₁, hd₂⟩ :=
    GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join Ω₁ Ω₂ Ω i₁ i₂ K₁ K₂ ι₁ ι₂ y₁ y₂ X₁ X₂ ξ₁ ξ₂ (finite_of i₁ hf₁) hg₁ hg₂ ht₁ ht₂
  let J : K₁ ⊕ K₂ ⊕ Unit → Type := Sum.elim ι₁ (Sum.elim ι₂ fun _ => Fin m)
  have fin : ∀ k, Finite (J k) := by
    rintro (k | k | k)
    · change Finite (ι₁ k); infer_instance
    · change Finite (ι₂ k); infer_instance
    · change Finite (Fin m); infer_instance
  let inst : ∀ k, Fintype (J k) := fun k => Fintype.ofFinite _
  let v₁ : (Σ k, ι₁ k) → Σ k, J k := fun p => ⟨.inl p.1, p.2⟩
  let v₂ : (Σ k, ι₂ k) → Σ k, J k := fun p => ⟨.inr (.inl p.1), p.2⟩
  have hv₁ : IsBlockMap (ι' := J) Sum.inl v₁ := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have hv₂ : IsBlockMap (ι' := J) (fun k => .inr (.inl k)) v₂ := by
    refine ⟨fun _ _ h => Sum.inl_injective (Sum.inr_injective h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have y1 : y ∘ v₁ = fun p => i₁ (y₁ p) := funext fun p => e₁ p.1 p.2
  have y2 : y ∘ v₂ = fun p => i₂ (y₂ p) := funext fun p => e₂ p.1 p.2
  have hb : Birational (ι := J) y := birational_of_tie (ι := J) ht
  obtain ⟨c, hc⟩ := exists_chart (ι := J) ht
  obtain ⟨c₁, hc₁⟩ := exists_chart ht₁
  have F : (blockFnField (ι := J) y).toSubfield = (RingHom.id Ω).fieldRange :=
    blockFnField_eq (ι := J) (RingHom.id Ω) y hb c hc
  have F₁ : (blockFnField (y ∘ v₁)).toSubfield = i₁.fieldRange := by
    rw [y1]; exact blockFnField_eq i₁ y₁ hb₁ c₁ hc₁
  have fd : FiniteDimensional (blockFnField (y ∘ v₁)) Ω := by
    have : FiniteDimensional (blockFnField (y ∘ v₁)).toSubfield Ω := by rw [F₁]; exact hf₁
    exact this
  have I1 : mCoordIdeal (y ∘ v₁) = mCoordIdeal y₁ := by rw [y1, mCoordIdeal_map]
  have I2 : mCoordIdeal (y ∘ v₂) = mCoordIdeal y₂ := by rw [y2, mCoordIdeal_map]
  refine ⟨K₁ ⊕ K₂ ⊕ Unit, inferInstance, J, inst, Sum.inl, v₁, fun k => .inr (.inl k), v₂, y, Z, ξ, h₁, h₂, hv₁, hv₂,
    congrFun y1, congrFun y2, I1, I2, ?_, hb, hg, ht, hN, hd₁, hd₂, ?_⟩
  · exact GlobalTheory.T.isArithVar_of_block_algebraic K₁ ι₁ _ J Sum.inl v₁ Ω y d hv₁
      (fun k => ⟨c k, Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)⟩) (I1 ▸ ha₁)
      (fun t _ => Algebra.IsAlgebraic.isAlgebraic t)
  · rw [relfinrank_eq i₁ _ _ F₁ F]
    exact Module.finrank_pos.ne'

end LevelTowerAlt.Comparison₂
end

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Cmp
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace LevelTowerAlt.Comparison₂

section Last

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) [Fintype (CMType H)]

theorem prod_last {M : Type} [CommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∏ r, (if D.p ≤ (r.2 : ℕ) then F r else 1) = ∏ a, F (lastRoot D a) := by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.prod_eq_one (fun i _ => if_neg (by omega)), one_mul]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.prod_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

theorem sum_last {M : Type} [AddCommMonoid M] (F : CMType H × Fin (D.p + D.q) → M) :
    ∑ r, (if D.p ≤ (r.2 : ℕ) then F r else 0) = ∑ a, F (lastRoot D a) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fin.sum_univ_add]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  rw [Finset.sum_eq_zero (fun i _ => if_neg (by omega)), zero_add]
  simp only [le_add_iff_nonneg_right, zero_le, if_true]
  exact (Fintype.sum_equiv Fin.revPerm (fun a => F (lastRoot D (τ, a))) (fun j => F (τ, Fin.natAdd D.p j))
    (fun a => rfl)).symm

end Last

theorem pullDeg_sum {K K' I : Type} [Fintype I] {κ : K → K'} (hκ : Function.Injective κ) (a : I → K → ℤ) :
    pullDeg κ (∑ j, a j) = ∑ j, pullDeg κ (a j) := by
  funext x
  simp only [pullDeg, Finset.sum_apply]
  by_cases hx : ∃ y, κ y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [hκ.extend_apply, Finset.sum_apply]
  · simp only [Function.extend_apply' _ _ _ hx, Pi.zero_apply, Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in
theorem common (h₁ : LevelFree) (h₂ : MuHodge) : Common := by
  intro hG E _ _ _ _ H D Xo l c Y S RM Sys Fx oR II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B hS hdisc hvR hR4 hp hbg hsm hgood hgen
  classical
  subst hS
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := OrLinked.mono_int' c
  have czR : CharZero RM.Ω := charZero_of_injective_ringHom oR.𝔐.cst.injective
  obtain ⟨a1, a2, a3, a4⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hfree : ∀ p ∈ S₀ ∪ Dc.SB B, HT.HTFree Or.𝔐 p := fun p hp' => by
    rcases Finset.mem_union.1 hp' with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  have hlev : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ q, InFibre Or.𝔐.ξ p q →
      Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4) q = Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p) q := fun p hp' =>
    h₁ hG.2.2.2.2.2.2.1 E H D l (Xo l) c Y _ Ω K J Dc.y (Or.𝔐.withS _ a1 a2 a3 a4) p hp' (by omega) (hfree p hp')
  let B₄ := levFour Or.𝔐 _ a1 a2 a3 a4 hlev
  have hB₄ : ∀ s, B₄.V s = Or.𝔐.VS (S₀ ∪ Dc.SB B) s := patch_four Or.𝔐 _ hlev

  have eg : genPt oR.𝔐.ξ₀ = genPt Or.𝔐.ξ₀ := by
    have g1 := RegAtDom.map_genPt oR.𝔐.fn_over
    have g2 := RegAtDom.map_genPt (show GlobalTheory.CompanionTheory.Ar.Dominates oR.𝔐.ξ Fx.ξf oR.𝔐.f oR.g from oR.g_over)
    rw [hgen, ← g1, g2]
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso oR.𝔐.gen₀ Or.𝔐.gen₀ eg
  have hfin : letI := (Or.𝔐.fn.comp ψ.toRingHom).toAlgebra; Module.Finite oR.𝔐.Ω₀ Ω := by
    have f1 : Or.𝔐.fn.Finite := by
      let _ := Or.𝔐.fn.toAlgebra
      exact Module.finite_of_finrank_pos (Or.cover.2 ▸ Or.cover.1)
    exact RingHom.Finite.comp f1 (RingHom.Finite.of_surjective _ ψ.surjective)
  obtain ⟨Ω₃, _, i₁, i₂, hi, hf₁⟩ := OrLinked.exists_tensor_field oR.𝔐.Ω₀ RM.Ω Ω oR.𝔐.fn _ hfin
  have cz : CharZero Ω₃ := charZero_of_injective_ringHom i₁.injective
  have fd₁ : FiniteDimensional i₁.fieldRange Ω₃ := FiniteDimensional.of_finrank_pos (by
    rw [OrLinked.finrank_fieldRange]
    let _ := i₁.toAlgebra
    exact Module.finrank_pos)
  obtain ⟨K₃, _, ρ, _, κ₁, v₁, κ, v, y, Z, ξ, g₁, g₂, bm₁, bm₂, hy₁, hy₂, I1, I2, har, hbir, hall, htie, hnorm, hd₁, hd₂, hrk⟩ :=
    join_normal i₁ i₂ RM.y Dc.y _ oR.𝔐.ξ Or.𝔐.ξ RM.arith RM.birational fd₁ oR.𝔐.all Or.𝔐.all oR.𝔐.tie Or.𝔐.tie
  obtain ⟨x₁, hx₁'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l (Xo l) c _ _ Y _ RM.Ω RM.K RM.ι RM.y oR.𝔐 hmono
  obtain ⟨x₂, hx₂'⟩ := GlobalTheory.T.hodge_component_factor_point E H D l (Xo l) c _ _ Y _ Ω K J Dc.y Or.𝔐 hmono
  have hx₁ : oR.𝔐.ξ ≫ oR.𝔐.f = (spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    rw [Category.assoc, ← hx₁']; exact oR.𝔐.fn_over
  have hx₂ : Or.𝔐.ξ ≫ Or.𝔐.f = (spMap Or.𝔐.fn ≫ x₂) ≫ Y.j := by
    rw [Category.assoc, ← hx₂']; exact Or.𝔐.fn_over
  have hdisc' : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀ ∪ Dc.SB B := fun p h1 h2 =>
    Finset.mem_union_left _ (hdisc p h1 h2)
  obtain ⟨𝔐, a, j₁, m₁, q1, q2, q3, q4, q5, q6, q7, -, q9⟩ :=
    GlobalTheory.T.hodge_cpt_field_extension E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 _ Z ξ g₁ hx₁ hdisc'
      (fun p hp s => (hvR p hp).2 s) hall htie hnorm hd₁
  have hdom₁ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ oR.𝔐.ξ (a.hom ≫ g₁) i₁ := by
    show 𝔐.ξ ≫ a.hom ≫ g₁ = _
    rw [← Category.assoc, q1]
    exact hd₁
  have hdom₂ : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ Or.𝔐.ξ (a.hom ≫ g₂) i₂ := by
    show 𝔐.ξ ≫ a.hom ≫ g₂ = _
    rw [← Category.assoc, q1]
    exact hd₂
  have hf𝔐 : 𝔐.f = (a.hom ≫ g₁) ≫ oR.𝔐.f := by rw [q2, Category.assoc]
  obtain ⟨Fl, hbF, -, -, hlF⟩ := FlagPull.flag_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐
    (a.hom ≫ g₁) j₁ m₁ κ₁ v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 fd₁
  have hZ : g₂ ≫ Or.𝔐.f = g₁ ≫ oR.𝔐.f := by
    refine OrLinked.map_eq_of_generic hnorm hall Y.s Y.proj ?_
    have e1 : ξ ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hd₁
    have e2 : ξ ≫ g₂ = spMap i₂ ≫ Or.𝔐.ξ := hd₂
    have e3 : oR.𝔐.ξ ≫ oR.𝔐.f = spMap oR.𝔐.fn ≫ oR.𝔐.ξ₀ := oR.𝔐.fn_over
    have e4 : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
    rw [← Category.assoc, ← Category.assoc, e1, e2, Category.assoc, Category.assoc, e3, e4, ← hψ, ← Category.assoc,
      ← Category.assoc, ← Category.assoc, OrLinked.spMap_spMap', OrLinked.spMap_spMap', OrLinked.spMap_spMap', hi, RingHom.comp_assoc]
  have hvb₄ : ∀ p ∈ S₀ ∪ Dc.SB B, ∀ s, ((Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ 4)).map (Or.𝔐.Vgen s).dualRestrict).IsVBOn
      {q | InFibre Or.𝔐.ξ p q} (labelRk D s) ⊤ := fun p hp' s =>
    vbOn_congr (L := (Or.𝔐.M.htOm Or.𝔐.t.PP.L (p ^ Or.𝔐.R p)).map (Or.𝔐.Vgen s).dualRestrict) (fun q hq => by
      simp only [Lat.map]
      rw [hlev p hp' q hq]) ((hfree p hp').2 s)
  have hf₄ : (a.hom ≫ g₂) ≫ Or.𝔐.f = 𝔐.f := by rw [q2, Category.assoc, hZ]
  obtain ⟨j, m, hj, hpt, hV⟩ := pull_on (i := i₂) B₄ 𝔐 (a.hom ≫ g₂) _ hx₂ hdisc'
    hvb₄ hdom₂ hf₄ (fun p hp' => by rw [q5]; exact hR4 p hp')
  have hx : 𝔐.ξ ≫ 𝔐.f = (spMap i₁ ≫ spMap oR.𝔐.fn ≫ x₁) ≫ Y.j := by
    have e1 : 𝔐.ξ ≫ a.hom ≫ g₁ = spMap i₁ ≫ oR.𝔐.ξ := hdom₁
    rw [hf𝔐, ← Category.assoc, e1, Category.assoc, hx₁]
    simp only [Category.assoc]
  obtain ⟨β, d, hβ, hβn, hint⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l (Xo l) c _ _ Y _ Ω₃ K₃ ρ y 𝔐 _ hx hmono
  have hdown : ∀ (z : Sp ℂ ⟶ 𝔐.X) (w : (Σ k, ρ k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      CoordsAt Or.𝔐.ξ Dc.y (z ≫ a.hom ≫ g₂) (fun p => w (v p)) ∧ Or.𝔐.Interior (z ≫ a.hom ≫ g₂) := fun z w hw hz =>
    ⟨HodgePull.coordsAt_pull hdom₂ 𝔐.tie.gen Or.𝔐.tie.cover bm₂ hy₂ (𝔐.all _) (Or.𝔐.all _) hw,
      (abLocus_pullback abLocusOne Or.𝔐.t.semi m.cart.1 _).2 hz⟩
  refine ⟨K₃, inferInstance, ρ, inferInstance, κ₁, v₁, κ, v, Ω₃, inferInstance, cz, y, β, d, bm₁, bm₂, I1, I2, har, hβ, hβn,
    hrk, fun w hw hb hBd => ?_, fun L L' hL hL' => ?_⟩
  · obtain ⟨z, hz, hI⟩ := hint w hw hb
    obtain ⟨c1, c2⟩ := hdown z w hz hI
    exact (Or.bd _ _ c1).1 hBd c2
  obtain ⟨ch₀, hch₀⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  obtain ⟨n, f, cc, -, -, hsum, hloc⟩ := Hd.locally ch₀ hch₀.1
  obtain ⟨l₀⟩ : Nonempty (Fin n) := by
    by_contra h
    have := not_nonempty_iff.1 h
    simp at hsum
  obtain ⟨bb, -, lam, -, hΛ⟩ := hloc l₀
  have hs : ∀ τ k, ∃ z, z ∈ Or.𝔐.Vgen (Or.sm τ) ∧ Or.i τ (bb τ (tailIdx Dc.j_le_N k)) - z ∈ Or.𝔐.Vgen (Or.bg τ) := fun τ k => by
    obtain ⟨a, ha, z, hz, h⟩ := Submodule.mem_sup.1
      (Or.i_range τ ▸ LinearMap.mem_range_self (Or.i τ) (bb τ (tailIdx Dc.j_le_N k)))
    exact ⟨z, hz, by rw [← h, add_sub_cancel_right]; exact ha⟩
  choose s hs using hs
  obtain ⟨hsi, hdeg⟩ := GlobalTheory.T.intersection_datum_degree_sum E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hmet := h₂ hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B bb s _ hs hΛ
  have hn : Dc.N - Dc.j = D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · rw [h, Or.N_eq]; omega
    · rw [hbg] at h
      obtain ⟨τ⟩ : Nonempty (CMType H) := (GlobalTheory.T.cm_host_rank_bounds E H).2.1
      exact absurd (congrFun h τ) (by simp)
  simp only [hsm] at hs hdeg hmet
  choose Lp hLp using fun r => ((GlobalTheory.T.block_pullback_herm_line RM.K RM.ι K₃ ρ κ₁ v₁ bm₁).1 (oR.sing r)).exists
  have hroot : Fl.RootLines (fun r => (Lp r).a) fun r => i₁ (oR.e r) := by
    have h := hlF _ _ oR.lines
    have e : (fun r => (Lp r).a) = fun r => pullDeg κ₁ (RM.xdeg r) := funext fun r => by rw [(hLp r).1, oR.sing_deg]
    rwa [e]
  have hiso := core 𝔐 Fl hbir Lp hroot
    (fun r => HodgePull.hodgeLine_pull E H D l (Xo l) c _ _ Y _ RM.Ω Ω₃ i₁ RM.K K₃ RM.ι ρ RM.y y oR.𝔐 𝔐 (a.hom ≫ g₁) j₁ m₁ κ₁
      v₁ oR.Fl bm₁ hy₁ hdom₁ hf𝔐 q3 q4 q6 q7 q9 Fl hbF r _ _ _ (oR.hodge r) (hLp r))
    Or.𝔐.t Or.𝔐.tie.gen Or.𝔐.tie.cover Or.𝔐.M (fun τ => Or.𝔐.VS (S₀ ∪ Dc.SB B) (.inr τ)) hdom₂ m j hj hpt
    (fun τ => (hV _).trans (by rw [hB₄]; rfl)) (fun τ => Or.𝔐.Vgen (.inr τ)) (fun τ => a4 (.inr τ)) hn s hsi
    (fun τ k => (hs τ k).1) (muVert Hd B) _ hdeg bm₂ hy₂
    (fun z w hw hz => hmet _ _ (hdown z w hw hz).1 (hdown z w hw hz).2) L L' ?_ (fun w => ?_) hL'
  · obtain ⟨f₁, f₂, hf, hdef⟩ := hiso
    exact ⟨f₁, f₂, hf, fun w hw => hdef w (hint w hw.1 hw.2)⟩
  · rw [hL.1, ← sum_last D fun r => (Lp r).a]
    show pullDeg κ₁ (∑ r, muExp D.p r • (oR.sing r).a) = _
    rw [pullDeg_sum bm₁.1]
    refine Finset.sum_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [one_smul, (hLp r).1]
    · rw [zero_smul]
      funext k'
      unfold pullDeg
      by_cases h : ∃ k, κ₁ k = k'
      · obtain ⟨k, rfl⟩ := h
        rw [bm₁.1.extend_apply]
        rfl
      · rw [Function.extend_apply' _ _ _ h]
  · rw [hL.2, ← prod_last D fun r => (Lp r).h w]
    show ∏ r, (oR.sing r).h _ ^ muExp D.p r = _
    refine Finset.prod_congr rfl fun r _ => ?_
    unfold muExp
    split_ifs
    · rw [zpow_one, (hLp r).2]
    · rw [zpow_zero]

end LevelTowerAlt.Comparison₂
