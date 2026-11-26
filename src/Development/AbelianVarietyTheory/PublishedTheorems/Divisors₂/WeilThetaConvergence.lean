module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def WeilThetaConvergence : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → (Formalism.MainNotions.SchurIrreducible.wittIdx V = 0 ∨ n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank) →
  ∀ θ : InfFam D, IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ Φ : schwartzA θ V.rank n, GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1 < ⊤

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.Whittaker

section Bridge

variable {k : Type} [Field k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem superDiag_eq_sum_pairs (g : GL (Fin N) k) :
    superDiag g = ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, g.val p.1 p.2 := by
  simp only [superDiag, Finset.sum_filter, Fintype.sum_prod_type]

theorem val_whitChar (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    ((GlobalTheory.LocGL.whitChar ψ N u : ℂˣ) : ℂ) = ψ (superDiag u.1) := by
  rw [superDiag_eq_sum_pairs]; rfl

theorem isGeneric_iff_isGenericFor (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    IsGeneric ψ π ↔ GlobalTheory.LocGL.IsGenericFor ψ π := by
  constructor
  · rintro ⟨l, hl, h⟩
    refine Submodule.Quotient.nontrivial_iff.2 fun htop => hl (LinearMap.ker_eq_top.1 (eq_top_iff.2 (htop ▸ ?_)))
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, val_whitChar, h u.1 u.2 v, sub_self]
  · intro h
    have h1 := Submodule.Quotient.nontrivial_iff.1 h
    obtain ⟨l, hl, hk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h1)
    refine ⟨l, hl, fun u hu v => ?_⟩
    have h2 := hk (Submodule.subset_span ⟨⟨u, hu⟩, v, rfl⟩)
    simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, val_whitChar] at h2
    exact sub_eq_zero.1 h2

theorem IsGeneric.of_surjective {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V}
    {σ : Representation ℂ (GL (Fin N) k) W} (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (h : IsGeneric ψ σ) :
    IsGeneric ψ π := by
  obtain ⟨l, hl, h⟩ := h
  refine ⟨l ∘ₗ f.toLinearMap, fun e => hl (LinearMap.ext fun w => ?_), fun u hu v => ?_⟩
  · obtain ⟨v, rfl⟩ := hf w
    exact LinearMap.congr_fun e v
  · exact (congrArg l (f.isIntertwining _ _ u v)).trans (h u hu _)

end Bridge

section Exact

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem isSmoothChar_whitChar {ψ : AddChar k Circle} (hψ : Continuous ψ) : IsSmoothChar (GlobalTheory.LocGL.whitChar ψ N) := by
  obtain ⟨r, hr⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  have hc : Continuous fun u : unipB k (Fin N) => superDiag u.1 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have h0 : superDiag ((1 : unipB k (Fin N)) : GL (Fin N) k) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj =>
      Matrix.one_apply_ne fun e => by have := (Finset.mem_filter.1 hj).2; rw [e] at this; omega
  refine (GlobalTheory.LocGL.whitChar ψ N).ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset
    (((GlobalTheory.SplitWeil.isOpen_cball r).preimage hc).mem_nhds ?_) fun u hu => Units.ext ?_)
  · rw [Set.mem_preimage, h0]
    simp [GlobalTheory.SplitWeil.cball]
  · rw [val_whitChar, hr _ hu]; rfl


end Exact

end GlobalTheory.Whittaker

namespace GlobalTheory.Published

open GlobalTheory.Whittaker

def CuspidalGeneric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) Circle), Continuous ψ → ψ ≠ 1 →
    GlobalTheory.Whittaker.IsGeneric ψ (π.locRep w)


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in
theorem cuspidalGeneric_holds : CuspidalGeneric := by
  intro E _ _ _ a _ P w ψ' hc' h1'
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  have := Submodule.nontrivial_iff_ne_bot.2 P.ne_bot
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : P.V)
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hgen : GlobalTheory.Whittaker.IsGeneric (locPsi hψ w) (P.locRep w) := by
    refine ⟨l, fun e => hne (by rw [e]; rfl), fun u hu v => ?_⟩
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  exact (isGeneric_iff_isGenericFor _ _).2 ((GlobalTheory.LocGL.isGenericFor_iff_of_continuous hcont hne1 hc' h1' _).1
    ((isGeneric_iff_isGenericFor _ _).1 hgen))

def GenericityGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (N c : ℕ) (m : Fin c → ℕ) (e : (Σ a, Fin (m a)) ≃ Fin N) (W : Type) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Levi k fun a => Fin (m a)) W), IsSmooth ρ → GlobalTheory.Whittaker.IsGeneric ψ (parInd e ρ) →
      ∃ l : Module.Dual ℂ W, l ≠ 0 ∧ ∀ u : Levi k fun a => Fin (m a), (∀ a, u a ∈ unipB k (Fin (m a))) →
        ∀ v, l (ρ u v) = (∏ a, (ψ (superDiag (u a)) : ℂ)) * l v

namespace GenericityGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GenericityGL

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def WeilSiegelFormula : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → 2 * n < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
  ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∀ Φ : schwartzA θ V.rank n,
    Eis.cosetSum (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1 =
      ⨍ q, AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def WeilEisensteinSiegelConvergence : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → 2 * n < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
  ∀ Φ : schwartzA θ V.rank n, Eis.CosetConv (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.Published.ChernDegreeComplexModel

variable (Y : Var ℂ)

theorem integrable {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) := by
  have : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  let R := AnRead.all Y.str (RingHom.id ℂ) Y.dim
  have hs : φ.IsSmooth R := (Weight.isCInf_iff_isSmooth R).1 h
  have hm := ReciprocityTheory.AnForm.M.mIntegrableCont R.finAtlas (fun _ => φ.locPot)
    (fun _ => Weight.isPotential_locPot hs) (fun _ => 1) continuous_const
  exact ((Weight.chernInt_eq_mInt R h measurable_const).1).2 hm

end GlobalTheory.Published.ChernDegreeComplexModel
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelEisensteinDoubled : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (B : Base F E) (n : ℕ), 1 ≤ n →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
  ∀ χ : Chr F E, IsHecke F E χ →
  ∀ (s₁ : ℂ) (φ : UA σ W₂.J → ℂ), φ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χ s₁ →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype
    let f : ℂ → UA σ W₂.J → ℂ := flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ s₁
    ∃ Ei : ℂ → UA σ W₂.J → ℂ,
      (∀ s : ℂ, (n : ℝ) / 2 < s.re → ∀ g,
        Eis.CosetConv P (ratU σ W₂.J) (f s) g ∧ Ei s g = Eis.cosetSum P (ratU σ W₂.J) (f s) g) ∧
      ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → UA σ W₂.J → ℂ), 0 < r ∧
        (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
        (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
        ContinuousOn (fun x : ℂ × UA σ W₂.J => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
        ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.Published

def SiegelWeilAnisotropicHermitian : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ B : Base F E, IsCharAF F B.ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ W : Spc F E n, (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
  ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
  ∀ X : Spc F E m, (∀ i j, σ (X.J j i) = X.J i j) → (∀ x, form σ X.J x x = 0 → x = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)) (Fin m × Fin (n + n)),
    (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : Fin m × Fin (n + n) → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : Rep σ X W₂, IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J) co χ 1 om →
  ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype (absE F E) K →
  ∀ Φ ∈ schA F (Fin m × Fin (n + n)), FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ X.J)) (𝓕 : Set (UA σ X.J)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) 𝓕 ν →
    let P : Subgroup (UA σ W₂.J) := siegelOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype
    let s₀ : ℂ := ((m : ℂ) - (n : ℂ)) / 2
    let f : ℂ → UA σ W₂.J → ℂ :=
      flatOf finSumFinEquiv (UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W₂.J)).subtype (absE F E) K (fun g => om (1, g) Φ 0) s₀
    (∀ g, IntegrableOn (fun h => theta om Φ h g) 𝓕 ν) ∧
    (∀ s : ℂ, (n : ℝ) / 2 < s.re →
      AutomorphicL2Unitary.LeftInv (P ⊓ ratU σ W₂.J) (f s) ∧ ∀ g, Eis.CosetConv P (ratU σ W₂.J) (f s) g) ∧
    ∀ g, Cont.HolValueAt (fun s => Eis.cosetSum P (ratU σ W₂.J) (f s) g) s₀
      ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, theta om Φ h g ∂ν)

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Formalism.UG

namespace GlobalTheory

namespace WeylCell

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def IsWeylRep (w : Equiv.Perm (Fin n)) (x : GL (Fin n) R) : Prop :=
  ∀ i j, i ≠ w j → (x : Matrix (Fin n) (Fin n) R) i j = 0

def cell (x : GL (Fin n) R) : Subgroup (GL (Fin n) R) :=
  unipB R (Fin n) ⊓ (unipBLower R (Fin n)).comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_unipBLower {g : GL (Fin n) R} :
    g ∈ unipBLower R (Fin n) ↔ (∀ i j, i < j → (g : Matrix (Fin n) (Fin n) R) i j = 0) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) R) i i = 1 := by
  refine (mem_unipRad (e := opp (points (Fin n)))).trans (and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ _ => ?_⟩)
  · exact (h i () ()).trans (by simp)
  · exact (h i).trans (by simp)

theorem mem_cell {x u : GL (Fin n) R} :
    u ∈ cell x ↔ u ∈ unipB R (Fin n) ∧ x⁻¹ * u * x ∈ unipBLower R (Fin n) := by
  simp [cell, Subgroup.mem_inf, Subgroup.mem_comap]

theorem isClosed_cell [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] (x : GL (Fin n) R) :
    IsClosed (cell x : Set (GL (Fin n) R)) := by
  have key : ∀ (f : GL (Fin n) R → GL (Fin n) R), Continuous f → ∀ i j (c : R),
      IsClosed {u | (f u : Matrix (Fin n) (Fin n) R) i j = c} := fun f hf i j c =>
    isClosed_eq ((Units.continuous_val.comp hf).matrix_elem i j) continuous_const
  have hc : Continuous fun u : GL (Fin n) R => x⁻¹ * u * x := by fun_prop
  have e : (cell x : Set (GL (Fin n) R)) =
      ((⋂ i, ⋂ j, ⋂ _ : j < i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | (u : Matrix (Fin n) (Fin n) R) i i = 1}) ∩
      ((⋂ i, ⋂ j, ⋂ _ : i < j, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = 0}) ∩
        ⋂ i, {u : GL (Fin n) R | ((x⁻¹ * u * x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i = 1}) := by
    ext u
    simp only [SetLike.mem_coe, mem_cell, mem_unipB, mem_unipBLower, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
  rw [e]
  refine ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ continuous_id i j 0).inter
    (isClosed_iInter fun i => key _ continuous_id i i 1)).inter
    ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => key _ hc i j 0).inter
    (isClosed_iInter fun i => key _ hc i i 1))


variable (R) in
abbrev permRep (w : Equiv.Perm (Fin n)) : GL (Fin n) R := (Matrix.permMatrixHom (R := R)).toHomUnits w

theorem permRep_apply (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permRep R w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp [Matrix.permMatrixHom, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.Perm.inv_def, Equiv.symm_apply_eq]

theorem isWeylRep_permRep (w : Equiv.Perm (Fin n)) : IsWeylRep w (permRep R w) := fun _ _ h => by
  rw [permRep_apply, if_neg h]

end Ring

def cSL (Q z : ℂ) : ℂ := (1 - Q⁻¹ * z) / (1 - z)

def cSU (q z : ℂ) : ℂ := (1 - (q ^ 2)⁻¹ * z) * (1 + q⁻¹ * z) / (1 - z ^ 2)

abbrev lo {n : ℕ} (i : Fin (n / 2)) : Fin n := Fin.castLE (Nat.div_le_self n 2) i

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def cellU {σ : L →+* L} {n : ℕ} (x : GU σ n) : Subgroup (GU σ n) :=
  (cell (x : GL (Fin n) L)).subgroupOf (GU σ n)

end Unitary

end WeylCell

namespace Published

open WeylCell

end Published

namespace WeylCell

theorem exists_haar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K N : Subgroup G}
    (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (hN : IsClosed (N : Set G))
    [MeasurableSpace N] [BorelSpace N] : ∃ μ : Measure N, μ.IsHaarMeasure ∧ μ (K.subgroupOf N) = 1 := by
  have h1 : IsOpen (K.subgroupOf N : Set N) := ho.preimage continuous_subtype_val
  have h2 : IsCompact (K.subgroupOf N : Set N) := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hc
  let P : TopologicalSpace.PositiveCompacts N := ⟨⟨_, h2⟩, by
    rw [show interior ((⟨_, h2⟩ : TopologicalSpace.Compacts N).carrier) = (K.subgroupOf N : Set N) from h1.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  haveI : LocallyCompactSpace N := h2.locallyCompactSpace_of_mem_nhds_of_group (h1.mem_nhds (one_mem _))
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

theorem exists_data_U {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (n : ℕ) (α : Fin (n / 2) → ℂˣ) (w : Equiv.Perm (Fin n))
    (hw : ∀ i, w i.rev = (w i).rev) :
    (∃ φ : GU σ n → ℂ, IsSphericalU q (fun i => (α i : ℂ)) φ ∧ φ 1 = 1) ∧
      (∃ x : GU σ n, x ∈ KU σ n ∧ IsWeylRep w (x : GL (Fin n) L)) ∧
      ∀ (x : GU σ n) [MeasurableSpace (cellU x)] [BorelSpace (cellU x)],
        ∃ μ : Measure (cellU x), μ.IsHaarMeasure ∧ μ ((KU σ n).subgroupOf (cellU x)) = 1 := by
  obtain ⟨ho, hc⟩ := LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n h
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) h (by omega) (by omega) (fun i => (α i : ℂ))
    fun i => (α i).ne_zero
  have hx : permRep L w ∈ GU σ n := by
    rw [LGrp.mem_GU_iff]
    intro i j
    rw [← map_inv, permRep_apply, permRep_apply, hw, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, Equiv.Perm.eq_inv_iff_eq, eq_comm (a := j)]
  refine ⟨⟨φ, hφ, h1⟩, ⟨⟨_, hx⟩, ⟨hx, permRep _ w, ?_⟩, isWeylRep_permRep w⟩,
    fun x _ _ => exists_haar ho hc ((isClosed_cell _).preimage continuous_subtype_val)⟩
  ext i j
  show (intL L).subtype ((permRep _ w).val i j) = (permRep L w).val i j
  simp only [permRep_apply, apply_ite (intL L).subtype, map_one, map_zero]

end WeylCell

end GlobalTheory

end
end
