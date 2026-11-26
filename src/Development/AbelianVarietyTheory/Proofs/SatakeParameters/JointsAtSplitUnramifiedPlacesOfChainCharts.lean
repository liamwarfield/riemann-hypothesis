module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplAlgLocAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockRowSubstitutionPreservesComplexSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanion
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanion
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseAtCompan

theorem mem_reL_symm {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin b → E))
    (x : Fin a → E) : x ∈ reL h.symm L ↔ reV h E x ∈ L := by
  subst h
  show x ∈ reL rfl L ↔ reV rfl E x ∈ L
  rw [reL_rfl, reV_rfl]

theorem mem_mvL_iff {E : Type} [Field E] [NumberField E] {N : ℕ} (co : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (y : Fin N → E) : (co : Matrix (Fin N) (Fin N) E) *ᵥ y ∈ mvL co Λ ↔ y ∈ Λ := by
  constructor
  · rintro ⟨z, hz, e⟩
    have e' : toLE co z = toLE co y := e
    rwa [(toLE co).injective e'] at hz
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem smul_mem_of_mem_compan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {R : Ranks} (sp : Spaces R F E) {σ : E →ₐ[F] E} (hσ : (σ : E →+* E) = (sp.cm.sig : E →+* E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (a : 𝓞 E)
    (y : Fin n → E) (hy : y ∈ compan (sp := sp) J a S.Lb) : (T : E) • y ∈ S.Lb := by
  let M : Submodule (𝓞 E) (Fin n → E) :=
    { carrier := {y | (T : E) • y ∈ S.Lb}
      add_mem' := fun {x z} hx hz => by
        show (T : E) • (x + z) ∈ S.Lb
        rw [smul_add]; exact add_mem hx hz
      zero_mem' := by show (T : E) • (0 : Fin n → E) ∈ S.Lb; rw [smul_zero]; exact zero_mem _
      smul_mem' := fun c x hx => by
        show (T : E) • (c • x) ∈ S.Lb
        rw [smul_comm]; exact S.Lb.smul_mem c hx }
  have hd : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) ≤ M := by
    rw [Submodule.span_le]
    intro z hz
    rw [← hσ] at hz
    exact S.Lb_dual z hz
  have hL : S.Lb ≤ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J S.Lb) := by
    intro x hx
    apply Submodule.subset_span
    have := S.Lb_int x hx
    rwa [hσ] at this
  exact hd (sup_le hL Submodule.smul_le_right hy)

theorem isBaseAt_inv_of_latCo : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  intro D X0 u w hg i hi T bad S co a hT hstd
  have hr := rankN D (i + 1) hi
  set C := compan (sp := D.sp) (gramN D (i + 1) hi) a S.Lb with hC
  have h1 : latAd (1 : GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) S.Lb = S.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one ⟨S.Lb_fin, S.Lb_span⟩
  have hm : mvL co C = StandardLatticesGL3.stdL D (D.R.N (i + 1)) := by
    rw [← hstd, GlobalTheory.TwU.latCo, h1]
  have hCi : ∀ y, y ∈ C ↔ ∀ k, ((co : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E) *ᵥ y) k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    rw [← mem_mvL_iff co C y, hm]
    unfold StandardLatticesGL3.stdL
    rw [Submodule.mem_pi]
    simp only [Set.mem_univ, true_imp_iff, Submodule.mem_one, RingHom.mem_range]
  have hTC : ∀ y ∈ C, (T : D.host.E) • y ∈ S.Lb :=
    smul_mem_of_mem_compan D.sp rfl S a
  refine IsBaseAt.congr X0 u w hg (isBaseAt_free X0 u w hg _ (reL (rankN D (i + 1) hi).symm C) fun x => ?_) fun w' hw => ?_
  · rw [mem_reL_symm, hCi]
    exact free_re (rankN D (i + 1) hi) co _ x
  · have hT' : ((T : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal :=
      natCast_notMem w' (D.what₂.places.resChar_prime w) hw hT
    refine (loc_lattice_eq_of_torsion_away w' _ _ T hT' ?_ ?_).symm
    · intro x hx
      rw [mem_reL_symm hr] at hx ⊢
      exact le_sup_left (a := S.Lb) hx
    · intro y hy
      rw [mem_reL_symm hr] at hy ⊢
      rw [map_smul]
      exact hTC _ hy

end GlobalTheory.BaseAtCompan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvCoordsIsBasisAtBaseLatticeOfStdCompanionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad) (co : GL (Fin (D.R.N (i + 1))) D.host.E) (a : 𝓞 D.host.E), ¬ (D.what₂.places.resChar w) ∣ T → GlobalTheory.TwU.latCo D.sp (gramN D (i + 1) hi) co a 1 S.Lb = StandardLatticesGL3.stdL D (D.R.N (i + 1)) → IsBaseAt X0 u w hg ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm co⁻¹) (reL (rankN D (i + 1) hi).symm S.Lb) := by
  first | exact @GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo | exact GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo | (intros; apply GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFractionRingGat
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ggeo.FracLocal

theorem isFractionRing_gat : ∀ {D : D7} (Gl : G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf :=
  fun {_} Gl u w hg => GlobalTheory.TwV.Lt.fracAt Gl u w hg

end GlobalTheory.Ggeo.FracLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiRatAllOfAdTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwUChiRat

open GlobalTheory.TwU _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV Formalism.UG NumberField IsDedekindDomain

section Gen

variable {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
  (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)
  (Rel : SB → (Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) → X.K → Prop)

theorem exists_isOver (Q : HeightOneSpectrum (𝓞 D.host.E)) : ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v Q := by
  refine ⟨⟨Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, ?_⟩, rfl⟩
  intro h
  have hN : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 D.host.F) ∈ Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hN
  have : Ideal.absNorm Q.asIdeal = 0 := by exact_mod_cast hN
  exact Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)

theorem chiRatAll_of_le (hLe : LocLe s lev fb dep Rel) (hChi : ChiIs s lev fb dep Rel)
    (hK : ∀ y : X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = s.σ₀ y) : ChiRatAll lev D.what₂.embLL := by
  classical
  intro κ
  have hv : ∀ P : SB, ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP s P.1) := fun P => exists_isOver (seamP s P.1)
  choose v hv using hv
  have hU := (lev.U_eq κ.1).1 κ.2
  have hgz : ∀ P : SB, ∃ g z, Rel P g z ∧ InFrame s fb dep P κ.1 g := fun P => hLe P (v P) (hv P) κ.1 hU.1 (hU.2 (v P))
  choose g z hgz using hgz
  have h1 := hChi κ g z hgz
  obtain ⟨k, hk⟩ := hK (∏ P, z P)
  refine ⟨k⁻¹, ?_⟩
  rw [map_inv₀, hk]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end Gen

theorem chiRatAll_of_adTie : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ) (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), GlobalTheory.TwU.AdTie A dtU a → (∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y) → ∀ i hi β, ChiRatAll ((St i hi).K β).lev D.what₂.embLL := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ St A dtU a H hK i hi β
  have hm := m_eq t μ
  rcases Nat.lt_or_ge t.m2 i with h | h
  · rcases Nat.lt_or_ge (t.m2 + 1) i with h' | h'
    · obtain rfl : i = t.m2 + 1 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levTop β).1 (H.levTop β).2 hK
    · obtain rfl : i = t.m2 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levCpl β).1 (H.levCpl β).2.2 hK
  · have hlt : i < D.R.m := by omega
    exact chiRatAll_of_le t.seam _ _ _ _ (H.levMid i hlt h β).1 (H.levMid i hlt h β).2.2 hK

end GlobalTheory.TwUChiRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemUnderSBOfGIdx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem not_mem_underSB_of_gIdx : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∀ v, GlobalTheory.TwU.UnderSB t μ v → ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ hQ v hv hmem
  classical
  obtain ⟨P, hP, hvP⟩ := hv
  have h1 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P).asIdeal := by
    have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈
        (seamP t.seam P).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hvP ▸ hmem
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have h2 : ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    rw [← mem_seamP t.seam P, map_natCast]
    exact h1
  rcases Finset.mem_union.1 hP with hG | hQE
  · obtain ⟨k, hk⟩ : ∃ k, P ∈ t.Pr.vG k := by
      rcases Finset.mem_union.1 hG with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    have hgk : ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.pr_ok.vG_norm k P hk]
      exact Ideal.absNorm_mem P.asIdeal
    have hnd : ¬ D.what₂.places.resChar w ∣ t.Pr.g k := by
      rw [t.g_rec]
      intro hd
      exact hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hg.1 (D.host.g_prime k)).1 hd) ▸ D.host.g_level k)
    have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) ((t.Pr.g k : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hnd)
    obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 t.X.E))
    have hone : (1 : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← hab]
      refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
      · simpa using h2
      · simpa using hgk
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)
  · exact hQ ((t.Q_rec μ _).2 ⟨hg.1, P, hQE, h2⟩)

end GlobalTheory.TwU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainCharts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SiteEx


set_option maxHeartbeats 4000000 in
theorem siteD_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ J hQ
  have hfr := GlobalTheory.Ggeo.FracLocal.isFractionRing_gat Gl u w hg
  have hrat := GlobalTheory.TwUChiRat.chiRatAll_of_adTie t u μ J.St J.A J.Hh.dt J.a J.tie J.kin
  have hpT : ∀ i (hi : i ≤ D.R.m), ¬ D.what₂.places.resChar w ∣ (J.St i hi).T := fun i hi => by
    rw [J.tie.T_eq i hi]; exact hg.2.2.2.2.2
  have hψ : ∀ i hi, PsiEx (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) := fun i hi =>
    psiEx_of (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) hfr (fun β => hrat (i + 1) hi β)
      (fun β => J.ord (i + 1) hi β)
  let Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ) :=
    { Fo := foOf J.Hh J.St J.val
      chFin := fun i hi => J.fin (i + 1) hi
      S := fun i hi =>
        { B := (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹
          B_lat := fun β => GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion J.Gd.herm u w hg hi ((J.St (i + 1) hi).K β).lev (J.A.crd (i + 1) hi) J.a
            (hpT (i + 1) hi) (J.base (i + 1) hi β)
          ψ := fun β => (hψ i hi β).choose
          fin := fun β => fin_of _ β _ } }
  refine ⟨Z, rfl, ⟨fun i hi => hpT (i + 1) hi, fun i hi w' hw' => ?_, fun i hi => trivial⟩, ⟨fun i hi => ?_, fun i hi β => ?_, fun i hi β cl => ?_⟩,
    fun i hi => ?_⟩
  · exact GlobalTheory.TwU.not_mem_underSB_of_gIdx t u w hg μ hQ w' (J.tie.bad (i + 1) hi w' hw')
  · show cT (sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 * gramN D (i + 1) hi *
      (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 = 1
    rw [MulEquiv.apply_symm_apply]
    exact std_of_C _ _ _ (J.pins.crd_orth (i + 1) hi)
  · exact (hψ i hi β).choose_spec
  · exact chRat_ofChiD J.chiD _ _ _
  · show Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹) = _
    exact MulEquiv.apply_symm_apply _ _

end GlobalTheory.SiteEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainChartsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparisonSiteData_over_chainCharts : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  first | exact @GlobalTheory.SiteEx.siteD_exists | exact GlobalTheory.SiteEx.siteD_exists | (intros; apply GlobalTheory.SiteEx.siteD_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepBasisSpansLatticeFirstFactorAtP
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepBasisSpansLatticeFirstFactorAtP
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.LbB

section Step

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [hcmp : Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}

theorem splAlg_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : GlobalTheory.TwV.SplAlg (locJ hi t B) := by
  intro v a
  exact (X.g u w hg).spl_alg _ _ a


set_option maxHeartbeats 400000 in
theorem lbAtB_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (hrat : FrRatJ t B) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E))
    (hL : L = reL (rankN D (i + 1) hi) Lb) : GlobalTheory.TwV.LbAtB (locJ hi t B) L := by
  rw [hL, reL_eq_map]
  exact lbAtB_of _ (locInt_locJ hi t B) (splAlg_locJ hi t B) _
    (frAtB_re (rankN D (i + 1) hi) (locJ hi t B) Lb B rfl (fun v => t.fr _ ((X.g u w hg).pl v).2)
      (fun v tt => t.fr_lat _ _ tt) (fun v => hrat _ _))

end Step

theorem lbAtB_inTw : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) j hj β, GlobalTheory.TwV.LbAtB (((Z.inTw Fl ht Gt).at' j hj).st.loc β) (((Z.inTw Fl ht Gt).at' j hj).st.K β).lev.Lb := by
  intro D X0 u w hg Tw μ Z Fl ht Gt j hj β
  set_option maxHeartbeats 16000000 in
   exact lbAtB_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B (Z.frRat Fl ht j hj β) _
    (reL_symm (rankN D (j + 1) hj) _).symm

end GlobalTheory.TwV.LbB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepBasisSpansLatticeFirstFactorAtPStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) j hj β, GlobalTheory.TwV.LbAtB (((Z.inTw Fl ht Gt).at' j hj).st.loc β) (((Z.inTw Fl ht Gt).at' j hj).st.K β).lev.Lb := by
  exact fun {D} X0 u w hg Tw μ Z Fl ht Gt =>
    @GlobalTheory.TwV.LbB.lbAtB_inTw D X0 u w hg Tw μ Z Fl ht Gt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonSiteChartsTwistsEqTupleChain
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonSiteChartsTwistsEqTupleChain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Port

theorem gl_one_eq_of_det_eq {R : Type*} [CommRing R] (g h : GL (Fin 1) R)
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : (g : Matrix (Fin 1) (Fin 1) R).det = (h : Matrix (Fin 1) (Fin 1) R).det := by
    have := congrArg Units.val e
    simpa using this
  ext i k
  rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
  simpa [Matrix.det_unique] using e'

theorem siteD_inTw_charts_tw : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : GlobalTheory.TwU.ChainCharts D u μ) (hv : ValAll Tw St), Z.Fo = foOf Hh St hv → (∀ j hj, St (j + 1) hj = GlobalTheory.TwU.StepCharts.ofStepIn ((Z.inTw Fl ht Gt).at' j hj).st) ∧ ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → (((Z.inTw Fl ht Gt).at' j hj).st.tw β).ch x = D.chiD (Hh.dt y) ^ cTw D (j + 1) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt Hh St hv hZ
  obtain ⟨Fo, fin, S⟩ := Z
  dsimp only at hZ
  subst hZ
  refine ⟨fun j hj => rfl, ?_⟩
  intro j hj β x y hy
  have hyx : y = detU D (j + 1) hj x := by
    apply Subtype.ext
    apply gl_one_eq_of_det_eq
    rw [det_detU]
    exact hy
  subst hyx
  rfl

end GlobalTheory.Port
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonSiteChartsTwistsEqTupleChainStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonSite_charts_twists_eq_tupleChain : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : GlobalTheory.TwU.ChainCharts D u μ) (hv : ValAll Tw St), Z.Fo = foOf Hh St hv → (∀ j hj, St (j + 1) hj = GlobalTheory.TwU.StepCharts.ofStepIn ((Z.inTw Fl ht Gt).at' j hj).st) ∧ ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → (((Z.inTw Fl ht Gt).at' j hj).st.tw β).ch x = D.chiD (Hh.dt y) ^ cTw D (j + 1) := by
  first | exact @GlobalTheory.Port.siteD_inTw_charts_tw | exact GlobalTheory.Port.siteD_inTw_charts_tw | (intros; apply GlobalTheory.Port.siteD_inTw_charts_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonDataStatementsAtSite
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonDataStatementsAtSite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HP


set_option maxHeartbeats 4000000 in
theorem cmpJHyp_inTw_site : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (T : ∀ u : D.what₂.Word, Forms0 D u) (c : LatCmp D), CmpTied D X0 T Gt c → FillTie Gt u w hg Fl → SiteGood Z → SiteRest Z c → CmpJHyp c (Z.inTw Fl ht Gt) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt T c K hF G A
  refine HypTiesI.hyp (X0 := X0) ⟨ht, hF, fun j hj => ⟨Z.Fo j hj, Z.loc Fl ht j hj, rfl, ?_⟩⟩ K
  exact
    { frRat := Z.frRat Fl ht j hj
      sameU := Z.sameU Fl ht j hj
      hypT := hypTJ_site Z Fl ht G.siteGood_prime_torsion G.bad_p j hj
      bad_p := G.bad_p j hj
      std := A.std j hj
      psi := A.psi j hj
      chRat := A.chRat j hj
      hypC := hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj
      ok := G.ok j hj
      siteGood_prime_torsion := G.siteGood_prime_torsion j hj
      Lb_eq := fun _ => (reL_symm (rankN D (j + 1) hj) _).symm }

end GlobalTheory.HP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparisonDataStatementsAtSiteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_data_statements_at_site : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (T : ∀ u : D.what₂.Word, Forms0 D u) (c : LatCmp D), CmpTied D X0 T Gt c → FillTie Gt u w hg Fl → SiteGood Z → SiteRest Z c → CmpJHyp c (Z.inTw Fl ht Gt) := by
  first | exact @GlobalTheory.HP.cmpJHyp_inTw_site | exact GlobalTheory.HP.cmpJHyp_inTw_site | (intros; apply GlobalTheory.HP.cmpJHyp_inTw_site <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMap
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Port


set_option maxHeartbeats 4000000 in
theorem site_labels_with_stepZero_classMap : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), Fl.mm = D.R.m → SiteGood Z → (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) → (D.chTw u μ).DGam ∣ (D.mem u).C.DGam → ∀ (one : OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y) (e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0), ∃ X : LabIn (Z.inTw Fl ht Gt), ∀ a (La : (D.gat u w hg).P.Tup), X.c0.cls a La = e0 (levelZeroClass one a La) := by
  intro D Gt c g u w hg Tw μ Z Fl ht hm G rat dgam one e0
  refine ⟨labOf ⟨fun _ _ => rfl, fun j hj => chX_stepInOf hj (Z.Fo j hj) (Z.loc Fl ht j hj) (Gt.gat_pos u w hg) (Z.sameU Fl ht j hj)
    (Z.frRat Fl ht j hj) (hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj), fillOK_of_empty (Z.lv_empty Fl ht)⟩ ht hm
    (clsAt0Of one e0 (fun c => Formalism.L2.G.Triv.card_stab (g.herm.lev0 u) D.host.g_prime D.host.g_ne c) _) rat dgam, fun a La => rfl⟩

end GlobalTheory.Port
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLabelsWithStepZeroClassMapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labIn_c0_cls_eq_levelZeroClass : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), Fl.mm = D.R.m → SiteGood Z → (∀ j, j < D.R.m → (Tw.fm u μ).KRat j) → (D.chTw u μ).DGam ∣ (D.mem u).C.DGam → ∀ (one : OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y) (e0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0), ∃ X : LabIn (Z.inTw Fl ht Gt), ∀ a (La : (D.gat u w hg).P.Tup), X.c0.cls a La = e0 (levelZeroClass one a La) := by
  intro D Gt c g u w hg Tw μ Z Fl ht hm good rat dgam one e0
  exact GlobalTheory.Port.site_labels_with_stepZero_classMap Gt c g u w hg Tw μ Z Fl ht hm good rat dgam one e0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Proof.LocOfSite

section Step

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [hcmp : Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}

theorem iw_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).iw v = (locAt X u w hg B0).iw v := rfl

theorem pl_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).pl v = (locAt X u w hg B0).pl v := rfl

theorem B_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : (locJ hi t B).B = reGL (rankN D (i + 1) hi) _ B := rfl

theorem splAlg_locJ' (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : GlobalTheory.TwV.SplAlg (locJ hi t B) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a

end Step

theorem splAlg_locAt {D : D7} (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B0 : GL (Fin D.R.k) D.host.E) :
    GlobalTheory.TwV.SplAlg (locAt X u w hg B0) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a


set_option maxHeartbeats 4000000 in
theorem loc_eq_step0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  intro D Gt c g u w hg Tw μ Z Fl ht
  refine ⟨fun j hj β v => ?_, fun j hj β v => ?_, fun j hj β β' => ?_, fun j hj => rfl, fun j hj β => ?_,
    splAlg_locAt g.herm u w hg g.cmp.B⟩
  · exact iw_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact pl_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B).trans
      (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β') hj ((Z.loc Fl ht j hj).t β') (Z.loc Fl ht j hj).B).symm
  · exact splAlg_locJ' (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B

end GlobalTheory.Proof.LocOfSite

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteLocalIdentificationsEqStepZeroStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_localIdentifications_eq_stepZero : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  exact @GlobalTheory.Proof.LocOfSite.loc_eq_step0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelStatementsOfJoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelStatementsOfJoint
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Port

theorem oneHyp_lev0At : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y := by
  intro D Gt c g u w hg h
  exact oneHyp_rec u w hg g.cmp h

end GlobalTheory.Port
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroLevelStatementsOfJointStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_zero_level_statements_of_joint : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → OneHyp ((g.forms u).cls0).toChart.lev (lev0At g u w hg).A ((g.forms u).cls0).toChart.y := by
  first | exact @GlobalTheory.Port.oneHyp_lev0At | exact GlobalTheory.Port.oneHyp_lev0At | (intros; apply GlobalTheory.Port.oneHyp_lev0At <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChTwDGamDvdMemDGam
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem chTw_DGam_dvd_mem_DGam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup), (D.chTw u μ).DGam ∣ (D.mem u).C.DGam := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ
  exact (ex.err.dgam.one u u μ).dvd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoprimeAbsNormCcKOfGIdx
open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem exists_prime_ge_dvd_absNorm {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] {p : ℕ} (hp : p.Prime) (I : Ideal S) (hI : I ≠ ⊥)
    (h : p ∣ Ideal.absNorm I) :
    ∃ P : Ideal S, P.IsPrime ∧ I ≤ P ∧ p ∣ Ideal.absNorm P := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ J hJ =>
    rw [Ideal.isUnit_iff.1 hJ, Ideal.absNorm_top] at h
    exact absurd (Nat.dvd_one.1 h) hp.one_lt.ne'
  | h₃ J P hJ hP ih =>
    rw [map_mul] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ⟨P, Ideal.isPrime_of_prime hP, Ideal.mul_le_left, h⟩
    · obtain ⟨Q, hQ, hle, hd⟩ := ih hJ h
      exact ⟨Q, hQ, Ideal.mul_le_right.trans hle, hd⟩

theorem coprime_absNorm_ccK_of_gIdx :
    ∀ (D : D7) (T p : ℕ), GIdx D.host T p → Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  intro D T p h
  obtain ⟨hp, -, hc, -⟩ := h
  have hj : jacobiSym (-(D.host.d : ℤ)) p ≠ 1 :=
    ((primeClass_eq_inert_iff _).1 hc).2.2.2.1
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨P, hP, hle, hdP⟩ := exists_prime_ge_dvd_absNorm hp _ D.host.ccK_ne_bot hd
  obtain ⟨h1, h2⟩ := D.host.ccK_split P hP hle
  rw [← (Nat.prime_dvd_prime_iff_eq hp h1).1 hdP] at h2
  exact hj h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtSplitUnramifiedPlacesOfChainCharts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 4000000 in
theorem jointsAt_of_jIn : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (μ : D.what₂.Tup), G.LatTied hT Gi Gl → (∀ u, Nonempty (JIn t u μ)) → GlobalTheory.TwV.JointsAt t μ := by
  intro D L hT Gi Gl Kc Dx cX ex t μ hlt hJ u w hg hw
  obtain ⟨J⟩ := hJ u
  have ht : (Gl.Fl u w hg).t = D.R.t := fl_t ex u w hg
  have hm : (Gl.Fl u w hg).mm = D.R.m := fl_mm_eq ex u w hg
  obtain ⟨Z, hFo, hgood, hrest, -⟩ := GlobalTheory.T.exists_comparisonSiteData_over_chainCharts t u w hg μ J hw
  have H : CmpJHyp ex.cmp (Z.inTw (Gl.Fl u w hg) ht hT) :=
    GlobalTheory.T.comparison_data_statements_at_site J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT (fun u => J.Gd.forms u) ex.cmp J.Gd.cmp (fillRec ex u w hg) hgood hrest
  have one := GlobalTheory.T.step_zero_level_statements_of_joint hT ex.cmp J.Gd u w hg J.joint0
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_labIn_c0_cls_eq_levelZeroClass hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht hm hgood J.rat
    (GlobalTheory.chTw_DGam_dvd_mem_DGam t u μ) one J.e0
  obtain ⟨hst, htw⟩ := GlobalTheory.T.comparisonSite_charts_twists_eq_tupleChain J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT J.Hh J.St J.val hFo
  obtain ⟨hiw, hpl, hB, hpos, halg, halg0⟩ := GlobalTheory.T.site_localIdentifications_eq_stepZero hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht
  refine ⟨Z.lv (Gl.Fl u w hg) ht, Z.inTw (Gl.Fl u w hg) ht hT, H, X, ⟨?_⟩⟩
  exact
  { Gd := J.Gd
    St := J.St
    A := J.A
    dtU := J.Hh.dt
    a := J.a
    pins := J.pins
    tie := J.tie
    st := fun j hj => hst j hj
    e0 := J.e0
    jointCmpEmbeddingY := J.jointCmpEmbeddingY
    e0Tw := J.e0Tw
    one := one
    cls0 := fun c La _ => hX c La
    lev0 := J.lev0
    ch0 := J.ch0
    y0 := J.y0
    fr0 := J.fr0
    iw := hiw
    oneB := hB
    pos := hpos
    tw := htw
    rel := J.rel
    base := J.base
    sharp := GlobalTheory.FormsSharpTie.formsSharpAt_of_pins t u μ J.St J.A J.Hh.dt J.pins (fun _ _ => True) (fun j hj => J.val j hj.le)
    dgen := t.O_dgen u μ ▸ (t.O u μ).dgen_gen
    tied := hlt
    away := hw
    cop := t.cc_rec ▸ GlobalTheory.coprime_absNorm_ccK_of_gIdx D _ _ hg
    empty := Z.lv_empty (Gl.Fl u w hg) ht
    alg := halg
    alg0 := halg0
    lbB := GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT
    lb0 := GlobalTheory.TwV.LbB.lbAtB_lev0At hT ex.cmp J.Gd u w hg J.joint0
    pl := hpl
    kin := J.kin }

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtSplitUnramifiedPlacesOfChainChartsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointsAtSplitUnramifiedPlaces_of_chainCharts : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (μ : D.what₂.Tup), G.LatTied hT Gi Gl → (∀ u, Nonempty (JIn t u μ)) → GlobalTheory.TwV.JointsAt t μ := by
  first | exact @GlobalTheory.TwV.jointsAt_of_jIn | exact GlobalTheory.TwV.jointsAt_of_jIn | (intros; apply GlobalTheory.TwV.jointsAt_of_jIn <;> assumption)
end
