module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open Matrix

namespace GlobalTheory.IwasawaAdelic

theorem cornerGL_entry {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i j : Fin a) :
    (cornerGL a s g).val i j
      = (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j) :=
  rfl

theorem cornerGL_entry_ne {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) {i j : Fin a} (h : i ≠ j) :
    (cornerGL a s g).val i j = s (g.val i j) := by
  rw [cornerGL_entry]; simp [Matrix.one_apply_ne h]

theorem cornerGL_entry_same {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S)
    (g : GL (Fin a) R) (i : Fin a) :
    (cornerGL a s g).val i i = 1 - s 1 + s (g.val i i) := by
  rw [cornerGL_entry]; simp

theorem stdBlocks_lt_of_lt {s r : ℕ} (d : Fin s → ℕ) (hd : ∑ i, d i = r) {a b : Fin s}
    (i : Fin (d a)) (j : Fin (d b)) (hba : b < a) : stdBlocks d hd ⟨b, j⟩ < stdBlocks d hd ⟨a, i⟩ := by
  let f : ℕ → ℕ := fun n => if h : n < s then d ⟨n, h⟩ else 0
  have key : ∀ c : Fin s, ∑ x : Fin c, d (Fin.castLE c.2.le x) = ∑ x ∈ Finset.range c, f x := by
    intro c
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℕ) < s := x.2.trans c.2
    simp only [f, hx, dif_pos]
    rfl
  rw [Fin.lt_def, stdBlocks_val, stdBlocks_val, key, key]
  have h1 : ∑ x ∈ Finset.range (b + 1), f x ≤ ∑ x ∈ Finset.range a, f x :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt hba))
  rw [Finset.sum_range_succ] at h1
  have h2 : f b = d b := by simp [f]
  have := j.2
  omega

theorem mem_parab_of_upper {R : Type} [CommRing R] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (b : GL (Fin N) R) (hb : (b : Matrix (Fin N) (Fin N) R).BlockTriangular id) :
    b ∈ parab R (stdBlocks n h) := by
  rw [mem_parab_iff]
  intro a a' i j hlt
  exact hb (stdBlocks_lt_of_lt n h i j hlt)

theorem exists_upper_mul_unitary (N : ℕ) (y : GL (Fin N) ℂ) :
    ∃ b : GL (Fin N) ℂ, (b : Matrix (Fin N) (Fin N) ℂ).BlockTriangular id ∧
      ∃ k : Matrix (Fin N) (Fin N) ℂ, k ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
        (y : Matrix (Fin N) (Fin N) ℂ) = b * k := by
  set A : Matrix (Fin N) (Fin N) ℂ := ((y⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hAdef
  have hyA : (y : Matrix (Fin N) (Fin N) ℂ) * A = 1 := by simp [hAdef]
  have hAdet : IsUnit A.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; exact (y⁻¹).isUnit
  have hdet : IsUnit (Aᴴ * A).det := by
    rw [det_mul, det_conjTranspose]; exact hAdet.star.mul hAdet
  obtain ⟨Q, u, hQ, hu, hudet, hA⟩ := GlobalTheory.QRDecomp.exists_qr N N A hdet
  letI := u.invertibleOfIsUnitDet hudet
  refine ⟨(Matrix.nonsingInvUnit u hudet)⁻¹, ?_, Qᴴ, ?_, ?_⟩
  · show (u⁻¹).BlockTriangular id
    exact Matrix.blockTriangular_inv_of_blockTriangular hu
  · rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 hQ
  · show (y : Matrix (Fin N) (Fin N) ℂ) = u⁻¹ * Qᴴ
    have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.1 hQ
    have h1 : (Q * u) * (u⁻¹ * Qᴴ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc u, Matrix.mul_nonsing_inv u hudet, Matrix.one_mul, hQQ]
    calc (y : Matrix (Fin N) (Fin N) ℂ) = (y : Matrix (Fin N) (Fin N) ℂ) * ((Q * u) * (u⁻¹ * Qᴴ)) := by
          rw [h1, Matrix.mul_one]
      _ = u⁻¹ * Qᴴ := by rw [← Matrix.mul_assoc, ← hA, hyA, Matrix.one_mul]

theorem ext_eval {ι : Type} {N : ℕ} {P Q : Matrix (Fin N) (Fin N) (ι → ℂ)}
    (hPQ : ∀ v, P.map (Pi.evalRingHom (fun _ : ι => ℂ) v) = Q.map (Pi.evalRingHom (fun _ : ι => ℂ) v)) :
    P = Q := by
  ext i j v; exact congrFun (congrFun (hPQ v) i) j

theorem exists_upper_mul_unitary_inf (E : Type) [Field E] (N : ℕ) (y : GL (Fin N) (Cinf E)) :
    ∃ b : GL (Fin N) (Cinf E), (b : Matrix (Fin N) (Fin N) (Cinf E)).BlockTriangular id ∧
      ∃ k : Kinf E N, y = b * Unitary.toUnits k := by
  let ev : InfinitePlace E → (Cinf E →+* ℂ) := fun v => Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v
  choose B hB K hK hyK using fun v => exists_upper_mul_unitary N (Matrix.GeneralLinearGroup.map (ev v) y)
  let bm : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (B v : Matrix (Fin N) (Fin N) ℂ) i j
  let bi : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j
  let km : Matrix (Fin N) (Fin N) (Cinf E) := fun i j v => K v i j
  have hbm : ∀ v, bm.map (ev v) = (B v : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hbi : ∀ v, bi.map (ev v) = (((B v)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := fun v => rfl
  have hkm : ∀ v, km.map (ev v) = K v := fun v => rfl
  have h1 : bm * bi = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have h2 : bi * bm = 1 := ext_eval fun v => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hbm, hbi]; simp
  have hkU : km ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff']
    refine ext_eval fun v => ?_
    have hs : (star km).map (ev v) = star (K v) := by
      ext i j; rfl
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hs, hkm]
    exact (Matrix.mem_unitaryGroup_iff').1 (hK v)
  refine ⟨⟨bm, bi, h1, h2⟩, ?_, ⟨km, hkU⟩, ?_⟩
  · intro i j hij
    funext v
    exact hB v hij
  · apply Units.ext
    refine ext_eval fun v => ?_
    show (y : Matrix (Fin N) (Fin N) (Cinf E)).map (ev v) = (bm * km).map (ev v)
    rw [Matrix.map_mul, hbm, hkm]
    exact hyK v

theorem infGL_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) :
    infGL E N = cornerGL N (GlobalTheory.CuspRep.sInf E) := rfl

theorem infGL_mem_unipRad (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (u : GL (Fin N) (Cinf E))
    (hu : u ∈ unipRad (Cinf E) (stdBlocks n h)) : infGL E N u ∈ unipRad (Ad E) (stdBlocks n h) := by
  rw [mem_unipRad] at hu ⊢
  obtain ⟨hP, hD⟩ := hu
  refine ⟨mem_parab_iff.2 fun a b i j hlt => ?_, fun a i j => ?_⟩
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he => by
      have := congrArg Sigma.fst ((stdBlocks n h).injective he)
      exact (ne_of_gt hlt) this
    rw [infGL_eq, cornerGL_entry_ne _ _ hne, mem_parab_iff.1 hP a b i j hlt, map_zero]
  · by_cases hij : i = j
    · subst hij
      rw [infGL_eq, cornerGL_entry_same, hD a i i]; simp
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he => by
        exact hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, cornerGL_entry_ne _ _ hne, hD a i j, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij,
        map_zero]

theorem infGL_leviEmb (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (h : ∑ i, n i = N) (l : ∀ i, GL (Fin (n i)) (Cinf E)) :
    infGL E N (leviEmb (Cinf E) (stdBlocks n h) l)
      = leviEmb (Ad E) (stdBlocks n h) (fun i => infGL E (n i) (l i)) := by
  have leviEmb_apply_same : ∀ (R : Type) [CommRing R] (l : ∀ i, GL (Fin (n i)) R) a i j,
      (leviEmb R (stdBlocks n h) l : Matrix (Fin N) (Fin N) R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨a, j⟩) = (l a : Matrix _ _ R) i j := by
    intro R _ l a i j
    simp [leviEmb, blockDiagonal'_apply_eq]
  have leviEmb_apply_ne : ∀ (R : Type) [CommRing R] (l : ∀ i, GL (Fin (n i)) R) {a b}, a ≠ b → ∀ i j,
      (leviEmb R (stdBlocks n h) l : Matrix (Fin N) (Fin N) R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) = 0 := by
    intro R _ l a b hab i j
    simp [leviEmb, blockDiagonal'_apply, hab]
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective q
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [infGL_eq, infGL_eq, cornerGL_entry_same, cornerGL_entry_same, leviEmb_apply_same]
    · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨a, j⟩ := fun he =>
        hij (by simpa using (stdBlocks n h).injective he)
      rw [infGL_eq, infGL_eq, cornerGL_entry_ne _ _ hne, cornerGL_entry_ne _ _ hij, leviEmb_apply_same]
  · have hne : stdBlocks n h ⟨a, i⟩ ≠ stdBlocks n h ⟨b, j⟩ := fun he =>
      hab (congrArg Sigma.fst ((stdBlocks n h).injective he))
    rw [leviEmb_apply_ne _ _ hab, infGL_eq, cornerGL_entry_ne _ _ hne, leviEmb_apply_ne _ _ hab, map_zero]

theorem iwasawa : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) := by
  intro E _ _ _ c N n h x
  obtain ⟨b, hb, k, hy⟩ := exists_upper_mul_unitary_inf E N (Matrix.GeneralLinearGroup.map (pInf E) x)
  let p : parab (Cinf E) (stdBlocks n h) := ⟨b, mem_parab_of_upper n h b hb⟩
  let l := leviProj (Cinf E) (stdBlocks n h) p
  have hLp : leviEmb (Cinf E) (stdBlocks n h) l ∈ parab (Cinf E) (stdBlocks n h) := by
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb, blockDiagonal'_apply, hab.ne']
  let Lp : parab (Cinf E) (stdBlocks n h) := ⟨leviEmb (Cinf E) (stdBlocks n h) l, hLp⟩
  have hproj : leviProj (Cinf E) (stdBlocks n h) Lp = l := by
    funext a
    ext i j
    simp [leviProj_apply, Lp, leviEmb, blockDiagonal'_apply_eq]
  let u : GL (Fin N) (Cinf E) := ((Lp⁻¹ * p : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E))
  have hu : u ∈ unipRad (Cinf E) (stdBlocks n h) := by
    apply (coe_mem_unipRad (Cinf E) (Lp⁻¹ * p)).2
    simp [hproj, l]
  have hbu : b = leviEmb (Cinf E) (stdBlocks n h) l * u := by
    change (p : GL (Fin N) (Cinf E)) = (Lp : GL (Fin N) (Cinf E)) * ((Lp⁻¹ * p : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E))
    simp
  set L := leviEmb (Cinf E) (stdBlocks n h) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩) with hL
  have hu' : L * u * L⁻¹ ∈ unipRad (Cinf E) (stdBlocks n h) := by
    let U : parab (Cinf E) (stdBlocks n h) := ⟨u, (mem_unipRad.1 hu).1⟩
    have hU : leviProj (Cinf E) (stdBlocks n h) U = 1 := (coe_mem_unipRad (Cinf E) U).1 hu
    change ((Lp * U * Lp⁻¹ : parab (Cinf E) (stdBlocks n h)) : GL (Fin N) (Cinf E)) ∈ _
    rw [coe_mem_unipRad, map_mul, map_mul, map_inv, hU, mul_one, mul_inv_cancel]
  refine ⟨infGL E N (L * u * L⁻¹), infGL_mem_unipRad E n h _ hu', fun i => infGL E (n i) (leviProj (Cinf E) (stdBlocks n h) ⟨b, mem_parab_of_upper n h b hb⟩ i), k, Matrix.GeneralLinearGroup.map (pFin E) x, ?_⟩
  rw [← infGL_leviEmb, ← hL]
  conv_lhs => rw [← infGL_mul_finGL x, hy]
  rw [hbu]
  simp only [map_mul, map_inv]
  group

end GlobalTheory.IwasawaAdelic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolicStatement
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGL_iwasawa_decomposition_standardParabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N) (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) := by
  first | exact @GlobalTheory.IwasawaAdelic.iwasawa | exact GlobalTheory.IwasawaAdelic.iwasawa | (intros; apply GlobalTheory.IwasawaAdelic.iwasawa <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (h γ₁ γ₂ : GA D V) (hγ₁ : γ₁ ∈ GQ V) (hγ₂ : γ₂ ∈ GQ V)
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (G₁ G₂ : Matrix (Fin r) (Fin r) D.host.E)
    (hG₁ : G₁ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hG₂ : G₂ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hL₁ : (L₁ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₁ * h) : Set _))
    (hL₂ : (L₂ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₂ * h) : Set _)) :
    ∃ γ : GL (Fin r) D.host.E,
      (L₁ : Set (Fin r → D.host.E)) = (γ : Matrix (Fin r) (Fin r) D.host.E).mulVec '' (L₂ : Set _) ∧
      (∀ v w, herm G₁ ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec v) ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec w) =
        herm G₂ v w) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ x : Matrix (Fin r) (Fin r) ℂ,
          Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₁ * h)) * x =
            (γ : Matrix (Fin r) (Fin r) D.host.E).map τ *
              (Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₂ * h)) * x) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG₁ hG₂
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V _ (mul_mem hγ₁ (inv_mem hγ₂))
  have hprod : γ₁ * γ₂⁻¹ * (γ₂ * h) * 1 = γ₁ * h := by group
  obtain ⟨ht1, -⟩ := GlobalTheory.ShortMoveIso.transport (finHom V) (latGHat V)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) 1 (γ₁ * γ₂⁻¹) (γ₂ * h) 1 rfl
  rw [hprod] at ht1
  have hmem : ∀ (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V),
      (L : Set (Fin V.rank → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast (rfl : V.rank = V.rank).symm) '' (latG V g : Set _) →
      ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g := fun L g hL v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ L₂ ↔ δ.1 *ᵥ v ∈ L₁ := fun v => by
    rw [hmem _ _ hL₂, hmem _ _ hL₁, ht1, hδf]
  refine ⟨δ, ?_, fun u v => ?_, fun τ θ hθ x => ?_⟩
  · ext v
    constructor
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
  · rw [hG₁, hG₂]
    exact hδu u v
  · have hmul : ∀ a b : GA D V, archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have e : γ₁ * h = γ₁ * γ₂⁻¹ * (γ₂ * h) := by group
    rw [hre, hre, e, hmul, hδa _ _ hθ, Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem frames_differ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨-, -, -, -, -, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, hL₂, -, hf₂⟩ := hd₂ h
  obtain ⟨γ, hl, hi, hf⟩ := move (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ _).1 (hW₂ _).1 hL₁ hL₂
  refine ⟨γ, hl, hi, fun τ t₂ t₁ => ?_⟩
  have e₂' := hf₂ ⟨τ, t₂⟩
  have e₁' := hf₁ ⟨τ, t₁⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
  rw [e₁', e₂']
  exact hf τ _ (hth₁ _ ⟨τ, t₁⟩) _

end GlobalTheory.CoverFrameMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometryStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_cover_frames_differ_by_rational_isometry : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  first | exact @GlobalTheory.CoverFrameMove.frames_differ | exact GlobalTheory.CoverFrameMove.frames_differ | (intros; apply GlobalTheory.CoverFrameMove.frames_differ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfFixedMemSpanTranslates
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.HeckeAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

theorem mem_conj {g : G} {t : K} :
    t ∈ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K ↔ g⁻¹ * (t : G) * g ∈ K := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, e⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem fix_eq {H : Subgroup K} {v : V} (hv : ∀ h ∈ H, ρ ((h : K) : G) v = v) {a b : K} (hab : (a : K ⧸ H) = b) :
    ρ (a : G) v = ρ (b : G) v := by
  have hm := QuotientGroup.eq.1 hab
  have : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
  rw [this, map_mul, Module.End.mul_apply, hv _ hm]

end GlobalTheory.HeckeAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OmRatInvApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.Move

variable {D : D7}

theorem heisO_eval_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w f 0 = f w := by
  have h : symplOH S T 0 w = 0 := by
    simp [symplOH, symplO, hO]
  simp [heisO, h]

theorem mt_one_eq (S : HSp D) : mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_eq (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by simp [Formalism.L2.Theta.mt]

theorem actO_one_left (V W : HSp D) (γ : GA D W) (w : WO V W) :
    actO V W 1 γ w = HMul.hMul (mt W γ) (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) := by
  unfold actO
  rw [inv_one, mt_one_eq, Matrix.mul_one]

theorem om_rat_actO {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ) f (actO V W 1 γ w) = f w := by
  have h1 := H.om_heis 1 γ w f hf
  have h2 := H.om_aut 1 (one_mem _) γ hγ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all H.std hf w)
  rw [← heisO_eval_zero ψ V W (actO V W 1 γ w) (om (1, γ) f), ← h1, h2, heisO_eval_zero]

theorem om_rat_inv_apply {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (H : IsWeilDatumO ψ V W χV χW om) {γ : GA D W}
    (hγ : γ ∈ GQ W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W) :
    om (1, γ⁻¹) f w = f (actO V W 1 γ w) := by
  have h := om_rat_actO H (inv_mem hγ) hf (actO V W 1 γ w)
  have e : actO V W 1 γ⁻¹ (actO V W 1 γ w) = w := by
    rw [actO_one_left, actO_one_left, ← Matrix.mul_assoc, ← mt_mul_eq, inv_mul_cancel, mt_one_eq, Matrix.one_mul]
  rwa [e] at h

theorem ratMul_eq_actO {V W : HSp D} {γ : GA D W} {c : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hc : mt W γ = c.map (incA D)) (u : WO V W) : ratMul c u = actO V W 1 γ u := by
  rw [actO_one_left, hc]
  rfl

theorem termMove : ∀ D : D7, TermMove D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr h f₁ f₂ h₁ h₂
  refine ⟨fun Y C hC => lagTerm_frame_indep D ψ V W μ 𝓕 h.covol h.weil.std f₁ f₂ h₁ h₂ Y C (fr Y) hC (h.frame Y),
    fun γ hγ c hc => ⟨fun C => ?_, ?_⟩⟩
  · unfold lagTerm
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [← ratMul_ratMul, ratMul_eq_actO hc, om_rat_actO h.weil hγ h₁]
  · unfold lagTerm thetaIP
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [ratMul_one, om_rat_inv_apply h.weil hγ h₂, ratMul_eq_actO hc, mul_comm]

end GlobalTheory.RawLift.Move
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDSingleLeviEmbEqZero
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.UnipZero

theorem mem_unipRad_of_eq_one {R : Type} [CommRing R] {c N : ℕ} {n : Fin c → ℕ}
    {e : (Σ i, Fin (n i)) ≃ Fin N} {p q : Fin N} (hpq : blk e p < blk e q) (u : GL (Fin N) R)
    (hu : ∀ i j, ¬ (i = p ∧ j = q) → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j) :
    u ∈ unipRad R e := by
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : ¬ (i = p ∧ j = q) := by
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hij hpq
    rw [hu i j hne, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  · have hne : ¬ (e ⟨a, i⟩ = p ∧ e ⟨a, j⟩ = q) := by
      rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [← h1, blk_apply]
      have h2' : blk e q = a := by rw [← h2, blk_apply]
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq
    rw [hu _ _ hne]
    simp [Matrix.one_apply, e.injective.eq_iff]

end GlobalTheory.UnipZero

namespace GlobalTheory.UnipZero

theorem lieD_single_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ}
    (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) e, ∀ g, ψ.1 (u * g) = ψ.1 g) (p q : Fin N) (hpq : blk e p < blk e q)
    (x : Cinf E) (m : ∀ i, GA E (n i)) :
    (lie E N (toL (Matrix.single p q x)) ψ).1 (leviEmb (Ad E) e m) = 0 := by
  set S : Matrix (Fin N) (Fin N) (Cinf E) := Matrix.single p q x with hS
  have hpq' : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
  have hSS : S * S = 0 := by rw [hS]; simp [hpq'.symm]
  let cc : ℝ → GL (Fin N) (Cinf E) := fun t =>
    ⟨1 + t • S, 1 - t • S, by
      rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel, by
      rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hSS, smul_zero]; abel⟩
  have h0 : cc 0 = 1 := Units.ext (by simp [cc])
  have hc : HasDerivAt (fun t => toL (cc t).val) (toL S) 0 := by
    have h : HasDerivAt (fun t : ℝ => toL (1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • toL S) ((1 : ℝ) • toL S) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const (toL S)).const_add _
    rw [one_smul] at h
    exact h
  set g := leviEmb (Ad E) e m
  have hmem : ∀ t, infGL E N (cc t) ∈ unipRad (Ad E) e := by
    intro t
    refine mem_unipRad_of_eq_one hpq _ fun i j hij => ?_
    have hij' : ((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j =
        (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j := by
      change ((1 : Matrix (Fin N) (Fin N) (Cinf E)) + t • S) i j = _
      have h1 : S i j = 0 := by
        rw [hS, Matrix.single_apply_of_ne]
        exact fun h => hij ⟨h.1.symm, h.2.symm⟩
      rw [Matrix.add_apply, Matrix.smul_apply, h1, smul_zero, add_zero]
    change (1 : Matrix (Fin N) (Fin N) (Ad E)) i j - sInf E ((1 : Matrix (Fin N) (Fin N) (Cinf E)) i j) +
      sInf E (((cc t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) i j) = _
    rw [hij', sub_add_cancel]
  have hconst : (fun t => ψ.1 (g * infGL E N (cc t))) = fun _ => ψ.1 g := by
    funext t
    have hconj : g * infGL E N (cc t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 (hmem t)
    have := hψ _ hconj g
    rwa [inv_mul_cancel_right] at this
  have hd := hasDerivAt_curve ψ g cc (toL S) h0 hc
  rw [hconst] at hd
  rw [lie_apply]
  exact hd.unique (hasDerivAt_const _ _)

end GlobalTheory.UnipZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumCardSubspaces
open scoped BigOperators

namespace GlobalTheory.GaussSubspace

theorem sum_card_subspaces :
    ∀ (k : Type) [Field k] [Finite k] (m : ℕ) (A : Type) [CommRing A] (Y : A), ∑ j ∈ Finset.range (m + 1), (-1 : A) ^ j * (Nat.card k : A) ^ (j * (j - 1) / 2) * (Nat.card {W : Submodule k (Fin m → k) // Module.finrank k W = j} : A) * Y ^ j = ∏ i ∈ Finset.range m, (1 - (Nat.card k : A) ^ i * Y) := by
  intro k _ _ m A _ Y
  rw [← GlobalTheory.GaussCount.gauss_formula (Nat.card k) A Y m]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := GlobalTheory.GaussCount.subspaceCount k (Fin m → k) j
  rw [Module.finrank_fin_fun] at h
  rw [h]

end GlobalTheory.GaussSubspace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSubspacesFinrankCongr
open scoped BigOperators

namespace GlobalTheory

open Module

theorem card_subspaces_le_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (p : Submodule k V) (j : ℕ) :
    Nat.card {U : Submodule k V // U ≤ p ∧ finrank k U = j} =
      Nat.card {U : Submodule k p // finrank k U = j} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun U => ⟨U.1.map p.subtype, Submodule.map_subtype_le p U.1, ?_⟩) ⟨?_, ?_⟩)
  · rw [Submodule.finrank_map_subtype_eq]; exact U.2
  · intro U U' h
    exact Subtype.ext (Submodule.map_injective_of_injective p.injective_subtype
      (congrArg Subtype.val h))
  · rintro ⟨U, hU, hj⟩
    have h : (U.comap p.subtype).map p.subtype = U := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hU]
    refine ⟨⟨U.comap p.subtype, ?_⟩, Subtype.ext h⟩
    rw [← Submodule.finrank_map_subtype_eq, h, hj]

theorem card_subspaces_finrank_congr {k V V' : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] (e : V ≃ₗ[k] V') (j : ℕ) :
    Nat.card {U : Submodule k V // finrank k U = j} =
      Nat.card {U : Submodule k V' // finrank k U = j} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_)
  intro U
  have : finrank k (U.map (e : V →ₗ[k] V')) = finrank k U := LinearEquiv.finrank_map_eq e U
  change _ ↔ finrank k (U.map (e : V →ₗ[k] V')) = j
  rw [this]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitive
noncomputable section

open Matrix GlobalTheory.SplitHecke GlobalTheory.ExportSeries

namespace GlobalTheory.HeckeMobius

section Pure

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem reps_mul_central {n : ℕ} {ι : Type} {x c : GL (Fin n) K} {R : Finset ι} {ρ : ι → GL (Fin n) K}
    (hc : ∀ g : GL (Fin n) K, c * g = g * c) (h : Reps O x R ρ) :
    Reps O (x * c) R fun γ => ρ γ * c := by
  have hc' : ∀ g : GL (Fin n) K, c⁻¹ * g = g * c⁻¹ := fun g => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc g, mul_inv_cancel_right]
  refine ⟨fun γ hγ => ?_, fun k₁ k₂ h₁ h₂ => ?_⟩
  · obtain ⟨k₁, k₂, h₁, h₂, e⟩ := h.1 γ hγ
    exact ⟨k₁, k₂, h₁, h₂, by show ρ γ * c = _; rw [e]; simp only [mul_assoc, hc k₂]⟩
  · have e : ∀ γ, (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = (ρ γ)⁻¹ * (k₁ * x * k₂) := fun γ => by
      calc (ρ γ * c)⁻¹ * (k₁ * (x * c) * k₂) = c⁻¹ * ((ρ γ)⁻¹ * (k₁ * x * k₂)) * c := by
            rw [_root_.mul_inv_rev]; simp only [mul_assoc, hc k₂]
        _ = (ρ γ)⁻¹ * (k₁ * x * k₂) := by rw [hc', inv_mul_cancel_right]
    exact (existsUnique_congr fun γ => and_congr_right fun _ => by rw [e γ]).2 (h.2 k₁ k₂ h₁ h₂)

def scal {n : ℕ} (a : K) (ha : a ≠ 0) : GL (Fin n) K :=
  Units.map (Matrix.scalar (Fin n) : K →+* Matrix (Fin n) (Fin n) K).toMonoidHom (Units.mk0 a ha)

theorem scal_val {n : ℕ} (a : K) (ha : a ≠ 0) :
    ((scal a ha : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) a := rfl

theorem scal_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : scal a ha * g = g * scal a ha :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, scal_val]
    exact (Matrix.scalar_commute a (fun _ => Commute.all _ _) _).eq)

theorem scal_inv_comm {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha)⁻¹ * g = g * (scal a ha)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, scal_comm, mul_inv_cancel_right]

theorem scal_mul_val {n : ℕ} (a : K) (ha : a ≠ 0) (g : GL (Fin n) K) : (scal a ha * g).1 = a • g.1 := by
  rw [Units.val_mul, scal_val, Matrix.scalar_apply, smul_eq_diagonal_mul]

theorem hk_compl {p : O} (hp : algebraMap O K p ≠ 0) {n j : ℕ} (hj : j ≤ n) {α : GL (Fin n) K} (h : Hk O p j α) :
    Hk O p (n - j) (scal (algebraMap O K p) hp * α⁻¹) := by
  refine ⟨by rw [scal_mul_val]; exact h.2.1, ?_, ?_⟩
  · have : algebraMap O K p • ((scal (algebraMap O K p) hp * α⁻¹)⁻¹ : GL (Fin n) K).1 = α.1 := by
      rw [← scal_mul_val _ hp, _root_.mul_inv_rev, inv_inv, ← mul_assoc, scal_comm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact h.1
  · obtain ⟨u, hu⟩ := h.2.2
    refine ⟨u⁻¹, ?_⟩
    have h1 : (α⁻¹).1.det * α.1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 : algebraMap O K ((u⁻¹ : Oˣ) : O) * algebraMap O K (u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [scal_mul_val, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow]
    rw [hu, map_mul, map_pow] at h1
    have hn : algebraMap O K p ^ n = algebraMap O K p ^ (n - j) * algebraMap O K p ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    rw [hn]
    linear_combination (-(algebraMap O K p ^ (n - j) * algebraMap O K p ^ j * (α⁻¹).1.det)) * h2 +
      (algebraMap O K p ^ (n - j) * algebraMap O K ((u⁻¹ : Oˣ) : O)) * h1

theorem cond_eq {p : O} (hp : algebraMap O K p ≠ 0) {r n : ℕ} (g : GL (Fin r) K) (z : Matrix (Fin r) (Fin n) O) :
    ((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) * (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 =
      ((g⁻¹).1 * z.map (algebraMap O K))ᵀ := by
  have : (tr ((g * (scal (algebraMap O K p) hp)⁻¹)⁻¹)).1 = (algebraMap O K p • (g⁻¹).1)ᵀ := by
    rw [_root_.mul_inv_rev, inv_inv, ← scal_mul_val _ hp]; rfl
  rw [this, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    inv_mul_cancel₀ hp, one_smul]
  rfl


open IsLocalRing in
theorem count_eq [Finite (ResidueField O)] {p : O} (hp : Irreducible p) {r n k : ℕ} (hk : k ≤ r) {ι : Type}
    {α : GL (Fin r) K} {R : Finset ι} {ρ : ι → GL (Fin r) K} (hα : Hk O p k α) (hR : Reps O α R ρ)
    (z : Matrix (Fin r) (Fin n) O) :
    Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} =
      Nat.card {W : Submodule (ResidueField O)
        (Fin (Module.finrank (ResidueField O) (LinearMap.ker (z.map (residue O))ᵀ.mulVecLin)) → ResidueField O) //
          Module.finrank (ResidueField O) W = k} := by
  have h0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  have hR' : Reps O (tr (scal (algebraMap O K p) h0 * α⁻¹)) R
      fun γ => tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹) := by
    apply Reps.tr
    rw [_root_.mul_inv_rev, inv_inv]
    exact reps_mul_central (scal_inv_comm _ h0) hR
  have hc := Cosets.card_cosets O K p hp n r (r - k) ι _ R _ zᵀ (Nat.sub_le r k) (hk_compl h0 hk hα).tr hR'
  calc Nat.card {γ : ι // γ ∈ R ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))}
      = Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • zᵀ.map (algebraMap O K)) *
          (tr ((ρ γ * (scal (algebraMap O K p) h0)⁻¹)⁻¹)).1)} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun γ => and_congr_right fun _ => by
          rw [cond_eq h0]; exact ⟨fun h => h.transpose, fun h => h.transpose⟩)
    _ = _ := hc
    _ = Nat.card {W : Submodule (ResidueField O) (Fin r → ResidueField O) //
          W ≤ LinearMap.ker (z.map (residue O))ᵀ.mulVecLin ∧ Module.finrank (ResidueField O) W = k} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun W => by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩)
    _ = _ := GlobalTheory.card_subspaces_le_eq _ _
    _ = _ := GlobalTheory.card_subspaces_finrank_congr (LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun _).symm) k

theorem sum_smul_row {F : Type} [Field F] {r n : ℕ} (y : Matrix (Fin r) (Fin n) F) (g : Fin r → F) :
    yᵀ *ᵥ g = ∑ i, g i • y.row i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.row, mul_comm]

end Pure


open IsLocalRing in
theorem sum_hecke_indicator_eq_prim : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite (IsLocalRing.ResidueField O)] (p : O), Irreducible p → ∀ (r n : ℕ) (ι : Type) (α : ℕ → GL (Fin r) K) (R : ℕ → Finset ι) (ρ : ι → GL (Fin r) K), (∀ k ∈ Finset.Icc 1 r, Hk O p k (α k) ∧ Reps O (α k) (R k) ρ) → ∀ z : Matrix (Fin r) (Fin n) O, (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) = ((prim (z.map (IsLocalRing.residue O)) : ℚ) : ℂ) := by
  intro O K _ _ _ _ _ _ _ p hp r n ι α R ρ h z
  set A := (z.map (residue O))ᵀ with hA
  set c := Module.finrank (ResidueField O) (LinearMap.ker A.mulVecLin) with hc
  have hcr : c ≤ r := by
    have := Submodule.finrank_le (LinearMap.ker A.mulVecLin)
    rwa [Module.finrank_fin_fun] at this
  let N : ℕ → ℂ := fun k => (Nat.card {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
    Module.finrank (ResidueField O) W = k} : ℂ)
  have hN0 : N 0 = 1 := by
    simp only [N, Submodule.finrank_eq_zero]
    rw [Nat.card_unique, Nat.cast_one]
  have hNc : ∀ k, c < k → N k = 0 := fun k hk => by
    simp only [N, Nat.cast_eq_zero]
    haveI : IsEmpty {W : Submodule (ResidueField O) (Fin c → ResidueField O) //
        Module.finrank (ResidueField O) W = k} := ⟨fun W => by
      have := Submodule.finrank_le W.1
      rw [Module.finrank_fin_fun, W.2] at this
      omega⟩
    exact Nat.card_of_isEmpty
  have e1 : (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) *
      (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) =
      ∑ k ∈ Finset.range (r + 1), (-1 : ℂ) ^ k * (Nat.card (ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * N k * 1 ^ k := by
    rw [Finset.sum_range_succ', pow_zero, pow_zero, one_mul, hN0, mul_one, one_mul, add_comm]
    congr 1
    have hI : Finset.Icc 1 r = Finset.Ico 1 (r + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : 1 + k ≤ r := by rw [Finset.mem_range] at hk; omega
    have hm : 1 + k ∈ Finset.Icc 1 r := Finset.mem_Icc.2 ⟨by omega, hk'⟩
    rw [count_eq hp hk' (h _ hm).1 (h _ hm).2 z, one_pow, mul_one, add_comm 1 k]
  have hli : LinearIndependent (ResidueField O) (z.map (residue O)).row ↔ c = 0 := by
    rw [hc, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot', Fintype.linearIndependent_iff]
    refine forall_congr' fun g => ?_
    rw [Matrix.mulVecLin_apply, hA, sum_smul_row]
    constructor
    · intro H h0; funext i; exact H h0 i
    · intro H h0 i; rw [H h0]; rfl
  rw [e1, ← Finset.sum_subset (Finset.range_subset_range.2 (show c + 1 ≤ r + 1 by omega)) (fun k hk hk' => ?_)]
  · refine Eq.trans (GlobalTheory.GaussSubspace.sum_card_subspaces (ResidueField O) c ℂ 1) ?_
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [prim, if_pos (hli.2 h0), h0, Finset.prod_range_zero]
      simp
    · rw [prim, if_neg (fun H => by have := hli.1 H; omega)]
      obtain ⟨m, hm⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
      rw [hm, Finset.prod_range_succ', pow_zero, one_mul, sub_self, mul_zero]
      simp
  · rw [Finset.mem_range, not_lt] at hk'
    rw [hNc k (by omega)]
    ring

end GlobalTheory.HeckeMobius
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitiveStatement
open Matrix GlobalTheory.SplitHecke GlobalTheory.ExportSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_hecke_indicator_integral_eq_primitive : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite (IsLocalRing.ResidueField O)] (p : O), Irreducible p → ∀ (r n : ℕ) (ι : Type) (α : ℕ → GL (Fin r) K) (R : ℕ → Finset ι) (ρ : ι → GL (Fin r) K), (∀ k ∈ Finset.Icc 1 r, Hk O p k (α k) ∧ Reps O (α k) (R k) ρ) → ∀ z : Matrix (Fin r) (Fin n) O, (1 : ℂ) + ∑ k ∈ Finset.Icc 1 r, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField O) : ℂ) ^ (k * (k - 1) / 2) * (Nat.card {γ : ι // γ ∈ R k ∧ IntM O (((ρ γ)⁻¹).1 * z.map (algebraMap O K))} : ℂ) = ((prim (z.map (IsLocalRing.residue O)) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim | exact GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim | (intros; apply GlobalTheory.HeckeMobius.sum_hecke_indicator_eq_prim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lx_eq_of_rep_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x y : LX R i v}
    (h : (rep x)⁻¹ * rep y ∈ levW R i) : x = y := by
  have : (Quotient.mk _ (Quotient.out x) : LX R i v) = Quotient.mk _ (Quotient.out y) := by
    apply Quotient.sound
    change ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i))) _ _
    rw [Setoid.comap_rel, QuotientGroup.leftRel_apply]
    exact h
  exact (Quotient.out_eq x).symm.trans (this.trans (Quotient.out_eq y))

theorem rep_notMem_levW {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x : LX R i v}
    (hx : x ≠ lx0 R i v) : rep x ∉ levW R i := fun h =>
  hx (lx_eq_of_rep_rel ((levW R i).mul_mem ((levW R i).inv_mem h) (trivial_level_coset_representative_mem_level R i v)))

theorem rep_suppF {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    SuppF (Wc D i) (fid D v) (rep x) := (Quotient.out x).2.2

theorem eq_one_of_suppF_zero {V : HSp D} {g : GA D V} (h : SuppF V 0 g) : g = 1 := by
  have e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V 1 := by
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := rfl
    rw [h1, ← sub_eq_zero]
    ext a b
    have := h a b
    simpa [eq_comm] using this
  exact Subtype.ext (Units.ext e)

end

theorem acoef_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hb⟩ := hLS μ 𝓕 hμ
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · refine Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => ?_) hs.abs
    exact max_le (le_abs_self _) (abs_nonneg _)
  · intro v C hC
    by_cases hex : ∃ f, IsFinIdem D v f
    · have hf : IsFinIdem D v (fid D v) := by
        unfold fid
        rw [dite_eq_left hex]
        exact hex.choose_spec
      have hinj : Function.Injective (rep : LX R i v → GA D (Wc D i)) := fun x y h =>
        lx_eq_of_rep_rel (by rw [h, inv_mul_cancel]; exact (levW R i).one_mem)
      have := hb v _ hf (C.image rep) ?_ ?_
      · rw [Finset.sum_image (fun x _ y _ h => hinj h)] at this
        exact this.trans (le_max_left _ _)
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨rep_suppF x, rep_notMem_levW fun e => hC (e ▸ hx)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hg'
        rw [lx_eq_of_rep_rel h]
    · have hf : fid D v = 0 := by
        unfold fid
        rw [dite_eq_right hex]
      have hC0 : C = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        have h1 : rep x = 1 := eq_one_of_suppF_zero (hf ▸ rep_suppF x)
        exact rep_notMem_levW (fun e => hC (e ▸ hx)) (h1 ▸ (levW R i).one_mem)
      rw [hC0, Finset.sum_empty]
      exact le_max_right _ _

end GlobalTheory.RawLift.Eu

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCoefficient_nontrivialCosets_summable_bound : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  first | exact @GlobalTheory.RawLift.Eu.acoef_small | exact GlobalTheory.RawLift.Eu.acoef_small | (intros; apply GlobalTheory.RawLift.Eu.acoef_small <;> assumption)
end
end
