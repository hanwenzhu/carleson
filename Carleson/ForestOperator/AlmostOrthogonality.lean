import BlueprintGen
import Carleson.ForestOperator.QuantativeEstimate

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.4 except Lemmas 4-6 -/

variable (t) in
/-- The operator `S_{2,𝔲} f(x)`, given above Lemma 7.4.3. -/
def adjointBoundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ‖adjointCarlesonSum (t u) f x‖ₑ + MB volume 𝓑 c𝓑 r𝓑 f x + ‖f x‖ₑ

variable (t u₁ u₂) in
/-- The set `𝔖` defined in the proof of Lemma 7.4.4.
We append a subscript 0 to distinguish it from the section variable. -/
def 𝔖₀ : Set (𝔓 X) := { p ∈ t u₁ ∪ t u₂ | 2 ^ ((Z : ℝ) * n / 2) ≤ dist_(p) (𝒬 u₁) (𝒬 u₂) }

/--
For each $\fp \in \fP$, we have
$$T_{\fp}^* g = \mathbf{1}_{B(\pc(\fp), 5D^{\ps(\fp)})} T_{\fp}^* \mathbf{1}_{\scI(\fp)} g\,.$$ For
each $\fu \in \fU$ and each $\fp \in \fT(\fu)$, we have
$$T_{\fp}^* g = \mathbf{1}_{\scI(\fu)} T_{\fp}^* \mathbf{1}_{\scI(\fu)} g\,.$$

Part 1 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function.
-/
@[blueprint
  "adjoint tile support"
  (proof := /--
  By \ref{forest1}, $E(\fp) \subset \scI(\fp) \subset \scI(\fu)$. Thus by
  [\[definetp\*\]](#definetp*) $$T_{\fp}^* g(x) = T_{\fp}^* (\mathbf{1}_{\scI(\fp)} g)(x)$$
  $$= \int_{E(\fp)} \overline{K_{\ps(\fp)}(y,x)} e(-\tQ(y)(x) + \tQ(y)(y)) \mathbf{1}_{\scI(\fp)}(y) g(y) \, \mathrm{d}\mu(y)\,.$$
  If this integral is not $0$, then there exists $y \in \scI(\fp)$ such that
  $K_{\ps(\fp)}(y,x) \ne 0$. By \ref{supp-Ks}, \ref{eq-vol-sp-cube} and the
  triangle inequality, it follows that $$\begin{equation*}
          x \in B(\pc(\fp), 5 D^{\ps(\fp)})\, .
  \end{equation*}$$ Thus
  $$T_{\fp}^* g(x) = \mathbf{1}_{B(\pc(\fp), 5D^{\ps(\fp)})}(x) T_{\fp}^* (\mathbf{1}_{\scI(\fp)} g)(x)\,.$$
  The second claimed equation follows now since $\scI(\fp) \subset \scI(\fu)$ and by
  \ref{forest6} we have $B(\pc(\fp), 5D^{\ps(\fp)}) \subset \scI(\fu)$.
  -/)
  (latexEnv := "lemma")]
lemma adjoint_tile_support1 : adjointCarleson p f =
    (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (adjointCarleson p ((𝓘 p : Set X).indicator f)) := by
  rw [adjoint_eq_adjoint_indicator E_subset_𝓘]; ext x
  rcases eq_or_ne (adjointCarleson p ((𝓘 p : Set X).indicator f) x) 0 with h0 | hn
  · exact (indicator_apply_eq_self.mpr fun _ ↦ h0).symm
  refine (indicator_of_mem ?_ _).symm
  obtain ⟨y, my, Ky⟩ : ∃ y ∈ 𝓘 p, Ks (𝔰 p) y x ≠ 0 := by
    contrapose! hn
    refine setIntegral_eq_zero_of_forall_eq_zero fun y my ↦ ?_
    simp [hn _ (E_subset_𝓘 my)]
  rw [mem_ball]
  calc
    _ ≤ dist y x + dist y (𝔠 p) := dist_triangle_left ..
    _ < D ^ 𝔰 p / 2 + 4 * (D : ℝ) ^ 𝔰 p :=
      add_lt_add_of_le_of_lt (dist_mem_Icc_of_Ks_ne_zero Ky).2 (mem_ball.mpr (Grid_subset_ball my))
    _ ≤ _ := by rw [div_eq_mul_inv, mul_comm, ← add_mul]; gcongr; norm_num

/-- Part 2 of Lemma 7.4.1.
Todo: update blueprint with precise properties needed on the function. -/
lemma adjoint_tile_support2 (hu : u ∈ t) (hp : p ∈ t u) : adjointCarleson p f =
    (𝓘 u : Set X).indicator (adjointCarleson p ((𝓘 u : Set X).indicator f)) := by
  rw [← adjoint_eq_adjoint_indicator (E_subset_𝓘.trans (t.smul_four_le hu hp).1.1),
    adjoint_tile_support1, indicator_indicator, ← right_eq_inter.mpr]
  exact (ball_subset_ball (by gcongr; norm_num)).trans (t.ball_subset hu hp)

lemma adjoint_tile_support2_sum (hu : u ∈ t) :
    adjointCarlesonSum (t u) f =
    (𝓘 u : Set X).indicator (adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator f)) := by
  unfold adjointCarlesonSum
  classical
  calc
    _ = ∑ p with p ∈ t u,
        (𝓘 u : Set X).indicator (adjointCarleson p ((𝓘 u : Set X).indicator f)) := by
      ext x; simp only [Finset.sum_apply]; congr! 1 with p mp
      rw [Finset.mem_filter_univ] at mp; rw [adjoint_tile_support2 hu mp]
    _ = _ := by simp_rw [← Finset.indicator_sum, ← Finset.sum_apply]

/-- A partially applied variant of `adjoint_tile_support2_sum`, used to prove Lemma 7.7.3. -/
lemma adjoint_tile_support2_sum_partial (hu : u ∈ t) :
    adjointCarlesonSum (t u) f = (adjointCarlesonSum (t u) ((𝓘 u : Set X).indicator f)) := by
  unfold adjointCarlesonSum
  ext x; congr! 1 with p mp; classical rw [Finset.mem_filter_univ] at mp
  rw [← adjoint_eq_adjoint_indicator (E_subset_𝓘.trans (t.smul_four_le hu mp).1.1)]

lemma enorm_adjointCarleson_le {x : X} :
    ‖adjointCarleson p f x‖ₑ ≤
    C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ * ∫⁻ y in E p, ‖f y‖ₑ := by
  calc
    _ ≤ ∫⁻ y in E p, ‖conj (Ks (𝔰 p) y x) * exp (.I * (Q y y - Q y x)) * f y‖ₑ := by
      apply enorm_integral_le_lintegral_enorm
    _ = ∫⁻ y in E p, ‖Ks (𝔰 p) y x‖ₑ * ‖f y‖ₑ := by
      congr! with y
      rw [enorm_mul, enorm_mul, ← ofReal_sub, enorm_exp_I_mul_ofReal, RCLike.enorm_conj, mul_one]
    _ ≤ C2_1_3 a * ∫⁻ y in E p, (volume (ball y (D ^ 𝔰 p)))⁻¹ * ‖f y‖ₑ := by
      rw [← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_mono fun y ↦ ?_
      rw [← mul_assoc, mul_comm _ _⁻¹, ← ENNReal.div_eq_inv_mul]
      exact mul_le_mul_right' enorm_Ks_le _
    _ ≤ _ := by
      rw [mul_assoc _ (_ ^ _), mul_comm (_ ^ _), ← ENNReal.div_eq_inv_mul,
        ← ENNReal.inv_div (.inl (by simp)) (.inl (by simp)), mul_assoc, ← lintegral_const_mul' _⁻¹]
      swap
      · simp_rw [ne_eq, ENNReal.inv_eq_top, ENNReal.div_eq_zero_iff, ENNReal.pow_eq_top_iff,
          ENNReal.ofNat_ne_top, false_and, or_false]
        exact (measure_ball_pos _ _ (by unfold defaultD; positivity)).ne'
      refine mul_le_mul_left' (setLIntegral_mono' measurableSet_E fun y my ↦ ?_) _
      exact mul_le_mul_right' (ENNReal.inv_le_inv' (volume_xDsp_bound_4 (E_subset_𝓘 my))) _

lemma enorm_adjointCarleson_le_mul_indicator {x : X} :
    ‖adjointCarleson p f x‖ₑ ≤
    C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ * (∫⁻ y in E p, ‖f y‖ₑ) *
      (ball (𝔠 p) (8 * D ^ 𝔰 p)).indicator 1 x := by
  rw [adjoint_tile_support1, enorm_indicator_eq_indicator_enorm]
  calc
    _ ≤ (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator (fun _ ↦
        C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ *
          ∫⁻ y in E p, ‖(𝓘 p : Set X).indicator f y‖ₑ) x := by
      gcongr; exact enorm_adjointCarleson_le
    _ = C2_1_3 a * 2 ^ (4 * a) * (volume (ball (𝔠 p) (8 * D ^ 𝔰 p)))⁻¹ * (∫⁻ y in E p, ‖f y‖ₑ) *
        (ball (𝔠 p) (5 * D ^ 𝔰 p)).indicator 1 x := by
      conv_lhs => enter [2, z]; rw [← mul_one (_ * _ * _ * _)]
      rw [indicator_const_mul]; congr 2
      refine setLIntegral_congr_fun measurableSet_E fun y my ↦ ?_
      rw [indicator_of_mem (E_subset_𝓘 my)]
    _ ≤ _ := by
      gcongr; refine indicator_le_indicator_apply_of_subset (ball_subset_ball ?_) (zero_le _)
      gcongr; norm_num

/-- The constant used in `adjoint_tree_estimate`.
Has value `2 ^ (181 * a ^ 3)` in the blueprint. -/
irreducible_def C7_4_2 (a : ℕ) : ℝ≥0 := C7_3_1_1 a

/--
For all $g$ with $\text{support}(g) \subseteq G$, we have that
$$\left\| \sum_{\fp \in \fT(\fu)} T_{\fp}^* g\right\|_2 \le 2^{181a^3} \dens_1(\fT(\fu))^{1/2} \|g\|_2\,.$$

Lemma 7.4.2.
-/
@[blueprint
  "adjoint tree estimate"
  (proof := /--
  By `TileStructure.Forest.density_tree_bound1`, we have for all bounded $f$ and $g$ with
  $|g| \le \mathbf{1}_G$ that
  $$\left| \int_X \overline{\sum_{\fp\in \fT(\fu)} T_{\fp}^* g} f \,\mathrm{d}\mu \right| = \left| \int_X \overline{g} \sum_{\fp \in \fT(\fu)} T_{\fp} f \,\mathrm{d}\mu \right|$$
  $$\begin{equation}
          \label{eq-adjoint-bound}
          \le 2^{181a^3} \dens_1(\fT(\fu))^{1/2} \|g\|_2 \|f\|_2\,.
  \end{equation}$$ Let $f = \sum_{\fp \in \fT(\fu)} T_{\fp}^* g$. Since $|g| \le \mathbf{1}_G$, $f$ is
  bounded and has bounded support. In particular $\|f\|_2 < \infty$. Dividing
  \ref{eq-adjoint-bound} by $\|f\|_2$ completes the proof.
  -/)
  (latexEnv := "lemma")]
lemma adjoint_tree_estimate (hu : u ∈ t) (hf : BoundedCompactSupport f) (h2f : f.support ⊆ G) :
    eLpNorm (adjointCarlesonSum (t u) f) 2 volume ≤
    C7_4_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume := by
  rw [C7_4_2_def]
  set g := adjointCarlesonSum (t u) f
  have hg : BoundedCompactSupport g := hf.adjointCarlesonSum
  have h := density_tree_bound1 hg hf h2f hu
  simp_rw [adjointCarlesonSum_adjoint hg hf] at h
  have : ‖∫ x, conj (adjointCarlesonSum (t u) f x) * g x‖ₑ = eLpNorm g 2 volume ^ 2 := by
    simp_rw [eLpNorm_two_eq_enorm_integral_mul_conj (hg.memLp 2), mul_comm, g]
  rw [this, pow_two, mul_assoc, mul_comm _ (eLpNorm f _ _), ← mul_assoc] at h
  by_cases hgz : eLpNorm g 2 volume = 0
  · simp [hgz]
  · refine ENNReal.mul_le_mul_right hgz ?_ |>.mp h
    exact (hg.memLp 2).eLpNorm_ne_top

/-- The constant used in `adjoint_tree_control`.
Has value `2 ^ (182 * a ^ 3)` in the blueprint. -/
irreducible_def C7_4_3 (a : ℕ) : ℝ≥0 := 2 ^ ((𝕔 + 7 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)

lemma le_C7_4_3 (ha : 4 ≤ a) : C7_4_2 a + CMB (defaultA a) 2 + 1 ≤ C7_4_3 a := by
  rw [C7_4_3, C7_4_2, C7_3_1_1, CMB_defaultA_two_eq]
  calc
    _ ≤ (2 : ℝ≥0) ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)
        + 2 ^ ((a : ℝ) + 3 / 2) + 2 ^ ((a : ℝ) + 3 / 2) := by
      gcongr; exact NNReal.one_le_rpow one_le_two (by linarith)
    _ = 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)  + 2 ^ ((a : ℝ) + 5 / 2) := by
      rw [add_assoc, ← two_mul, ← NNReal.rpow_one_add' (by positivity)]; congr 2; ring
    _ ≤ 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4) * a ^ 3)
        + 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4 : ℕ) * (a : ℝ) ^ 3) := by
      gcongr
      · exact one_le_two
      · calc
          _ ≤ 2 * (a : ℝ) := by
            rw [two_mul]; gcongr; exact (show (5 : ℝ) / 2 ≤ 4 by norm_num).trans (mod_cast ha)
          _ = 2 * a * 1 * 1 := by ring
          _ ≤ (𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4 : ℕ) * a * a * a := by
            gcongr
            · norm_cast
              have := seven_le_c
              omega
            · norm_cast; omega
            · norm_cast; omega
          _ = _ := by ring
    _ ≤ 2 ^ ((𝕔 + 6 + 𝕔 / 2 + 𝕔 / 4 : ℕ) * (a : ℝ) ^ 3 + 1) := by
      rw [← NNReal.rpow_natCast]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_pow]
      rw [← mul_two, ← NNReal.rpow_add_one' (by positivity)]
    _ ≤ _ := by
      rw [← NNReal.rpow_natCast]; gcongr
      · exact one_le_two
      · norm_cast
        have : 1 ≤ a ^ 3 := one_le_pow_of_one_le' (by linarith) _
        grw [this]
        exact le_of_eq (by ring)

/--
We have for all $\fu \in \fU$ and for all $g$ with $\text{support}(g) \subseteq G$
$$\|S_{2, \fu} g\|_2 \le 2^{182a^3} \|g\|_2\,.$$

Lemma 7.4.3.
-/
@[blueprint
  "adjoint tree control"
  (proof := /--
  This follows immediately from Minkowski's inequality, `Finset.measure_biUnion_le_lintegral` and
  `TileStructure.Forest.adjoint_tree_estimate`, using that $a \ge 4$.
  -/)
  (latexEnv := "lemma")]
lemma adjoint_tree_control
    (hu : u ∈ t) (hf : BoundedCompactSupport f) (h2f : f.support ⊆ G) :
    eLpNorm (adjointBoundaryOperator t u f ·) 2 volume ≤ C7_4_3 a * eLpNorm f 2 volume := by
  have m₁ : AEStronglyMeasurable (‖adjointCarlesonSum (t u) f ·‖ₑ) :=
    hf.aestronglyMeasurable.adjointCarlesonSum.enorm.aestronglyMeasurable
  have m₂ : AEStronglyMeasurable (MB volume 𝓑 c𝓑 r𝓑 f ·) := .maximalFunction 𝓑.to_countable
  have m₃ : AEStronglyMeasurable (‖f ·‖ₑ) := hf.aestronglyMeasurable.enorm.aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x ↦ ‖adjointCarlesonSum (t u) f x‖ₑ + MB volume 𝓑 c𝓑 r𝓑 f x) 2 volume +
        eLpNorm (‖f ·‖ₑ) 2 volume := eLpNorm_add_le (m₁.add m₂) m₃ one_le_two
    _ ≤ eLpNorm (‖adjointCarlesonSum (t u) f ·‖ₑ) 2 volume +
        eLpNorm (MB volume 𝓑 c𝓑 r𝓑 f ·) 2 volume + eLpNorm (‖f ·‖ₑ) 2 volume := by
      gcongr; apply eLpNorm_add_le m₁ m₂ one_le_two
    _ ≤ C7_4_2 a * dens₁ (t u) ^ (2 : ℝ)⁻¹ * eLpNorm f 2 volume +
        CMB (defaultA a) 2 * eLpNorm f 2 volume + eLpNorm f 2 volume := by
      gcongr
      · exact adjoint_tree_estimate hu hf h2f
      · exact (hasStrongType_MB_finite 𝓑_finite one_lt_two) _ (hf.memLp _) |>.2
      · rfl
    _ ≤ (C7_4_2 a * 1 ^ (2 : ℝ)⁻¹ + CMB (defaultA a) 2 + 1) * eLpNorm f 2 volume := by
      simp_rw [add_mul, one_mul]; gcongr; exact dens₁_le_one
    _ ≤ _ := by
      gcongr
      simp only [ENNReal.one_rpow, mul_one, defaultA, Nat.cast_pow, Nat.cast_ofNat]
      norm_cast
      apply le_C7_4_3 (four_le_a X)

/-- Part 1 of Lemma 7.4.7. -/
lemma overlap_implies_distance (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂)
    (h2u : 𝓘 u₁ ≤ 𝓘 u₂) (hp : p ∈ t u₁ ∪ t u₂)
    (hpu₁ : ¬Disjoint (𝓘 p : Set X) (𝓘 u₁)) : p ∈ 𝔖₀ t u₁ u₂ := by
  simp_rw [𝔖₀, mem_setOf, hp, true_and]
  wlog plu₁ : 𝓘 p ≤ 𝓘 u₁ generalizing p
  · have u₁lp : 𝓘 u₁ ≤ 𝓘 p := (le_or_ge_or_disjoint.resolve_left plu₁).resolve_right hpu₁
    obtain ⟨p', mp'⟩ := t.nonempty hu₁
    have p'lu₁ : 𝓘 p' ≤ 𝓘 u₁ := (t.smul_four_le hu₁ mp').1
    obtain ⟨c, mc⟩ := (𝓘 p').nonempty
    specialize this (mem_union_left _ mp') (not_disjoint_iff.mpr ⟨c, mc, p'lu₁.1 mc⟩) p'lu₁
    exact this.trans (Grid.dist_mono (p'lu₁.trans u₁lp))
  have four_Z := four_le_Z (X := X)
  have four_le_Zn : 4 ≤ Z * (n + 1) := by rw [← mul_one 4]; exact mul_le_mul' four_Z (by omega)
  have four_le_two_pow_Zn : 4 ≤ 2 ^ (Z * (n + 1) - 1) := by
    change 2 ^ 2 ≤ _; exact Nat.pow_le_pow_right zero_lt_two (by omega)
  have ha : (2 : ℝ) ^ (Z * (n + 1)) - 4 ≥ 2 ^ (Z * n / 2 : ℝ) :=
    calc
      _ ≥ (2 : ℝ) ^ (Z * (n + 1)) - 2 ^ (Z * (n + 1) - 1) := by gcongr; norm_cast
      _ = 2 ^ (Z * (n + 1) - 1) := by
        rw [sub_eq_iff_eq_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]
      _ ≥ 2 ^ (Z * n) := by apply pow_le_pow_right₀ one_le_two; rw [mul_add_one]; omega
      _ ≥ _ := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le one_le_two; rw [Nat.cast_mul]
        exact half_le_self (by positivity)
  rcases hp with (c : p ∈ t.𝔗 u₁) | (c : p ∈ t.𝔗 u₂)
  · calc
    _ ≥ dist_(p) (𝒬 p) (𝒬 u₂) - dist_(p) (𝒬 p) (𝒬 u₁) := by
      change _ ≤ _; rw [sub_le_iff_le_add, add_comm]; exact dist_triangle ..
    _ ≥ 2 ^ (Z * (n + 1)) - 4 := by
      gcongr
      · exact (t.lt_dist' hu₂ hu₁ hu.symm c (plu₁.trans h2u)).le
      · have : 𝒬 u₁ ∈ ball_(p) (𝒬 p) 4 :=
          (t.smul_four_le hu₁ c).2 (by convert mem_ball_self zero_lt_one)
        rw [@mem_ball'] at this; exact this.le
    _ ≥ _ := ha
  · calc
    _ ≥ dist_(p) (𝒬 p) (𝒬 u₁) - dist_(p) (𝒬 p) (𝒬 u₂) := by
      change _ ≤ _; rw [sub_le_iff_le_add, add_comm]; exact dist_triangle_right ..
    _ ≥ 2 ^ (Z * (n + 1)) - 4 := by
      gcongr
      · exact (t.lt_dist' hu₁ hu₂ hu c plu₁).le
      · have : 𝒬 u₂ ∈ ball_(p) (𝒬 p) 4 :=
          (t.smul_four_le hu₂ c).2 (by convert mem_ball_self zero_lt_one)
        rw [@mem_ball'] at this; exact this.le
    _ ≥ _ := ha

/--
Let $\fu_1 \ne \fu_2 \in \fU$ with $\scI(\fu_1) \subset \scI(\fu_2)$. If
$\fp \in \fT(\fu_1) \cup \fT(\fu_2)$ with $\scI(\fp) \cap \scI(\fu_1) \ne \emptyset$, then
$\fp \in \mathfrak{S}$. In particular, we have $\fT(\fu_1) \subset \mathfrak{S}$.

Part 2 of Lemma 7.4.7.
-/
@[blueprint
  "overlap implies distance"
  (proof := /--
  Suppose first that $\fp \in \fT(\fu_1)$. Then $\scI(\fp) \subset \scI(\fu_1) \subset \scI(\fu_2)$,
  by \ref{forest1}. Thus we have by the separation condition \ref{forest5},
  \ref{eq-freq-comp-ball}, \ref{forest1} and the triangle inequality
  $$\begin{align*}
          d_{\fp}(\fcc(\fu_1), \fcc(\fu_2)) &\ge d_{\fp}(\fcc(\fp), \fcc(\fu_2)) - d_{\fp}(\fcc(\fp), \fcc(\fu_1))\\
          &\ge 2^{Z(n+1)} - 4\\
          &\ge 2^{Zn/2}\,,
  \end{align*}$$ using that $Z= 2^{12a}\ge 4$. Hence $\fp \in \mathfrak{S}$.
  
  Suppose now that $\fp \in \fT(\fu_2)$. If $\scI(\fp) \subset \scI(\fu_1)$, then the same argument as
  above with $\fu_1$ and $\fu_2$ swapped shows $\fp \in \mathfrak{S}$. If
  $\scI(\fp) \not \subset \scI(\fu_1)$ then, by \ref{dyadicproperty},
  $\scI(\fu_1) \subset \scI(\fp)$. Pick $\fp' \in \fT(\fu_1)$, we have
  $\scI(\fp') \subset \scI(\fu_1) \subset \scI(\fp)$. Hence, by `Grid.dist_mono` and the first
  paragraph $$d_{\fp}(\fcc(\fu_1), \fcc(\fu_2)) \ge d_{\fp'}(\fcc(\fu_1), \fcc(\fu_2)) \ge 2^{Zn}\,,$$
  so $\fp \in \mathfrak{S}$.
  -/)
  (latexEnv := "lemma")]
lemma 𝔗_subset_𝔖₀ (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t) (hu : u₁ ≠ u₂) (h2u : 𝓘 u₁ ≤ 𝓘 u₂) :
    t u₁ ⊆ 𝔖₀ t u₁ u₂ := fun p mp ↦ by
  apply overlap_implies_distance hu₁ hu₂ hu h2u (mem_union_left _ mp)
  obtain ⟨c, mc⟩ := (𝓘 p).nonempty
  exact not_disjoint_iff.mpr ⟨c, mc, (t.smul_four_le hu₁ mp).1.1 mc⟩

end TileStructure.Forest
