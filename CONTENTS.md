# Manuscript collection

**3 manuscripts covering 10 result families.**

## Manuscript map

Each result description is followed by its manuscript and abstract. Paper titles link directly to PDFs.

<table>
<thead><tr><th>Result</th></tr></thead>
<tbody><tr>
<td>

**001. Three-space is not six-colorable, machine-checked.** Every coloring of ℝ³ with six colors, with arbitrary color classes, has two points at distance 1 of the same color, so χ(ℝ³) ≥ 7 (previously 6). The proof transfers arbitrary colorings to measurable ones by averaging over independent rotations of coordinate 2-planes and applying OpenAI's planar rigidity theorem block by block. It is verified in Lean end to end, relative to the published density bound m₁(ℝ³) ≤ 0.1532996. Crocker independently posted the argument conditionally on OpenAI's rigidity theorem (Oct 10, 2026).

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[A machine-checked proof that three-space is not six-colorable](preprints/A-machine-checked-proof-that-three-space-is-not-six-colorable-October-14-2026/paper.pdf)

We give a proof, formally verified in Lean 4, that every coloring of ℝ³ with six colors contains two points at distance 1 of the same color, so χ(ℝ³) ≥ 7. The proof extends OpenAI's planar transfer principle to every dimension and to every finite set of algebraic distances by torus averaging, and records consequences for finite graphs and for many forbidden distances.

</td>
</tr></tbody>
<tbody><tr>
<td>

**002. Transfer in every dimension and for algebraic distance sets.** For every n ≥ 2 and every countable set D of positive algebraic distances, a D-avoiding coloring of ℝⁿ yields a conull measurable partition into D-avoiding sets, so χ_D(ℝⁿ) ≥ 1/m_D(ℝⁿ). Verified in Lean, together with the conditional bounds χ(ℝⁿ) ≥ 11, 17, 23, 39, 53 for n = 4, …, 8 and their finite forms. For n ≥ 4 and rational squared distances these consequences are due to Davies.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[A machine-checked proof that three-space is not six-colorable](preprints/A-machine-checked-proof-that-three-space-is-not-six-colorable-October-14-2026/paper.pdf)

We give a proof, formally verified in Lean 4, that every coloring of ℝ³ with six colors contains two points at distance 1 of the same color, so χ(ℝ³) ≥ 7. The proof extends OpenAI's planar transfer principle to every dimension and to every finite set of algebraic distances by torus averaging, and records consequences for finite graphs and for many forbidden distances.

</td>
</tr></tbody>
<tbody><tr>
<td>

**003. Many forbidden distances in the plane.** With Bukh's theorem, the number of colors needed to avoid k distances in the plane exceeds 4.0486ᵏ, answering Erdős Problem #706 in the negative; every finite coloring of the plane realizes every sufficiently large algebraic distance, such as 2ʲ or j!, monochromatically (questions of Soifer and Kahle). Also stated conditionally by Crocker.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Monochromatic distances in finite colorings of the plane](preprints/Monochromatic-distances-in-finite-colorings-of-the-plane-October-14-2026/paper.pdf)

Every finite coloring of the plane has, for all large n, monochromatic pairs at distance 2ⁿ and at distance n!; the number of colors needed to avoid r distances grows exponentially (Erdős #706), with explicit distance sets; quantitative bounds for odd, lacunary and two-distance problems; the main qualitative statements are formally verified in Lean.

</td>
</tr></tbody>
<tbody><tr>
<td>

**004. Finite unit-distance graphs in ℝ³ attain the measurable density; an improved density bound.** The infimum of α(G)/|G| over finite unit-distance graphs in ℝ³ equals m₁(ℝ³); in particular some finite unit-distance graph in ℝ³ has independence ratio below 0.1486, using the new bound m₁(ℝ³) ≤ 0.1485113 (previously 0.1532996), certified in ball arithmetic and checked by two independent programs. The equality α₁ = m₁ in ℝ³ is verified in Lean. The plane is due to Li–Su and n ≥ 4 to Davies.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[A machine-checked proof that three-space is not six-colorable](preprints/A-machine-checked-proof-that-three-space-is-not-six-colorable-October-14-2026/paper.pdf)

We give a proof, formally verified in Lean 4, that every coloring of ℝ³ with six colors contains two points at distance 1 of the same color, so χ(ℝ³) ≥ 7. The proof extends OpenAI's planar transfer principle to every dimension and to every finite set of algebraic distances by torus averaging, and records consequences for finite graphs and for many forbidden distances.

</td>
</tr></tbody>
<tbody><tr>
<td>

**005. Seven colors for the plane with two forbidden distances.** χ(ℝ², {1, (√2+√6)/2}) ≥ 7, by an 8-point pigeonhole gadget and two 12-point chains whose long pairs land exactly on the forbidden distances, with exact-arithmetic and DRAT certificates. This is the only bound χ_D(ℝ²) ≥ 7 for an explicit two-distance set proved by a finite certificate.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Chromatic numbers of the plane with two forbidden distances: a seven-color lower bound and smaller six-chromatic graphs](preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/paper.pdf)

We prove χ(ℝ², {1, (√2+√6)/2}) ≥ 7 with explicit SAT- and exact-arithmetic-certified finite configurations, give record small 6-chromatic two-distance graphs (26 and 30 vertices), the bound e₅ ≤ 2278, the six-coloring continuum up to 0.667504532081, and forced-density constants, with all certificates.

</td>
</tr></tbody>
<tbody><tr>
<td>

**006. Small six-chromatic two-distance graphs and an edge-sparse 5-chromatic unit-distance graph.** A 26-vertex 6-chromatic {1, (√2+√6)/2}-graph (previously 117 for this pair; smallest known for any pair, previously 31) and a 30-vertex 6-chromatic {1, √3}-graph (previously 33). The 509-vertex 5-chromatic unit-distance graph stays 5-chromatic with 2278 edges (previously 2406).

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Chromatic numbers of the plane with two forbidden distances: a seven-color lower bound and smaller six-chromatic graphs](preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/paper.pdf)

We prove χ(ℝ², {1, (√2+√6)/2}) ≥ 7 with explicit SAT- and exact-arithmetic-certified finite configurations, give record small 6-chromatic two-distance graphs (26 and 30 vertices), the bound e₅ ≤ 2278, the six-coloring continuum up to 0.667504532081, and forced-density constants, with all certificates.

</td>
</tr></tbody>
<tbody><tr>
<td>

**007. The six-coloring continuum.** There are colorings of the plane with six colors in which five classes avoid distance 1 and the sixth avoids distance d, for every d ∈ [0.354, 0.667504532081] (previously up to 0.657), certified by 59 exact rational tilings.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Chromatic numbers of the plane with two forbidden distances: a seven-color lower bound and smaller six-chromatic graphs](preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/paper.pdf)

We prove χ(ℝ², {1, (√2+√6)/2}) ≥ 7 with explicit SAT- and exact-arithmetic-certified finite configurations, give record small 6-chromatic two-distance graphs (26 and 30 vertices), the bound e₅ ≤ 2278, the six-coloring continuum up to 0.667504532081, and forced-density constants, with all certificates.

</td>
</tr></tbody>
<tbody><tr>
<td>

**008. Monochromatic powers of two and factorials, machine-checked.** Every finite coloring of the plane (and of ℝⁿ, n ≥ 2) has two points of the same color at distance 2ⁿ, and two at distance n!, for all sufficiently large n; more generally no finite coloring avoids an unbounded set of algebraic distances. This answers questions of Soifer and of Kahle recorded by Davies–McCarty–Pilipczuk. Fully verified in Lean (transfer plus a torus-Fourier proof of the needed Furstenberg–Katznelson–Weiss theorem). Stated conditionally by Crocker.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Monochromatic distances in finite colorings of the plane](preprints/Monochromatic-distances-in-finite-colorings-of-the-plane-October-14-2026/paper.pdf)

</td>
</tr></tbody>
<tbody><tr>
<td>

**009. Quantitative monochromatic distances.** Every k-coloring of the plane has two points of the same color at an odd distance below 18k² and at a distance 2ⁱ < k^6.2; in ℝ³, at an odd distance at most k and at a distance 2ⁱ < k^2.58. χ(ℝ², {1, q, …, q^{K−1}}) ≥ 1 + (22/15)(2.5^K − 1) for algebraic q ≥ 4096 (an explicit exponential lower bound for Erdős Problem #706), and χ(ℝ², {1, d}) ≥ 12 for every algebraic d ≥ 10⁴. Explicit certified cases: every 6-coloring of the plane has a monochromatic pair at distance 1, 3, 5 or 7. Proofs combine the Lean-verified transfer with explicit Fourier certificates.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Monochromatic distances in finite colorings of the plane](preprints/Monochromatic-distances-in-finite-colorings-of-the-plane-October-14-2026/paper.pdf)

</td>
</tr></tbody>
<tbody><tr>
<td>

**010. Erdős Problem #706, machine-checked.** For every C and e there is a K-element set D of integer distances and a finite point set P in the plane whose D-distance graph is not C·K^e-colorable; explicitly, every coloring of the plane avoiding {(10⁶)^j : j < K} uses at least (4/9)(3/2)^K colors. Hence L(r) is not polynomially bounded. Also formal: every k-coloring of the plane has a monochromatic distance 2^i with i ≤ 20(2⌊log₂ 9k⌋+2). Two forbidden distances (computer-certified): χ(ℝ², {1, d}) ≥ 7 for algebraic d ∈ [1.77, 1.92] ∪ [7, ∞), ≥ 8 for d ≥ 16, ≥ 9 for d ≥ 40, ≥ 10 for d ≥ 150, ≥ 12 for d ≥ 10⁴. The qualitative exponential growth was stated conditionally by Crocker.

</td>
</tr></tbody>
<tbody><tr>
<td>

&emsp;[Monochromatic distances in finite colorings of the plane](preprints/Monochromatic-distances-in-finite-colorings-of-the-plane-October-14-2026/paper.pdf)

</td>
</tr></tbody>
</table>
