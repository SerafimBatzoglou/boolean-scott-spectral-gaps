# Unbounded minimum Scott ranks for Boolean algebras

GPT 6.2 Astra (Codex) with Serafim Batzoglou

**For every countable ordinal $b$, there is a satisfiable pure Boolean $\Pi_{\omega+4}$ sentence whose countable models all have Scott rank greater than $b$.** The input sentence may depend on $b$. Its syntactic complexity has the same upper bound for every $b$.

Gonzalez and Harrison-Trainor asked whether fixing the complexity of a sentence extending Boolean algebra theory bounds the least Scott rank of a model. The theorem gives a negative answer already at $\alpha=\omega+4$. Here rank at most $b$ means that the structure has a parameterless $\Pi_{b+1}$ Scott sentence. The first complexity level where such a bound fails remains a separate question. [Original question, §1.9](https://arxiv.org/html/2411.12084v1)

## Read the result

| Start here | What to look for |
| --- | --- |
| [Formal theorem](BooleanScott/PureCounterexample.lean#L61) | `BooleanScott.pure_boolean_counterexample` states the exact quantifiers. Its sentence entails the Boolean equations and $0\ne 1$, has a countable Boolean model, and excludes a $\Pi_{b+1}$ Scott sentence for every countable model among all countable structures of the signature. |
| [Manuscript source](paper/boolean-scott-spectral-gaps.tex) | The full proof, including the finite-degree markers, the chart Scott bound, both directions of the absorption theorem in arbitrary models, and the Borel argument. The private draft release includes the typeset PDF. |
| [Guide to the formal proof](PROOF_GUIDE.md) | A module-by-module account of the arguments, including where finiteness, countability and the quantifier over all models enter. |
| [Rank and syntax](BooleanScott/Infinitary.lean) | The pure Boolean language, infinitary hierarchy and definition of the comparison with $b$. |
| [Absorption and the Boolean-algebra theorem](BooleanScott/NegativeResolution.lean) | `BooleanScott.guarded_absorption_iff_branch` and `BooleanScott.negativeResolution` discharge the geometric hypotheses. |

The proof constructs a fixed Boolean factor $B$ and a sentence for each tree $T$. Every countable Boolean algebra $A$ satisfying that sentence obeys the same criterion: $A\cong A\times B$ precisely when $T$ has an infinite branch. A projection argument supplies a branchless tree for which every satisfying $A$ agrees with its product on all $\Pi_{b+1}$ sentences. The two structures are nonisomorphic, so none of those sentences isolates $A$. [Formal projection argument](BooleanScott/Reduction.lean)

## Check the proof

Install [elan](https://github.com/leanprover/elan) and Git. From the root of a fresh clone, run

```sh
lake exe cache get
./scripts/verify.sh
```

The first command obtains the pinned dependencies and their available build cache. The script builds the project, runs the [transitive axiom audit](Audit.lean), and uses `leanchecker` to replay each of the 85 proof modules in a separate process. A successful run prints an audit count of **955** and a replay count of **85**. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. [Verifier script](scripts/verify.sh) · [Lean version](lean-toolchain) · [Dependency revisions](lake-manifest.json)

To inspect the literal statement and its dependencies after building, run

```sh
printf '%s\n' 'import BooleanScott' \
  '#print BooleanScott.pure_boolean_counterexample' \
  '#print axioms BooleanScott.pure_boolean_counterexample' | lake env lean --stdin
```

To typeset the manuscript, run `mkdir -p dist` followed by `latexmk -pdf -outdir=dist paper/boolean-scott-spectral-gaps.tex` from the repository root.

## Contributions and review

OpenAI Codex developed the mathematical argument and Lean formalization under the direction of Serafim Batzoglou. Batzoglou directed the proof search and requested adversarial checks. The formalization passed the documented Lean verification. Batzoglou has not yet read the proof in full or independently verified that the formal theorem resolves the original question. Independent expert review is pending. [Citation metadata](CITATION.cff)

The proof code is available under Apache-2.0. The manuscript and proof guide are available under CC BY 4.0. [License texts and scope](LICENSE.md)
