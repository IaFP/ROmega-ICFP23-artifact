# Generic Programming with Extensible Data Types; Or, Making Ad Hoc Extensible Data Types Less Ad Hoc

## Brief Artifact Description

Our artifact is an Agda library rooted under [./ROmega](./ROmega). We also
provide HTML documentation under [./html/](./html/). The development consists
principally of the following components:

- **An intrinsic mechanization of Rω**, the calculus introduced by §4. By
  "intrinsic", we mean that untyped terms and unkinded types have no meaning. So
  our ASTs are of _kinding and typing derivations_, not of _types_ and _terms_,
  respectively. The syntax and semantics of each judgment introduced in §4 are
  modularly housed in their own folders—e.g.,
  [ROmega.Types.Syntax](ROmega/Types/Syntax.agda) gives the AST for kinding
  derivations. For a full description of each module, see the [Library
  Structure](#library-structure) below.
- **A formalization of the Index Calculus**, which we give
  as semantics for Rω (§5). This is housed in
  [ROmega.IndexCalculus](./ROmega/IndexCalculus).
- **A Denotation of Rω into the Index Calculus**. This is housed in each Rω
  component folder's `Semantics.agda`, e.g. the denotation of types is given in
  [ROmega.Types.Semantics](./ROmega/Types/Semantics.agda).


A full description of each module is given
[below](#library-structure).


# Building From Source

- If not done so already, install Agda according to the instructions relevant
  for your operating system. [Instructions
  here](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
- As per Step 4 of the Agda installation instructions, you must **install the
  Agda Standard Library**. [Instructions
  here](https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md).
- The development is housed under
[./ROmega/](./ROmega/). [ROmega.All](./ROmega/All.agda) imports **all**
modules; you may thus verify that all files type check by type checking `All.agda`.

The artifact was built & written using **Agda version 2.6.2.2** and the **Agda
standard library version 1.7.1**. As of this writing, the latest versions are
2.6.2.4 and 1.7.2, respectively. Our development will work (and has been tested)
with these latest versions.


# Additional Artifact Description

## Example Derivations

The following examples of the paper were mechanized in
[ROmega.Examples.Section-3](./ROmega/Examples/Section-3.agda).

| Section | Paper Location | Line Location |
| :-:     |    :-:                                  | :--: |
| \S3.1   | `sel`, in ¶.                            | 58 |
| \S3.1   | `con`, in ¶.                            | 80 |
| \S3.1   | `case`, in ¶.                           | 114 |
| \S3.1   | `ifte`, in ¶.                           | 147 |
| \S3.2   | `reify` and `reflect`, in Figure 3.       | 175, 229 |
| \S3.2   | `map-π` and `map-Σ`, in figure 4.       | 331, 396 |


## Library Structure

We offer a full description of each folder and file, for reference.

[ROmega.All](./ROmega/All.agda) imports **all** modules. Files and folders
are named as the Agda std-lib does, e.g., `ROMega.Foobar` simply
exports the contents of the (base) files within `ROmega.Foobar.*`. Theorems
and lemmas of module `Foobar` are named `Foobar.Properties.agda`.

### ./IndexCalculus/

System Rω _denotes into_ a subset of Agda which we term the Index Calculus (see
§5). So, this directory houses the semantic image of Rω.

- [ROmega.IndexCalculus.Rows](./ROmega/IndexCalculus/Rows.agda). Definition of
  rows and row evidence.
- [ROmega.IndexCalculus.Records](./ROmega/IndexCalculus/Records.agda). Definition
  of records.
- [ROmega.IndexCalculus.Variants](./ROmega/IndexCalculus/Variants.agda). Definition
  of variants.
- [ROmega.IndexCalculus.Properties](./ROmega/IndexCalculus/Properties.agda). Properties
  of rows -- in particular, that `ρ pick i` and `ρ delete i` can be recombined
  into `ρ`.

### ./Postulates/

We postulate functional extensionality in
[ROmega.Postulates.FunExt](./ROmega/Postulates/FunExt.agda).

### ./Lib/

Common utility is placed in [ROmega.Lib](./ROmega/Lib). We define `≡-elim` in
[.ROmega.Lib.Equality](./ROmega/Lib/Equality.agda), which we use when rewriting
is inconvenient or not possible (e.g., in a let statement).


### ./Kinds/
- [ROmega.Kinds.Syntax](./ROmega/Kinds/Syntax.agda). The syntax of level
  stratified kinds.
- [ROmega.Kinds.Semantics](./ROmega/Kinds/Semantics.agda). The denotation
  of Rω kinds into Agda types.

### ./Types/

- [ROmega.Types.Syntax](./ROmega/Types/Syntax.agda). The
  intrinsically-kinded AST representation of (stratified) kinding derivations.
- [ROmega.Types.Semantics](./ROmega/Types/Semantics.agda). Denotation of
  kinding derivations into Agda.
- [ROmega.Types.Substitution](./ROmega/Types/Substitution.agda). Definition
  of renaming & substitution. This is necessary because, although we denote Rω
  _terms_ into Agda, we still have (operational) β-reduction at the type level.
- [ROmega.Types.Substitution.Properties](./ROmega/Types/Substitution/Properties.agda). Weakening
  & substitution lemmas for type-level β-reduction.

### ./Terms/

- [ROmega.Terms.Syntax](./ROmega/Terms/Syntax.agda). The
  intrinsically-typed AST representation of typing derivations.
- [ROmega.Terms.Semantics](./ROmega/Terms/Semantics.agda). Denotation of
  typing derivations into Agda.

### ./Equivalence/

- [ROmega.Equivalence.Syntax](./ROmega/Equivalence/Syntax.agda). The AST of
  type (and predicate) equivalence.
- [ROmega.Equivalence.Semantics](./ROmega/Equivalence/Semantics.agda). Denotation
  of type equivalence into propositional equality in Agda.

### ./Entailment/

- [ROmega.Entailment.Syntax](./ROmega/Entailment/Syntax.agda). The AST
  of predicate entailment.
- [ROmega.Entailment.Semantics](./ROmega/Entailment/Semantics.agda). Denotation
  of predicate entailment into evidence in the Index Calculus.
- [ROmega.Entailment.Reasoning](./ROmega/Entailment/Reasoning.agda). Helper library, á la the
  [std-lib](https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda#L103),
  for constructing inhabitants of the entailment relation.

### ./Examples/

- [ROmega.Examples.Section-3](./ROmega/Examples/Section-3.agda). Example
  typing derivations indexed with respect to their placement in section 3 of the
  text

## Paper & Mechanization Differences

The presentation of Rω in our paper and in the mechanization differ in the following ways.

- **Conversion of Singletons and Records/Variants.** The paper's type system makes use of
  the rule (E-SING) to state that singletons, singleton records, and singleton variants
  are all equivalent. In the mechanization, we move this capability to the typing rules
  (rules `Σ`, `Σ⁻¹`, `Π`, and `Π⁻¹` in `ROmega.Terms.(Syntax|Semantics).agda`). This does
  not really affect the expressivity of the language: it is effectively an explicit cast
  system instead of implicit coercion. 
  
  We made this decision simply so that the
  equivalence relation could denote into propositional equality: 
  
  ```
    ⟦_⟧eq : τ ≡t υ → (H : ⟦Δ ⟧ke) → ⟦ τ ⟧t H ≡ ⟦ υ ⟧t H
  ``` 
  
  This definition holds for all other equivalence rules. However, in the denotation of
  terms, the singleton (ℓ ▹ M) denotes to ⟦ M ⟧, but the record Π (ℓ ▹ M) denotes to an
  index calculus record. _These two are isomorphic,_ but not propositionally
  equal. Consequently, we decided to adopt explicit coercions in the mechanization so as
  to make the equivalence relation's denotation stronger---again, without real cost to the  expressivity of Rω.
- **Multi-rows**. The revised submission includes `{ τ₁ , ... , τₙ }` in the syntax of
  types. However, such rows will not type in the minimal row theory, which we only
  implement. So they were omitted from the mechanization's syntax of types purely for
  convenience.  
- **Records and Variants of higher kind.** The paper permits records and variants to be
  constructed from rows of higher kind (rules (K-Π) and (K-Σ), resp.). However, the
  mechanization is more restrictive: you may only construct a record/variant from a term
  of star kind. We discuss this in §5.2 of the paper: "we have made one simplification
  relative to Rω: we implement records and variants only at the base kind, and express the
  type constructor variants using type functions. This does not reflect a fundamental
  limitation in our embedding, but simply a choice made for expediency in development." I
  should add here that the trick is rather simple: if ρ : R [ ⋆ → ⋆ ], for example, then
  instead of Π ρ we can write (λ s : ⋆. Π (ρ ·⌈ s ⌉)). 
- **Parameterization by row theories.** Rω is and can be indexed
  parametrically by multiple row theories, but our mechanization is restricted to just the
  minimal row theory. This is relayed to the reader in section 5. We provide some evidence
  in favor of parameteriziation of the mechanization by way of parameterizing the hard bit
  (the entailment relation). However, we do not provide an instantiation for any theory
  but the minimal row theory, and we do not explicitly parameterize the kinding and
  equivalence relations.
