# Licensing brief

A factual summary for an intellectual-property / software licensing review.
Prepared 2026-11-27. Everything below is verifiable from the repository and the
public records cited.

No professional review has been commissioned. The questions below are answered
in the final section as working positions, adopted by the author from the
license texts themselves, not by counsel.

## Who and what

Sole author and copyright holder named in the repository: Ezzeldin Ashraf
Mohamed Shafey Wahba (ezzeldinashraf.web@gmail.com). No other contributors,
assignments, or employer claims are recorded in it. There is no company behind
the project; licensing decisions are the author's personally.

Repository: <https://github.com/ezzasdf/erdos-problem-engine> (public).

Contents:

| Part | What it is | Size |
| --- | --- | --- |
| `ErdosTernary/` | Lean 4 formalization, Mathlib-pinned | 133 Lean files |
| Python verification scripts | number-theoretic and certificate checks | 118 files, ~20,300 lines |
| `verify_erdos_rs/`, `verify_middle/` | Rust certificate verifiers | 10 files, 2 crates |
| `paper/` | Two LaTeX manuscripts | Paper 1, Paper 2 |
| Certificates and outputs | `*.csv`, `*.txt`, JSON manifests | 15 data files |

## Current licensing state

1. **Apache-2.0 up to commit `6d68a98d8a5bdbbef982cd07b5789094e9800450`**
   (2026-11-27). Every Lean file in that tree carried the header
   `Released under Apache 2.0 license as described in the file LICENSE.`
   The repository was public in that state.
2. **PolyForm Strict 1.0.0 from commit `731bfa7` onward.** Verbatim text in
   `LICENSE-CODE`. All 261 source files now carry a header naming it. The
   `LICENSE` file is a per-part map, not a single license.
3. **Paper 1** (`paper/cantor_multiplier_dimension.*`) is CC BY 4.0, and is
   published at DOI `10.5281/zenodo.24595631` under that license.
4. **Paper 2** (`paper/erdos_ternary_repunit.*`) is CC BY 4.0, and is published
   at DOI `10.5281/zenodo.24609635` under that license. The software it
   describes has its own record, `10.5281/zenodo.24609575`, under PolyForm
   Strict 1.0.0.
5. **Two derived packages are Apache-2.0 by necessity**, not by choice:
   `contrib/palomar/` (a registry submission, published at
   `github.com/ezzasdf/erdos-ternary-carry-packet`, commit
   `911f225c66314ead429a4f60f7572dc256e3afee`) and `contrib/formal-conjectures/`
   (a proposed contribution to an Apache-2.0 upstream project).

## The business model the author wants

Charge private companies for commercial use. Allow universities and public
research organizations to use it without payment. Prevent modified versions from
circulating. Allow reading and downloading by anyone.

## Known frictions already identified

- **PolyForm Strict 1.0.0 permits noncommercial use, and its "Noncommercial
  Organizations" clause permits use by charitable organizations, educational
  institutions, public research organizations, public safety or health
  organizations, environmental protection organizations, and government
  institutions, regardless of the source of funding.** A university on an
  industry grant therefore already has a free permission. The intended business
  model and the chosen license may not match on this point.
- **The Apache-2.0 period cannot be reversed.** Anyone who obtained the code
  before `6d68a98` holds an irrevocable Apache-2.0 grant for that copy,
  including private companies, and may modify and redistribute it freely.
- **Copyright may not reach the certificates.** Numerical values and
  mathematical facts are not copyrightable; only selection, arrangement, and
  original expression might be.
- **GitHub's platform terms permit forking public repositories.** The
  repository's license states it grants no rights over a fork, but cannot
  withdraw GitHub's own permission, and the repository does not assert how the
  two interact.

## Questions for counsel

1. Is PolyForm Strict 1.0.0 suitable for the intended business model, or does
   the noncommercial-organizations clause defeat it?
2. Can private companies be charged for commercial use while the university and
   public-research exception is preserved, and if not, what license shape would
   achieve both?
3. What rights do recipients of the pre-`6d68a98` Apache-2.0 releases retain,
   and can a commercial license be sold to an organization that already holds
   those rights?
4. Do the mathematical certificates and datasets need a separate license from
   the code, and if so, what kind?
5. Can a commercial agreement be drafted that is usable with customers as
   written?

## What a commercial agreement has to answer

Scope of permitted use; whether modification is allowed; whether redistribution
is allowed; whether products containing the code may be sold; whether payment is
one-time or recurring; the duration of the grant; what happens on non-payment;
and what happens on acquisition of the author's interest or of the licensee.

`COMMERCIAL.md` currently states these as headings only. It is an offer, not an
agreement, and it grants nothing until signed.

## Facts a reviewer will want that are not yet settled

- Governing law and jurisdiction: not chosen.
- Whether licensing is done personally or through an entity: not decided.
- Whether any employer, funder, or institution has a claim on the work: none
  recorded, none disclosed.
- Whether the certificates have been offered to any third party: they have not
  been published outside this repository.

## Standing caution recorded in the repository

`LICENSE` and `NOTICE` state that the treatment of the certificates applies "to
the extent copyright subsists", and that the interaction between GitHub's fork
permission and this license is a question for counsel. Those statements are
intent, not adjudication, and are open to correction by the review.

## Working answers, adopted without counsel

These are the author's positions after reading the license texts. They are not
legal advice, they have not been reviewed, and they are written down so that a
later reviewer can see exactly what was decided and when.

**1. Is PolyForm Strict suitable for the model?**
Yes, for the model as stated: universities and public research free, private
companies pay. The noncommercial-organizations clause is not a defect here, it
is the intended half of the split. Three costs come with it: noncommercial
users cannot modify the code without written permission, so that channel is
opened separately in `COMMERCIAL.md`; the license is not open source, which
rules out some funders and venues; and a company can route work through a
university and pay nothing. The third cannot be closed by wording.

**2. Can private companies be charged while the university exception stays?**
Yes, and this already works. PolyForm Strict grants the noncommercial half;
`COMMERCIAL_AGREEMENT_TEMPLATE.md` grants the commercial half to a named
licensee. Nothing further is needed structurally.

**3. What do the pre-`6d68a98` Apache-2.0 users keep?**
Everything Apache-2.0 gives: perpetual, worldwide, royalty-free use,
modification, and redistribution, including commercially, for every copy
obtained under it. That grant cannot be withdrawn. A company that cloned before
that commit never needs to pay for that copy. The commercial license therefore
sells the current version, later work, and support, not the old one. Clause 2 of
the template names the commit so buyers know what they are getting.

**4. Do the certificates need a separate license?**
Numerical values and mathematical facts are not copyrightable. What may be
protectable is the selection, arrangement, and original expression in the files.
`LICENSE` already limits the claim to "to the extent copyright subsists". No
separate data license is adopted, because a permissive one would hand companies
the datasets for free while the code still costs money.

**5. Can an agreement be drafted?**
`COMMERCIAL_AGREEMENT_TEMPLATE.md` exists and covers all eight required points,
with a coverage table mapping each to a clause. It is unreviewed and says so.

## Residual risk after these answers

- No jurisdiction, entity, or tax position has been chosen, so the template
  cannot be signed as it stands.
- The university and public-research carve-out cannot be narrowed by the
  author's own wording; it is in the license text.
- The Apache-2.0 tail is permanent and free to competitors.
- The template now separates ownership of the Software, of Modifications, and
  of the Licensee's own material (clause 10), names affiliates explicitly rather
  than assuming the word "organization" covers them (clause 3.2 and Schedule A),
  and states that a perpetual grant is still terminable for breach with a
  defined wind-down (clauses 6.2 and 7). All three remain unreviewed.
- None of this has been read by a lawyer. The template is a starting point that
  a later reviewer can correct, not a substitute for one.
