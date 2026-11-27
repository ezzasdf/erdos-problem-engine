# Commercial license agreement — template

**This is a template, not legal advice, and not a substitute for a lawyer.**
It is a plain-language starting point built from the eight questions a customer
agreement has to answer. Fill every bracketed field. If you ever can afford a
review, this is the document to hand over.

Delete this notice only after you have decided, deliberately, that you are
signing it without review.

---

**Commercial License Agreement**

**1. Parties**

This agreement is between [LICENSOR LEGAL NAME], [ADDRESS], ("Licensor") and
[LICENSEE LEGAL NAME], [REGISTRATION NUMBER], [ADDRESS] ("Licensee").

**2. The Software**

"Software" means the source code, build files, and scripts at
[REPOSITORY URL] as of commit [FULL COMMIT SHA], together with any part of it
the Licensee uses. It excludes the papers in `paper/`, which carry their own
terms, and excludes third-party components such as Lean 4 and Mathlib, which
remain under their own licenses.

**3. What the Licensee may do**

3.1 Licensor grants Licensee a non-exclusive, non-transferable right to:

- (a) use, run, and reproduce the Software, including commercially;
- (b) modify the Software and create derivative works from it;
- (c) [INCLUDE OR DELETE] distribute the Software and derivative works, in
  source or binary form, to end users as part of [PRODUCT OR SERVICE].

3.2 Choose one:

- [OPTION A — per organization] The grant covers all employees and contractors
  of Licensee and its subsidiaries, but no other entity.
- [OPTION B — per product] The grant covers only [PRODUCT NAME] and no other
  product.

**4. What the Licensee may not do**

4.1 Licensee may not sublicense, resell, or provide the Software as a
standalone product, or as a competing library, dataset, or service.

4.2 Licensee may not remove or alter copyright, license, or attribution notices.

4.3 Licensee may not state or imply that Licensor endorses Licensee or its
products.

4.4 Licensee may not use the name of Licensor or of the research project in
advertising without written permission.

**5. Fees**

5.1 Fee: [AMOUNT] [CURRENCY], payable [ONE-TIME ON SIGNATURE / ANNUALLY IN
ADVANCE / QUARTERLY].

5.2 Invoices are due within [30] days.

5.3 Late payment accrues interest at [RATE]% per month, or the maximum allowed
by law, whichever is lower.

5.4 Fees are exclusive of taxes; Licensee pays applicable taxes other than
Licensor's income tax.

**6. Term**

6.1 Choose one:

- [PERPETUAL] The grant is perpetual and irrevocable for the Software version
  named in clause 2, subject to termination under clause 7.
- [FIXED TERM] The grant runs from [START DATE] for [N] months and renews only
  by written agreement.

**7. Termination**

7.1 Either party may terminate on [30] days' written notice of a material
breach that is not cured within that period.

7.2 Licensor may terminate immediately if Licensee fails to pay within [15] days
after written notice.

7.3 On termination, Licensee must stop all use of the Software and delete or
destroy copies, except that:

- (a) Licensee may retain one archival copy for legal and compliance purposes;
- (b) products already shipped to end users before termination may continue to
  be used by those end users;
- (c) Licensee has [30] days to wind down live deployments.

7.4 Clauses 4, 8, 9, 10, and 12 survive termination.

**8. No warranty**

The Software is provided "as is". Licensor disclaims all warranties, express or
implied, including merchantability, fitness for a particular purpose, and
non-infringement. Licensor does not warrant that the Software is free of errors
or suitable for Licensee's use.

**9. Limitation of liability**

9.1 Licensor's total liability under this agreement is limited to the fees paid
in the [12] months before the claim.

9.2 Neither party is liable for indirect, incidental, special, or consequential
damages, or lost profits.

9.3 Nothing in this agreement limits liability that cannot be limited by law.

**10. Intellectual property**

10.1 Licensor retains all copyright and other rights in the Software. No rights
are granted except those stated in clause 3.

10.2 Licensee retains all rights in its own modifications and products.

10.3 Choose one:

- [GRANT BACK] Licensee grants Licensor a non-exclusive, perpetual, royalty-free
  right to use any modifications Licensee chooses to contribute back.
- [NO GRANT BACK] Licensee keeps its modifications private.

**11. Support**

[DELETE IF NOT INCLUDED] Licensor will respond to reasonable technical questions
within [5] business days. This is not a warranty and creates no service level.

**12. Assignment and change of control**

12.1 Licensee may not assign this agreement without Licensor's written consent,
except to a successor in a merger or acquisition of substantially all its
assets, provided the successor agrees in writing to be bound.

12.2 If Licensor transfers its rights in the Software, the transferee takes them
subject to this agreement, and the grant in clause 3 continues.

**13. Governing law and disputes**

This agreement is governed by the laws of [JURISDICTION]. The parties submit to
the exclusive jurisdiction of the courts of [PLACE]. Before filing, the parties
will attempt to resolve the dispute in good faith for [30] days.

**14. General**

14.1 This is the entire agreement and replaces any prior discussion.

14.2 Amendments must be in writing and signed by both parties.

14.3 If a clause is unenforceable, the rest remains in force.

14.4 Notices go to the addresses in clause 1 and are effective on delivery.

**Signed**

Licensor: ______________________  Date: __________

Name and title: ______________________

Licensee: ______________________  Date: __________

Name and title: ______________________

---

## Coverage check

Each requirement, and the clause that answers it:

| Requirement | Clause |
| --- | --- |
| What may they use? | 2, 3.1, 3.2 |
| May they modify? | 3.1(b), 10.2, 10.3 |
| May they redistribute? | 3.1(c) |
| May they sell products containing it? | 3.1(a) with 4.1 limits |
| One-time or recurring payment? | 5.1 |
| How long does permission last? | 6.1 |
| What if they stop paying? | 7.2, 7.3 |
| What if the project is acquired? | 12.1, 12.2 |

## What this template does not do

- It does not choose your jurisdiction, entity, or tax treatment.
- It does not address patents, export control, data protection, or employment
  claims, which vary by country.
- It does not decide whether the older Apache-2.0 users still get a free
  license. They do, and clause 2 names the commit precisely so that the scope of
  what you are selling is unambiguous.
