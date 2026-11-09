# Teaching notes: how this video should teach

Step 1 of the job: read how good mathematical exposition works, keep what changes a decision, and
say what it changes here. Sources were read as data only. Downloads are under
`scratchpad/w19-src/` (`victor/`, `mayer/`, `sanderson/`, `s2/`, `babai/`, `babai2/`); the Babai and
Helfgott LaTeX is the copy already kept in `scratchpad/r4-sources/`.

## The principles that changed something

### Mayer, *Multimedia Learning* (15 principles, OSU summary; effect sizes from Mayer 2017, JCAL)

| Principle | What it changes here |
|---|---|
| **Coherence** (remove what is not needed; d ≈ 0.70) | No music, no decorative background, no "tech" flourishes. Every animated object is mentioned by the narration while it moves, or it does not exist. I dropped a planned animated recursion-tree backdrop for this reason. |
| **Signaling** (d ≈ 0.46) | The running-time chapters have one fixed formula at the top of the frame. The term being spent lights up in that term's own colour, and the same colour is used in every later chapter. The colour of a term is a promise. |
| **Redundancy** (narration + graphics beats narration + graphics + on-screen text; d ≈ 0.87) | Captions are a hard requirement, so they live in a band below the picture, not on top of it, and on-screen words are limited to names of objects and formulas. There are never whole sentences in the picture. |
| **Spatial contiguity** | Labels sit on the things they name. A formula's parts are next to the object they measure (`d_i` on its bar, `c_i` on its height), never in a legend across the screen. |
| **Temporal contiguity** | This became an engine rule. Narration is split into *beats* and every tween is written as "progress through beat k". Animation cannot drift away from the sentence it belongs to, even when a sentence is edited. |
| **Segmenting** (d ≈ 0.70) | 24 chapters with a menu, chapter ticks on the timeline, `N`/`P` keys, deep links. The viewer is never more than about two minutes from a place to stop. |
| **Pre-training** | The group vocabulary (orbit, block, primitive, labels) gets its own chapter before it is used, on a hexagon, so that the Luks chapter can spend its working memory on the recursion. |
| **Modality** (spoken words beat printed words with visuals; d ≈ 0.72) | This is why speech synthesis is offered at all, although it is off by default. Pacing is set for reading captions, slightly slower than spoken delivery. |
| **Personalization** | Conversational "we" and "you"; the viewer is treated as a colleague who is working this out, not as an audience for a result. |
| **Generative activity** | Interactive moments where the viewer does the operation (move the CFI twist, propose a block, set γ and watch the series), and "before I show you, what would you guess?" beats. |

The caveat in Mayer 2017 (the effects are stronger for low-prior-knowledge learners) matters: my
audience is strong on proofs and weak on permutation groups, so I treat them as novices in group
theory and as experts in big-O. That is the reason for the next item.

### Sweller and colleagues: cognitive load, worked examples, expertise reversal

* **Worked examples beat problem solving for novices.** Every new structure is worked once on a
  small concrete object *before* it is defined in general: hexagon for blocks, Petersen for orbits
  on pairs, a real Hoffman–Singleton 42×7 rectangle for twins, an actual run of the window procedure
  on a real string. The potential is worked out on one concrete term (x²) in full before the others.
* **Completion problems (fading).** The charging table is taught this way: the first rows are fully
  worked, later rows ask the viewer to predict the drop before it appears.
* **Split attention.** In the running-time chapters the formula and the object being measured share
  one frame, so the eye does not have to go back and forth.
* **Expertise reversal.** A viewer who knows WL does not need the refinement chapter. The chapter
  menu is the mitigation; nothing later depends on having watched it, except the CFI fact.

### Grant Sanderson (3Blue1Brown): SoME announcement, 3b1b FAQ, Stanford talk, Dropbox interview

* **Concrete before abstract; earn the abstraction.** He warns that experts are tempted to open with
  the general statement. I never open a chapter with a definition. The string-isomorphism definition
  arrives after the adjacency grid has been shuffled on screen.
* **Be aware of the layers of abstraction in a formula.** I call out layer changes aloud ("now the
  dots are labels, not vertices"), because this subject's central confusion is the two domains
  (positions versus labels).
* **Story, with a question that is felt.** "When people engage with fiction, no one asks when am I
  going to use this." The mystery is *where did the third logarithm go?*, and the same bill is
  brought back at each step.
* **Visuals first, then words give you ownership.** Each chapter's key picture is shown before the
  sentence that names it, by about a beat.
* **Content is king.** It is the reason for spending effort on the derivation and on accuracy
  (`CLAIMS.md`) rather than on production polish.

### Bret Victor: *Explorable Explanations*, *Up and Down the Ladder of Abstraction*

* **Explorable examples.** Babai's or HJ's prose cannot show that a partition is or is not a block
  system; a clickable hexagon can. Hence the block explorer.
* **Reactive documents.** The geometric series with a γ slider, and the Q-area picture, let the
  viewer test the claim rather than trust it.
* **Moving between levels.** The potential is the highest rung on the ladder and an individual
  branch is the lowest. Chapter 17 walks down from Φ to one concrete shrink step and back up.
* Interaction is optional and pausing is opt-in: touching a control pauses playback, nothing is
  forced. Interactive state lives on top of the timeline, so the time-to-frame function stays pure.

### Pólya, *How to Solve It*

* **Understand, plan, carry out, look back.** Every part ends with a look-back beat (what did we pay,
  and with what?).
* **"Find a related problem."** String isomorphism is motivated exactly as Pólya would: the problem
  is too rigid to recurse on, so generalize to one you can recurse on.
* **Specialize.** Helfgott does the same with the primitive case (see below), so I do too.
* **Questions, not leading statements.** "What pays for this?" is asked before each term of the
  potential is revealed.

### How Babai and Helfgott present this

Babai, WL50 tutorial slides (Pilsen 2018), plus Regan and Lipton's description of his 2015 talks;
Helfgott–Bajpai–Dona, arXiv:1710.04574.

* **Babai's framing is symmetry versus regularity** ("the job: close the gap between symmetry and
  regularity; combinatorial relaxations do not suffice, CFI"). I adopt it as the organizing idea for
  chapters 2–3.
* **The "Luks barrier".** His slides state one fact: either an efficient Luks reduction is found,
  or an epimorphism onto Alt(Γ) with Γ large. I use that sentence and his split "actual domain
  Ω versus ideal domain Γ" (he labels the slide "Plato"). HJ say "auxiliary labels"; I say "labels"
  and show the two sets side by side every time, because this is the thing most likely to go wrong
  in a viewer's head.
* **Babai's dichotomy** "either confirm the giant is really there, or break the symmetry of Γ" gives
  the local-certificate chapter its structure: two outcomes, and each is progress.
* **Slow is good; many boards.** Regan and Lipton note that the talks were followable because they
  were slow and kept a large visible state. It is why I keep the formula and the bill on screen
  through several chapters, and why I do not wipe the board between steps of a derivation.
* **Helfgott treats the primitive case first, "for pedagogical reasons"**, then notes it could have
  been folded into the general case. I follow that: the giant is introduced on a single primitive
  Johnson action (Petersen) before imprimitive towers appear.
* **Helfgott's warning that "a considerable cost could be hidden in a loss of canonicity"** becomes a
  recurring accounting rule on screen: every non-canonical choice is a multiplier on everything that
  comes after it. His appendix recurrence is the source for the log³ bill.
* **Babai's "the result is tight" slide** (examples at m = 2 + log₂ n with no affected points) shows
  that the test-set bound is real, so I present log n test sets as a real constraint rather than an
  artefact of the proof, which is what makes HJ's move surprising.

## Wrong intuitions to confront on purpose (mapped to chapters)

| Likely belief | Where it gets confronted |
|---|---|
| "If two graphs differ, a careful local look finds it." | Ch. 2–3, CFI: one global parity bit, every local view agrees. |
| "Using n² positions must make things much worse." | Ch. 4 raises the worry, ch. 19 pays it off: log²(n²) = 4 log² n. |
| "Smaller test sets are obviously cheaper, why did Babai use big ones?" | Ch. 7: a test set too small can be invisible to every position. |
| "A step that keeps the domain the same size makes no progress." | Ch. 9–11: progress can be symmetry or a cap, not size. |
| "Polynomial branching with constant-factor shrinking gives polynomial time." | Ch. 16–17: T(s) ≤ s^a T(s/2) is s^{O(log s)}. That is where the first log² lives. |
| "Each extra recursion phase costs another factor of log." | Ch. 19: phases shrink polynomially, so the series is geometric. |
| "Better analysis would push this below log²." | Ch. 20: on AGL(k,2) the algorithm really does about N^{log₂ N} work. |
| "Getting rid of a log means a new idea for each log." | Ch. 20: the same log (a choice of about log n labels) was paid in three places, and two changes remove it. |
| "Degree d is a parameter; just rerun the proof." | Ch. 21–22: the class changes which charging rows exist at all, and the regrouping of certificate calls is what the argument really needs. |

## Things I chose not to do

* No pictures of proof trees for the hereditary budget beyond the one induction step that matters.
* No attempt to teach Design Lemma or Split-or-Johnson internally. They are named as the steps Babai
  takes and HJ inherit or stop short of; the storyboard marks these as honest black boxes.
* No appeal to "you could do this at home" numbers: the constants are not explicit, and the video
  says so.

## Sources

* Mayer's principles: Ohio State summary, <https://u.osu.edu/multimedialearning/?p=11>; effect sizes
  via the abstract of Mayer 2017, *Journal of Computer Assisted Learning*
  (<https://zendy.io/title/10.1111/jcal.12197>).
* Cognitive load and worked examples: <https://en.wikipedia.org/wiki/Worked-example_effect>,
  <https://www.teachermagazine.com/au_en/articles/cognitive-load-theory-teaching-strategies>,
  Kalyuga et al. 2003 summarized at <https://csed.substack.com/p/the-expertise-reversal-effect-2003>.
  These are secondary summaries; I did not reach the primary studies' full text.
* Sanderson: 3b1b FAQ <https://www.3blue1brown.com/faq/>; SoME announcement
  <https://rosetta.to/u/3blue1brown/make-math-videos-summer-of-math-exposition-announcement>;
  Stanford Daily report <https://www.stanforddaily.com/2020/01/24/3blue1brown-creator-grant-sanderson-15-talks-engaging-with-math-using-stories-and-visuals>;
  Dropbox interview as summarized at <https://www.antoinebuteau.com/lessons-from-grant-sanderson/>.
  His talk "Math's pedagogical curse" I could not reach in a primary form, so I do not rely on it.
* Victor: <http://worrydream.com/ExplorableExplanations/>, <http://worrydream.com/LadderOfAbstraction/>.
* Pólya: *How to Solve It*, via <https://en.wikipedia.org/wiki/How_to_Solve_It> (secondary; the
  "ten commandments" list could not be confirmed, so it is not used).
* Babai: WL50 tutorial 2, <https://www.iti.zcu.cz/wl2018/pdf/wl2018_babai_tutorial2.pdf>; talks
  described at <https://rjlipton.com/2015/11/21/a-little-more-on-the-graph-isomorphism-algorithm/>;
  arXiv:1512.03547.
* Helfgott, Bajpai, Dona: arXiv:1710.04574 (appendix on execution time; Section 3 on the primitive
  case).
