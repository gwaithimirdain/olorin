// The numbers in the unlock rules, kept apart from main.js so the tests can read them too
// (test/lib/levels.js loads this file the way it loads levels.js, so it must stay pure data: no
// imports).  See worldGateBlockers and unlockBlockers in main.js for the rules themselves.

// The fractions of a world or stage that the unlock rules ask to be complete.  A world's fractions
// are of its non-bonus levels.
// Rule 1 (and 1a, a course's world gating itself): every world this one follows, at this difficulty.
export const PREVIOUS_WORLD_FRACTION = 0.5; // 0.8;
// Rule 2: every world that follows this one, one difficulty down.
export const FOLLOWING_WORLD_FRACTION = 0.5;
// Rule 3: every world followed by a world this one follows, one difficulty up.
export const EARLIER_WORLD_FRACTION = 0; // 0.5;
// Rule 4: each of this stage's prerequisite stages, at this difficulty.
export const PREVIOUS_STAGE_FRACTION = 0.7;

// Rule 5: how many of the levels before a level in its stage may be left incomplete -- so a
// stage's first SKIPPABLE_EARLIER_LEVELS + 1 levels are available as soon as it opens.
export const SKIPPABLE_EARLIER_LEVELS = 4; //2;

// Rule 7: how many completions must pass before a just-completed difficulty stops re-locking the
// next.
export const RECENT_COMPLETION_WINDOW = 10;
