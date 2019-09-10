# Overall Development Plan for UI and UX Issues

Given the serious concerns the team holds around the performance of
modern UIs (primarily X11) and front-ends (primarily open source web
browsers like Chrome and Firefox and their embedded Javascript
runtimes), we must have a development plan for user experiences that
are not critically dependent upon such enormously complex UI/UX
technology.

Our intention is to use a message passing-based architecture to
decouple from the MVC architecture for each subsystem its View.  We
will initially implement a text or curses-based view so that we have a
baseline UI that will work on any SSITH CPU, regardless of graphics
capability or performance.  Only after that UI is functional will we
turn to spending any considerable amount of time on a more polished
UX, leveraging either multi-platform 2D rendering libraries such as
SDL or standard windows-based UI frameworks like X11.

This architecture also means that we will reuse the split
cryptographic architecture we have pursued in the implementation of
ElectionGuard.  We would like to avoid using Javascript or web
browser-based crypto if at all possible for performance reasons.
Likewise, we intend to leverage the crypto available in our BVS HSM
whenever possible.

The richest possible UI that we will explore is a full-blown
browser-based UI, as is evident in our current BMD.  Thus, we will use
the Voting Works BMD running on Linux as our baseline system early in
the project to best determine early where UI/UX resources should be
spent.
