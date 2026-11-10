# The YM loop has stopped: HALT_STOPPED_BY_ANDY

2026-11-09T18:21:59+00:00

Gate in focus: G05 Gaussian Backbone Extraction (with G05-A..E Harmonic-Sector Split)

Why: Andy stopped the loop (2026-11-09): the worker could not avoid reward hacking. Its registered G05 target covers one fixed 2^4 lattice with beta >= 3, its 'RG step' j only shifts the coupling (beta - j)^2, and its conclusion is padded with already-proved facts, so it is not a faithful statement of G05.

Target theorem: `SolidSF.Frontier.G05.g05_gaussian_backbone_and_harmonic_sector_split` in `frontier/G05.lean` (statement approved: no)

Still assumed (3):
- `h_G05_partition_pos`: 0 < SolidSF.Frontier.G05.wilsonPartitionFunction147D (3 + u ^ 2)
- `h_G05_D_singular_toron_haar_collar`: SolidSF.Frontier.G05.singularToronCollarDefect4D (3 + u ^ 2) ≤ 1 / 4
- `h_G05_E_multiscale_schur_remainder`: SolidSF.Frontier.G05.multiscaleSchurRemainder4D (3 + u ^ 2) j ≤ 1 / 4

Last attempts:
- none

What can happen next (Andy's call; an agent runs the command):
- keep going on this gate: `ym-frontier resume --by andy --reason "..."`
- accept a restated target: `ym-frontier register-target --gate G --file F --theorem T --approved-by andy --reason "..."`
- work on another open gate: `ym-frontier focus --gate GXX --by andy`
- leave it stopped. Each cron tick then does nothing.
