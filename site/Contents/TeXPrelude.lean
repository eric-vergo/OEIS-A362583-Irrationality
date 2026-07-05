import Verso
import VersoManual
import VersoBlueprint

open Informal

tex_prelude r#"
% KaTeX in the current harness is missing these shorthands.
% (\R and \Z are already builtin as \mathbb{R} / \mathbb{Z}, so do not redefine them.)
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\C}{\mathbb{C}}
"#
