#!/usr/bin/env bash
#
# deploy-ghpages.sh — publish the generated A362583 blueprint site to the
# `gh-pages` branch of eric-vergo/OEIS-A362583-Irrationality (served at
# https://eric-vergo.github.io/OEIS-A362583-Irrationality/).
#
# ⚠️  LEGACY FALLBACK ONLY.  Deploys are now owned by GitHub Actions (the
# `site.yml` workflow builds the site and publishes it via the Pages
# `upload-pages-artifact` / `deploy-pages` path).  This manual orphan-branch
# force-push script is kept solely as a break-glass fallback for when Actions
# is unavailable.  It ONLY works if the repository's Pages source has first been
# flipped back from "GitHub Actions" mode to legacy branch mode:
#
#     gh api -X PUT repos/eric-vergo/OEIS-A362583-Irrationality/pages \
#       -f build_type=legacy \
#       -f "source[branch]=gh-pages" \
#       -f "source[path]=/"
#
# Otherwise a `gh-pages` push is ignored and the live URL keeps serving the last
# Actions deploy.
#
# This script BUILDS NOTHING.  It assumes `_out/site/html-multi` already exists
# and is fresh.  Regenerate it first, from this directory, with:
#
#     rm -rf _out/site
#     lake build Contents
#     lake env lean --run Main.lean --output _out/site
#
# The site is sub-path-safe: every page carries a depth-adjusted relative
# `<base href>`, and the client JS (command palette, search, graph, xref
# redirects) resolves data addresses against that base — so it works served
# from the `/OEIS-A362583-Irrationality/` sub-path without any rewriting.
#
# Idempotent and safe to re-run: each invocation clones the repo fresh into a
# temporary directory, resets an ORPHAN `gh-pages` branch to exactly the current
# site contents (no history accumulation), and force-pushes.  `main` is never
# touched.
#
set -euo pipefail

REPO_URL="https://github.com/eric-vergo/OEIS-A362583-Irrationality.git"
BRANCH="gh-pages"

# Resolve the site directory relative to this script, so the working directory
# does not matter.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE_DIR="${SCRIPT_DIR}/_out/site/html-multi"

# --- Preconditions -----------------------------------------------------------

if [[ ! -f "${SITE_DIR}/index.html" ]]; then
  echo "ERROR: ${SITE_DIR}/index.html not found." >&2
  echo "       Regenerate the site before deploying (see header comment)." >&2
  exit 1
fi

# Guard against an accidentally-empty or half-generated site.
FILE_COUNT="$(find "${SITE_DIR}" -type f | wc -l | tr -d ' ')"
if [[ "${FILE_COUNT}" -lt 50 ]]; then
  echo "ERROR: ${SITE_DIR} has only ${FILE_COUNT} files — refusing to deploy a" >&2
  echo "       suspiciously small site.  Regenerate and retry." >&2
  exit 1
fi
echo "Site source : ${SITE_DIR} (${FILE_COUNT} files)"

# --- Fresh clone into a temp dir ---------------------------------------------

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/a362583-ghpages.XXXXXX")"
cleanup() { rm -rf "${WORKDIR}"; }
trap cleanup EXIT

echo "Cloning     : ${REPO_URL}"
git clone --quiet "${REPO_URL}" "${WORKDIR}/repo"
cd "${WORKDIR}/repo"

# --- Reset the orphan gh-pages branch to the current site contents -----------

# Orphan branch => no shared history with main, single-commit deploy each time.
git checkout --quiet --orphan "${BRANCH}"
git rm  -rqf . >/dev/null 2>&1 || true   # clear the index (main's tree)
git clean -qfdx                          # clear any stray untracked files

# Copy the site tree verbatim, including dot- and dash-prefixed asset dirs
# (e.g. `-verso-data/`, `-verso-search/`).  tar preserves the full tree; the
# leading `./` keeps dash-prefixed entries from being read as options.
( cd "${SITE_DIR}" && tar cf - . ) | tar xf - -C .

# `.nojekyll` is REQUIRED: without it GitHub Pages runs the content through
# Jekyll, which silently drops files and directories whose names begin with a
# dot or an underscore/dash — exactly this site's asset directories.
touch .nojekyll

# --- Commit and force-push ---------------------------------------------------

git add -A
if git diff --cached --quiet; then
  echo "Result      : no changes — ${BRANCH} already matches the current site."
  exit 0
fi

DATE="$(date -u +%Y-%m-%d)"
git \
  -c user.name="A362583 Blueprint Deploy" \
  -c user.email="noreply@anthropic.com" \
  commit --quiet -m "deploy blueprint site ${DATE}"

echo "Pushing     : ${BRANCH} (force) -> ${REPO_URL}"
git push --quiet --force origin "${BRANCH}"

echo "Result      : deployed $(git rev-parse --short HEAD) to ${BRANCH}."
echo "Live URL    : https://eric-vergo.github.io/OEIS-A362583-Irrationality/"
