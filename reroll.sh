#!/bin/bash
# bot.py picks a fresh random patrol phase in every match, so each submission is a new draw.
# This pushes an empty commit (in case the site won't take the same commit twice).
set -e
cd "$(dirname "$0")"
git commit -q --allow-empty -m "reroll $(date +%H:%M:%S)"
git push -q
echo "pushed $(git log -1 --format='%h %s') -> now submit the repo URL on the track page"
