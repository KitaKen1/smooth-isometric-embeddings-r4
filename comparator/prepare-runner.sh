#!/usr/bin/env bash
# Prepare a GitHub runner for the Lean builds: free disk space (the build of `lean/` takes about
# 15 GB, mostly the C output in .lake/build/ir, and the Mathlib cache about 6 GB), install GNU time
# and elan, and record the resources of the runner in $RUNNER_TEMP/runner.txt.
set -eu
sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /usr/local/.ghcup /opt/hostedtoolcache \
  /usr/local/share/boost /usr/share/swift /usr/local/share/powershell /usr/lib/jvm /opt/microsoft \
  /opt/google /opt/az /usr/local/share/chromium /usr/local/julia*
sudo docker system prune -af > /dev/null 2>&1 || true
sudo apt-get install -y -q time > /dev/null
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$RUNNER_TEMP/elan-init.sh"
sh "$RUNNER_TEMP/elan-init.sh" -y --default-toolchain none > /dev/null
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
{ echo "cores: $(nproc)"; free -g; df -h / /mnt 2>/dev/null || true; } > "$RUNNER_TEMP/runner.txt"
cat "$RUNNER_TEMP/runner.txt"
