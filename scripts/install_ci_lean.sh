#!/usr/bin/env bash
# Install the reviewed release bytes without elan's unrelated latest-release lookup.
set -euo pipefail

toolchain_file="${1:-lean-toolchain}"
expected_toolchain='leanprover/lean4:v4.33.1'
if [[ "$(cat "$toolchain_file")" != "$expected_toolchain" ]]; then
  echo "CI installer requires the reviewed pin $expected_toolchain" >&2
  exit 1
fi
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'CI installer supports only Linux x86_64' >&2
  exit 1
fi

elan_binary="${ELAN_HOME:-$HOME/.elan}/bin/elan"
"$elan_binary" --version
install_dir="$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/lean-harness-ci-lean.XXXXXX")"
archive="$install_dir/lean.tar.zst"
# The linked directory must survive this step for later build/test steps.
installed=false
trap 'if [[ "$installed" != true ]]; then rm -rf -- "$install_dir"; fi' EXIT

curl_options=(-sSfL --retry 3 --retry-delay 2 --retry-max-time 600
              --connect-timeout 20 --max-time 300)
if ! curl "${curl_options[@]}" \
    https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst \
    -o "$archive"; then
  curl "${curl_options[@]}" -H 'Accept: application/octet-stream' \
    https://api.github.com/repos/leanprover/lean4/releases/assets/523687465 -o "$archive"
fi
printf '%s  %s\n' '890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235' "$archive" |
  sha256sum --check --status
mkdir "$install_dir/toolchain"
tar --zstd -xf "$archive" --strip-components=1 -C "$install_dir/toolchain"
rm -- "$archive"
"$elan_binary" toolchain link "$expected_toolchain" "$install_dir/toolchain"
"$elan_binary" run "$expected_toolchain" lean --version
"$elan_binary" run "$expected_toolchain" lake --version
installed=true
