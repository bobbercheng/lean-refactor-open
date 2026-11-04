# shellcheck shell=sh
# BASH_ENV of the job (run.sh; 2026-11-01): bash reads this file in every NON-INTERACTIVE shell, and in a login shell (`bash -lc`: the
# model's shell tool in harness/agent.py) AFTER /etc/profile and ~/.bash_profile. A profile that rebuilds PATH (SUSE-style
# /etc/profile, a site profile) would otherwise hide the package's tools from the model: ripgrep and the Python wrapper in .lra/,
# lake / lean in $ELAN_HOME/bin. Each directory of LRA_SHELL_PATH_PREPEND that PATH lacks is put back in front; nothing is removed,
# and a PATH that already has them is left exactly as it is. Never handed into the vLLM image (lib.sh LRA_IMAGE_UNSET).
if [ -n "${LRA_SHELL_PATH_PREPEND:-}" ]; then
  _lra_ifs=$IFS; IFS=:; _lra_add=""
  for _lra_d in $LRA_SHELL_PATH_PREPEND; do
    case ":${PATH:-}:" in *":$_lra_d:"*) ;; *) _lra_add="$_lra_add${_lra_add:+:}$_lra_d" ;; esac
  done
  IFS=$_lra_ifs
  if [ -n "$_lra_add" ]; then PATH="$_lra_add${PATH:+:$PATH}"; export PATH; fi
  unset _lra_ifs _lra_add _lra_d
fi
