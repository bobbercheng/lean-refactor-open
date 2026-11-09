RID=p85b-t06-k1
for d in /proc/[0-9]*; do
  c=$(tr '\0' ' ' < $d/cmdline 2>/dev/null) || continue
  case "$c" in *harness/agent.py*"$RID"*) p=${d#/proc/}; pg=$(ps -o pgid= -p $p | tr -d ' '); echo "match pid $p pgid $pg: ${c:0:120}";;
  esac
done | sort -u > /tmp/stop_t05.match; cat /tmp/stop_t05.match
n=$(wc -l < /tmp/stop_t05.match); [ "$n" -ge 1 ] || { echo "no match"; exit 0; }
pg=$(awk '{print $5}' /tmp/stop_t05.match | sort -u | tr -d ':' ); echo "pgids: $pg"
for g in $pg; do [ "$g" -gt 1 ] && kill -TERM -- -$g && echo "TERM sent to pgid $g"; done
sleep 20; for g in $pg; do ps -o pid= -g $g | head -3; done; echo done
