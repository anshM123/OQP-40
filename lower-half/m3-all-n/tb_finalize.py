"""Insert the Theorem B section (with the current table of tb_table.md) into RESULTS.md and update Section 0."""
import subprocess, sys
sys.path.insert(0, '.')
exec(open('tb_table.py').read())
sec = open(sys.argv[1]).read()
table = open('tb_table.md').read().strip()
sec = sec.replace('TB_TABLE_PLACEHOLDER', table)
res = open('RESULTS.md').read()
marker = '\n## 8. Theorem B'
if marker in res:
    res = res[:res.index(marker)]
res = res.rstrip('\n') + '\n' + sec
open('RESULTS.md', 'w').write(res)
print('RESULTS.md updated')
