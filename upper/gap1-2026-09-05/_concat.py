import io
base = open('H05G_Assembly.lean', encoding='utf-8').read()
app = open('_append_h05.lean', encoding='utf-8').read()
open('H05G_Assembly.lean', 'w', encoding='utf-8').write(base + app)
print(len(base + app))
