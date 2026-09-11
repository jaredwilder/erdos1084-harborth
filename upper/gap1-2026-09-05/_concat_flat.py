src = open('H3G_Frontier.lean', encoding='utf-8').read()
marker = "/-! ## THE MODEL -- the frontier hypotheses are NOT vacuous."
base = src.split(marker)[0]
app = open('_append_flat.lean', encoding='utf-8').read()
open('H3G_FlatModel.lean', 'w', encoding='utf-8').write(base + app)
print(len(base + app))
