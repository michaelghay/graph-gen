# ----------------------------------------------------------------------------
# Some helper functions
# ----------------------------------------------------------------------------

def get_max(items):
	"Returns index of first max value"
	max = None
	argmax = None
	for i in range(len(items)):
		if items[i] > max:
			argmax = i
			max = items[i]
	assert argmax != None
	return argmax

def normalize(unnormalized):
	if type(unnormalized) == dict:
		for val in unnormalized.values():
			assert val >= 0
		total = sum(unnormalized.values())
		normalized = dict([ (val, float(score)/total) for (val, score) in unnormalized.iteritems() ])
		return normalized
	assert type(unnormalized) == list
	for val in unnormalized:
		assert val >= 0
	total = sum(unnormalized)
	normalized = [ float(score)/total for score in unnormalized ]
	return normalized

def sample(probs):
	x = random.random()
	cdf = 0
	for i in range(len(probs)):
		if cdf < x and (cdf + probs[i]) >= x:
			return i
		cdf += probs[i]
	assert False, "Failed to sample!"

def structural_equivalence(g):
	sig_to_nodes = {}
	for u in g:
		nbrs = g.neighbors(u)
		nbrs.sort()
		sig = str(nbrs)
		sig_to_nodes[sig] = sig_to_nodes.get(sig, []) + [u]
	return sig_to_nodes.values()

