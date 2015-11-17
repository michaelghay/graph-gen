import math
import networkx
import random

random.seed(0)

class GeneralizedGraph(object):
	"Represents a generalized graph described in Hay et al. VLDB 2008"
	def __init__(self, g, partition, alg, k, enforce_min=False):
		# self.g = g
		# self.partition = partition
		self.name = g.name
		self.alg = alg
		self.k = k
		self.min_degree = False
		
		gen_g = networkx.MultiGraph()
		for (u,v) in g.edges():
			u_gid = partition.get_group(u)
			v_gid = partition.get_group(v)
			gen_g.add_edge(u_gid, v_gid)
		
		self.gen_g = gen_g
		self.partition = partition
		if enforce_min:
			assert partition.get_min_group_size() >= self.k, "min size=%d k=%d" % (partition.get_min_group_size(), self.k)
	
	def get_alg(self):
		return self.alg

	def get_k(self):
		return self.k
	
	def get_name(self):
		return self.name
	
	def neighbors(self, u):
		nbrs = set(self.gen_g.neighbors(u))
		nbrs.difference_update([u])
		assert u not in nbrs
		return nbrs
		
	def num_edges(self, u, v):
		return self.gen_g.number_of_edges(u, v)
		
	def supernode_iter(self):
		return self.partition.keys().__iter__()

	def size(self, u):
		return self.partition.get_size(u)
		
	def sample_graph(self, seed=None):
		if seed != None:
			random.seed(seed)
		tmp_gen_g = self.gen_g.copy()
		g = networkx.Graph()
		g.add_nodes_from(self.partition.nodes())
		
		for (gid1, gid2) in tmp_gen_g.edges():
			group1 = self.partition.get_members(gid1)
			group2 = self.partition.get_members(gid2)
			random.shuffle(group1)
			random.shuffle(group2)
			
			found = False
			for i in range(len(group1)):
				u = group1[i]
				for j in range(len(group2)):
					v = group2[j]
					if u != v and not g.has_edge(u,v):
						g.add_edge(u,v)
						assert g.has_edge(u,v)
						found = True
						break
				if found:
					break
			assert found

		if self.min_degree:
			for u in g.nodes():
				if g.degree(u) == 0:
					nodes = self.partition.get_members(self.partition.get_group(u))
					for v in nodes:
						if g.degree(v) > 1:
							nbr = random.choice(g.neighbors(v))
							g.delete_edge(v, nbr)
							g.add_edge(u, nbr)
							break
				assert g.degree(u) > 0
			assert min(g.degree()) > 0
		# print "Created graph with %d nodes and %d edges" % (g.number_of_nodes(), g.number_of_edges())			
		return g
	
	# def num_worlds(self):
	# 	num_worlds = 0
	# 	super_nodes = self.partition.keys()
	# 	for i in range(len(super_nodes)):
	# 		u = super_nodes[i]
	# 		n = self.partition.get_size(u)
	# 		e = self.gen_g.number_of_edges(u, u)
	# 		num_worlds += utils.lnchoose(n*(n-1)/2, e)
	# 		
	# 		for j in range(i+1, len(super_nodes)):
	# 			v = super_nodes[j]
	# 			m = self.partition.get_size(v)
	# 			e = self.gen_g.number_of_edges(u, v)
	# 			num_worlds += utils.lnchoose(m*n, e)
	# 	return num_worlds
