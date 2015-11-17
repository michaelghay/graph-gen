# ----------------------------------------------------------------------------
# This is an implementation of some Partitioner classes.  There is a basic
# Partitioner which just divides nodes randomly into groups of size k.  Then 
# there is a partitioner based on the algorithm described in 
#
# 	Resisting structural re-identification in anonymized social networks
# 	Michael Hay, Gerome Miklau, David Jensen, Don Towsley, and Philipp Weis
# 	Proceedings of the VLDB, 2008
#
# That algorithm uses local search to find a good partition.  The search is 
# implemented in search.py and the code below implements the search state 
# space and associated details (methods for evaluating current search state
# and proposing new states).
# ----------------------------------------------------------------------------

import math
import networkx
import random

import partition
import search
import utils_lite as utils

class Partitioner(object):

	def __init__(self, g, k):
		self.g = g
		self.k = k
		self.partitioner_type = 'r'
	
	def name(self):
		return self.g.name + "." + str(self.k) + "." + self.partitioner_type + ".partition"
		
	def partition(self):
		nodes = self.g.nodes()
		random.shuffle(nodes)
		part = []
		while len(nodes) >= 2*self.k:
			part.append( nodes[:self.k] )
			del nodes[:self.k]
		part.append(nodes)
		self.partition = partition.Partition(part)
		return self.partition
	
	def save(self, directory):
		self.partition.save(directory + self.name())


class MinNumWorldsPartitioner(Partitioner):

	def __init__(self, g, k, working_dir, max_steps=None):
		Partitioner.__init__(self, g, k)
		self.working_dir = working_dir
		self.max_steps = max_steps

	def name(self):
		return self.g.name + "." + str(self.k) + "." + 'p' + ".partition"

	def partition(self):
		problem = Problem(self.g, self.k, max_steps=self.max_steps)
		state = search.annealing(problem, working_dir=self.working_dir)
		final_partition = []
		for gid in state.get_partitions():
			final_partition.append(state.get_nodes(gid))
		p = partition.Partition(groups=final_partition)
		self.partition = p
		return p



debug_sampling = False
debug = False
debug_edge_count = debug
doing_flips = True
two_hop_only = True
doing_mergesplits = True
random_split = False  # it really slows down runtime
random_splitmerge = True  # it really slows down runtime
init_struct_equivalence = True

class StateChange(object):
	def __init__(self):
		self.score_change = 0
	def get_score_change(self):
		return self.score_change
	def set_score_change(self, score):
		self.score_change = score

class Merge(StateChange):
	def __init__(self, i, j):
		StateChange.__init__(self)
		self.i = i
		self.j = j

class MergeSplit(StateChange):
	def __init__(self, i, j, g1, g2):
		StateChange.__init__(self)
		self.i = i
		self.j = j
		self.g1 = g1
		self.g2 = g2		

class Split(StateChange):
	def __init__(self, partition_idx, sub_partition_1, sub_partition_2):
		StateChange.__init__(self)
		self.partition_idx = partition_idx
		self.sub_partition_1 = sub_partition_1
		self.sub_partition_2 = sub_partition_2		

class Flip(StateChange):
	def __init__(self, node, i, j):
		StateChange.__init__(self)
		self.node = node
		self.i = i
		self.j = j

class NoOp(StateChange):
	def __init__(self):
		StateChange.__init__(self)

class State(object):
	# state consists:
	#   - G, input graph
	#   - a mapping of partition key to set of nodes in partition
	#	- a mapping from node to partition
	#   - a partition graph where edge between i,j reveals number 
	#     of edges in G between nodes in i to nodes in j

	def __init__(self, g, partition=None, min_size=None):
		self.g = g
		if partition != None:
			self.partition = {}
			self.nodes = {}
			self.next_key = 0
			for group in partition:
				self.partition[self.next_key] = group[:]
				for member in group:
					self.nodes[member] = self.next_key
				self.next_key += 1
		elif not init_struct_equivalence:	
			self.partition = { 0: g.nodes() }
			self.nodes = {}
			for node in g.nodes():
				self.nodes[node] = 0
			self.next_key = 1
		else:
			assert min_size != None and type(min_size) == int
			eq_classes = utils.structural_equivalence(self.g)
			eq_classes = [ (len(i), i) for i in eq_classes ]
			eq_classes.sort()
			eq_classes.reverse()

			self.partition = {}
			self.nodes = {}
			curr_key = 0
			self.partition[curr_key] = []
			remaining_nodes = g.number_of_nodes()

			for (length, eq_class) in eq_classes:
				# only create a new partition if:
				# - current partition is big enough
				# - current structural eq. class is larger than one
				# - you have enough nodes to fill another partition
				if len(self.partition[curr_key]) >= min_size and length > 1 and remaining_nodes >= min_size:
					curr_key += 1
					self.partition[curr_key] = []

				self.partition[curr_key] += eq_class[:]
				for u in eq_class:
					self.nodes[u] = curr_key
			self.next_key = curr_key + 1
			assert min(map(len, self.partition.values())) >= min_size

		self.free_keys = []
		self.likelihood_cache = {}

	def __add_edge(self, i, j, count):
		if count > 0:
			self.partition_graph.add_edge(i,j,key=0,count=count)
		elif self.partition_graph.has_edge(i,j):
			self.partition_graph.remove_edge(i,j)
			assert not self.partition_graph.has_edge(i,j)

	def __add_node(self, i):
		self.partition_graph.add_node(i)

	def __remove_edges(self, i):
		self.partition_graph.remove_edges_from(self.partition_graph.edges(i))

	def __delete_node(self, i):
		self.partition_graph.delete_node(i)

	def __get_edge(self, i, j):
		count = self.partition_graph.get_edge_data(i,j,key=0)["count"]
		assert count > 0
		return count

	def __has_edge(self, i, j):
		has_edge = self.partition_graph.has_edge(i,j)
		if has_edge:
			assert self.partition_graph.get_edge_data(i,j,key=0)["count"] > 0
		return has_edge

	def __make_partition(self, nodes):
		if self.free_keys:
			key = self.free_keys.pop()
		else:
			key = self.next_key
			self.next_key += 1
		self.partition[key] = nodes[:]
		return key

	def apply_change(self, state_change):
		if isinstance(state_change, Split):
			idx = state_change.partition_idx
			part = self.partition[idx]
			self.partition[idx] = state_change.sub_partition_1
			new_idx = self.__make_partition(state_change.sub_partition_2)

			for node in state_change.sub_partition_2:
				self.nodes[node] = new_idx

			nbrs = self.neighbors(idx)
			self.__remove_edges(idx)
			self.__add_node(new_idx)

			# update likelihood cache
			for nbr in nbrs + [idx]:
				if nbr in self.likelihood_cache:
					del self.likelihood_cache[nbr]

			edge_count = self.edge_count(state_change.sub_partition_1, state_change.sub_partition_2)
			if edge_count > 0:
				self.__add_edge(idx, new_idx, edge_count)

			for (idx, group) in [ (idx, state_change.sub_partition_1), \
			(new_idx, state_change.sub_partition_2)]:
				edge_count = self.edge_count(group)
				self.__add_edge(idx, idx, edge_count)
				for j in nbrs:
					edge_count = self.edge_count(group, self.get_nodes(j))
					self.__add_edge(idx, j, edge_count)

		elif isinstance(state_change, Merge):
			i = state_change.i
			j = state_change.j

			# compute ll of new partition of ij merged
			edges_ii = self.edge_count(i)
			edges_jj = self.edge_count(j)
			edges_ij = self.edge_count(i,j)

			edges_ii = edges_ii + edges_jj + edges_ij
			self.__add_edge(i, i, edges_ii)

			# compute ll of new partition with all neighbors of i and j
			nbrs = self.neighbors([i,j])
			for k in nbrs:
				edges_ik = self.edge_count(i,k) + self.edge_count(j,k)
				self.__add_edge(i, k, edges_ik)

			# update likelihood cache
			for nbr in nbrs.union([i,j]):
				if nbr in self.likelihood_cache:
					del self.likelihood_cache[nbr]

			self.partition[i] = self.partition[i] + self.partition[j]
			self.__delete_node(j)
			for node in self.partition[j]:
				self.nodes[node] = i
			del self.partition[j]
			self.free_keys.append(j)

		elif isinstance(state_change, MergeSplit):
			i = state_change.i
			j = state_change.j
			g1 = state_change.g1
			g2 = state_change.g2

			nbrs = self.neighbors([i,j])

			# update likelihood cache
			for nbr in nbrs.union([i,j]):
				if nbr in self.likelihood_cache:
					del self.likelihood_cache[nbr]

			edge_count = self.edge_count(g1, g2)
			self.__add_edge(i, j, edge_count)

			for (idx, grp) in [ (i, g1), (j, g2) ]:
				self.__add_edge(idx, idx, self.edge_count(grp))
				for k in nbrs:
					edge_count = self.edge_count(grp, self.get_nodes(k))
					self.__add_edge(idx, k, edge_count)

			self.partition[i] = g1
			self.partition[j] = g2
			for node in g1:   
				self.nodes[node] = i
			for node in g2:
				self.nodes[node] = j

		elif isinstance(state_change, Flip):
			u = state_change.node
			i = state_change.i
			j = state_change.j
			assert self.nodes[u] == i and u in self.partition[i], "Flipped node not in partition"

			edges_ii = self.edge_count(i)
			edges_jj = self.edge_count(j)
			edges_ij = self.edge_count(i,j)

			edges_ui = self.edge_count([u], self.get_nodes(i))
			edges_uj = self.edge_count([u], self.get_nodes(j))

			self.__add_edge(i, i, edges_ii - edges_ui)
			self.__add_edge(j, j, edges_jj + edges_uj)
			self.__add_edge(i, j, edges_ij + edges_ui - edges_uj)

			nbrs = self.neighbors(i)
			for k in nbrs:

				if k == j:
					continue  # handled above

				nodes_k = self.get_nodes(k)
				edges_uk = self.edge_count([u], nodes_k)

				edges_ik = self.edge_count(i,k) - edges_uk
				self.__add_edge(i, k, edges_ik)

				edges_jk = self.edge_count(j,k) + edges_uk
				self.__add_edge(j, k, edges_jk)

			for nbr in self.neighbors([i,j]).union([i,j]):
				if nbr in self.likelihood_cache:
					del self.likelihood_cache[nbr]

			self.partition[i].remove(u)
			self.partition[j].append(u)
			self.nodes[u] = j
		elif not isinstance(state_change, NoOp):
			assert False, "Unrecognized change %s" % (state_change.__class__)

	# SANITY CHECKS OF STATE:
	# - state data structure represents a valid state:
	#	- 1. every node in G has been assigned to exactly one partition
	#	- 2. each partition has at least k nodes 
	#	- 3. the nodes in each partition appear in G
	#	- 4. the partition graph matches the partitions (nodes of V equals the set of partitions)
	#	- 5. the partition graph matches input graph G:
	#		- edge count between partitions i and j == no. of edges in G between nodes of i and nodes of j
	#	- 6. the score of the state matches likelihood when computed from scratch
	# 	- cached edge counts are accurate
	def check_state(self, min_size=None):

		# check nodes of G are all in partition assignment
		V = set(self.g.nodes())
		nodes = set(self.nodes.keys())
		assert V == nodes

		# check each nodes's partition contains the node
		assigned_partitions = set([])
		for u in V:
			i = self.nodes[u]
			assert u in set(self.partition[i])
			assigned_partitions.add(i)

		assert assigned_partitions == set(self.partition.keys())

		# check that the set of nodes in partitioning is exactly V
		tmp = reduce(lambda x,y: x+y, self.partition.values())
		nodes = set(tmp)
		assert len(tmp) == len(nodes)
		assert V == nodes

		# check min size of partitions
		partition_sizes = map(len, self.partition.values())
		if min_size != None:
			assert min(partition_sizes) >= min_size
		assert sum(partition_sizes) == len(V)

		assert set(self.partition_graph.nodes()) == set(self.partition.keys())

		for i in self.partition_graph:
			for j in self.partition_graph:

				if i < j:
					continue

				if i == j:
					nodes_i = set(self.partition[i])
					neighbors = []
					for u in nodes_i:
						neighbors += self.g.neighbors(u)
					count = 0
					for nbr in neighbors:
						count += nbr in nodes_i
					count /= 2  # each edge is double counted
				else: 
					nodes_i = self.partition[i]
					nodes_j = self.partition[j]
					count = len(networkx.edge_boundary(self.g, nodes_i, nodes_j))

				if self.partition_graph.has_edge(i,j):
					stored_count = self.partition_graph.get_edge_data(i,j,key=0)["count"]
					assert count == stored_count, \
					"Mismatch: edges(%d,%d)=%d stored count=%d" % (i,j,count, stored_count)
				else:
					assert count == 0, \
					"Mismatch: edges(%d,%d)=%d but no count stored" % (i,j, count)


	def choose_random_node(self):
		return random.choice(self.nodes.keys())

	def copy(self):
		return State(self.g, partition=self.partition.values())

	def edge_count(self, i, j=None):
		self_loop = False
		assert i != j, "Should not be equal"
		if j == None:
			self_loop = True
			j = i

		if type(i) == type(0):
			num_edges = 0
			if self.__has_edge(i,j):
				num_edges = self.__get_edge(i,j)
			if debug_edge_count:
				if self_loop:
					num_edges_check = self.edge_count(self.get_nodes(i))
				else:
					num_edges_check = self.edge_count(self.get_nodes(i), self.get_nodes(j))
				assert num_edges == num_edges_check, "Count mismatch (" + str(i) + "," + str(j) + "): returns " + \
				str(num_edges) + " but is " + str(num_edges_check)
			return num_edges

		# otherwise, compute number between groups i and j
		if len(i) == 0 or len(j) == 0:
			return 0

		if len(i) > len(j):
			tmp = i
			i = j
			j = tmp

		# SORTING SEEMS TO BE SLOWER
		# neighbors = reduce(lambda x,y: x + y, map(self.adj_list.get, i))
		# neighbors.sort()
		# j.sort()
		# count = 0
		# n_idx = 0
		# n = len(neighbors)
		# for u in j:
		# 	while n_idx < n and neighbors[n_idx] < u:
		# 		n_idx += 1
		# 	while n_idx < n and neighbors[n_idx] == u:
		# 		n_idx += 1
		# 		count += 1
		# edge_count = count

		j = set(j)
		neighbors = reduce(lambda x,y: x + y, map(self.adj_list.get, i))
		edge_count = reduce(lambda total, nbr: total + (nbr in j), neighbors, 0)

		if self_loop:
			edge_count = edge_count / 2 # every edge is double counted
		assert edge_count >= 0
		return edge_count

	def get_likelihood_partition(self, i):
		return self.likelihood_cache[i]

	def get_partition_of_node(self, u):
		return self.nodes[u]

	def get_partitions(self):
		return self.partition.keys()

	def get_partition_map(self):
		self.initialize()
		nodes_to_group = {}
		for gid in self.partition:
			for node in self.partition[gid]:
				nodes_to_group[node] = gid
		return nodes_to_group

	def get_nodes(self, i):
		return self.partition[i]

	def has_likelihood_partition(self, i):
		return i in self.likelihood_cache

	def initialize(self):
		self.adj_list = {}
		for u in self.g:
			self.adj_list[u] = self.g.neighbors(u)[:]

		self.partition_graph = networkx.MultiGraph()
		# for i in self.partition:
		# 	self.__add_node(i)
		# 	for j in self.partition:
		# 		if i < j:
		# 			continue
		# 		elif i == j:
		# 			edge_count = self.edge_count(self.partition[i])
		# 		else:
		# 			edge_count = self.edge_count(self.partition[i], self.partition[j])
		# 		self.__add_edge(i,j,edge_count)

		# a faster way, initialize by iterating over edges of G
		for i in self.partition:
			self.__add_node(i)
		for (u,v) in self.g.edges():
			i = self.nodes[u]
			j = self.nodes[v]
			if self.partition_graph.has_edge(i,j):
				count = self.partition_graph.get_edge_data(i,j,key=0)["count"] + 1
			else:
				count = 1
			self.partition_graph.add_edge(i,j,key=0,count=count)

		if debug:
			self.check_state()

	def neighbors(self, i):
		if type(i) == type([]):
			nbrs = []
			for idx in i:
				nbrs += self.partition_graph.neighbors(idx)
			nbrs = set(nbrs)
			nbrs.difference_update(i)
			return nbrs
		else:
			assert type(i) == type(0) or type(i) == type('s')
			nbrs = self.partition_graph.neighbors(i)
			if i in nbrs:
				nbrs.remove(i)
			return nbrs

	def neighbors_two_hop(self, i):
		"Returns neighbors and neighbors' neighbors excluding i"
		nbrs = []
		for nbr in self.partition_graph.neighbors(i):
			nbrs.append(nbr)
		nbrs2 = []
		for nbr in nbrs:
			nbrs2 += self.partition_graph.neighbors(nbr)
		nbrs = set(nbrs + nbrs2)
		nbrs.discard(i)
		return nbrs

	def node_count(self, i):
		return len(self.get_nodes(i))	

	def num_partitions(self):
		return len(self.partition)

	def set_likelihood_partition(self, i, l):
 		self.likelihood_cache[i] = l


class Problem(object):

	def __init__(self, g, k=None, max_steps=None, start_state=None):
		self.n = g.number_of_nodes()

		# parameters
		self.k = k
		self.max_steps = 200 * max(self.n, 100)
		self.start_temp = 1000
		self.alpha = math.exp( 1./(self.max_steps) * math.log(.0001/self.start_temp ))
		if max_steps != None:
			self.max_steps = max_steps
		self.cycle_length = 5 * self.n
		self.min_changes_per_cycle = int(round(.10 * self.n))  # 10% of nodes must flip per cycle
		self.split_frequency = 100
		self.num_changes = 0
		self.score = None
		if start_state == None:
			self.__start_state(g)
		else:
			self.state = start_state
			self.state.initialize()


		# logging
		self.num_noops = 0
		self.num_splits = 0
		self.num_merges = 0
		self.num_mergesplits = 0
		self.num_flips = 0
		self.cache_hit = 0
		self.cache_tries = 0
		self.nbr_merge = 0
		self.nbr_nbr_merge = 0
		self.nonnbr_merge = 0

	def __likelihood(self):
		ll = 0
		for i in self.state.get_partitions():
			edges_ii = self.state.edge_count(i)
			nodes_i = self.state.node_count(i)
			ll += self.__likelihood_partition_pair(edges_ii, nodes_i)

			for j in self.state.get_partitions():
				if i <= j:
					continue
				edges_ij = self.state.edge_count(i,j)
				nodes_j = self.state.node_count(j)
				ll += self.__likelihood_partition_pair(edges_ij, nodes_i, nodes_j)

		return ll

	def __likelihood_flip(self, u, i, j):
		ll = 0

		edges_ii = self.state.edge_count(i)
		edges_jj = self.state.edge_count(j)
		edges_ij = self.state.edge_count(i,j)
		nodes_i = self.state.node_count(i)
		nodes_j = self.state.node_count(j)

		edges_ui = self.state.edge_count([u], self.state.get_nodes(i))
		edges_uj = self.state.edge_count([u], self.state.get_nodes(j))

		ll += self.__likelihood_partition_pair(edges_ii - edges_ui, nodes_i - 1)
		ll += self.__likelihood_partition_pair(edges_jj + edges_uj, nodes_j + 1)
		ll += self.__likelihood_partition_pair(edges_ij - edges_uj + edges_ui, nodes_i - 1, nodes_j + 1)

		# recompute ll of partition i and j with all neighbors of i and j
		for k in self.state.neighbors([i,j]):
			nodes_k = self.state.get_nodes(k)
			edges_uk = self.state.edge_count([u],nodes_k)

			edges_ik = self.state.edge_count(i,k)
			ll += self.__likelihood_partition_pair(edges_ik - edges_uk, nodes_i - 1, len(nodes_k))

			edges_jk = self.state.edge_count(j,k)
			ll += self.__likelihood_partition_pair(edges_jk + edges_uk, nodes_j + 1, len(nodes_k))
		return ll

	def __likelihood_merge(self, i, j):
		ll = 0

		# compute ll of new partition of ij merged
		edges_ii = self.state.edge_count(i)
		edges_jj = self.state.edge_count(j)
		edges_ij = self.state.edge_count(i,j)
		edges = edges_ii + edges_jj + edges_ij
		nodes = self.state.node_count(i) + self.state.node_count(j)
		ll += self.__likelihood_partition_pair(edges, nodes)

		# compute ll of new partition with all neighbors of i and j
		for k in self.state.neighbors([i,j]):
			edges = self.state.edge_count(i,k) + self.state.edge_count(j,k)
			nodes_k = self.state.node_count(k)
			ll += self.__likelihood_partition_pair(edges, nodes, nodes_k)

		return ll

	def __likelihood_merge_and_split(self, i, j, g1, g2):
		ll_change = 0

		# compute likelihood of edges in g1, edges in g2 and edges between g1 and g2
		edges_11 = self.state.edge_count(g1)
		edges_12 = self.state.edge_count(g1, g2)
		edges_22 = self.state.edge_count(g2)


		ll_change += self.__likelihood_partition_pair(edges_11, len(g1))
		ll_change += self.__likelihood_partition_pair(edges_12, len(g1), len(g2))
		ll_change += self.__likelihood_partition_pair(edges_22, len(g2))

		# compute likelihood with neighbors of i and j
		nbrs = self.state.neighbors([i,j])
		for sub_partition in [g1, g2]:
			for k in nbrs:
				nodes_k = self.state.get_nodes(k)
				edges_sk = self.state.edge_count(sub_partition, nodes_k)
				ll_change += self.__likelihood_partition_pair(edges_sk, len(sub_partition), len(nodes_k))	
		return ll_change


	def __likelihood_partition(self, i):
		self.cache_tries += 1

		if self.state.has_likelihood_partition(i):
			self.cache_hit += 1
			return self.state.get_likelihood_partition(i)


		ll = 0
		nodes_i = self.state.node_count(i)
		edges_ii = self.state.edge_count(i)
		ll += self.__likelihood_partition_pair(edges_ii, nodes_i)

		for j in self.state.neighbors(i):
			edges_ij = self.state.edge_count(i,j)
			nodes_j = self.state.node_count(j)
			ll += self.__likelihood_partition_pair(edges_ij, nodes_i, nodes_j)

		self.state.set_likelihood_partition(i, ll)
		return ll

	def __likelihood_partition_pair(self, edge_count, n, m=None):
		if m == None:
			num_slots = n * (n-1) / 2
		else:
			num_slots = n * m
		if edge_count == 0 or edge_count == num_slots:
			return 0
		assert edge_count < num_slots and edge_count > 0, "edge count=%d slots=%d" % (edge_count, num_slots)
		p = 1. * edge_count / num_slots
		l = num_slots * (p * math.log(p) + (1-p) * math.log(1-p))
		assert str(l) != 'nan'
		return l

	def __likelihood_split(self, split_idx, part1, part2):
		ll_change = 0
		# compute score between subpartitions
		edges_12 = self.state.edge_count(part1, part2)
		ll_change += self.__likelihood_partition_pair(edges_12, len(part1), len(part2))
		assert str(ll_change) != "nan"

		# for each subpartition, compute its score and its score to the other partitions
		for sub_partition in [part1, part2]:
			edges_ii = self.state.edge_count(sub_partition)
			ll_change += self.__likelihood_partition_pair(edges_ii, len(sub_partition))
			assert str(ll_change) != "nan"
			for i in self.state.neighbors(split_idx):
				nodes_i = self.state.get_nodes(i)
				edges_ij = self.state.edge_count(sub_partition, nodes_i)
				ll_change += self.__likelihood_partition_pair(edges_ij, len(sub_partition), len(nodes_i))	
				assert str(ll_change) != "nan"
		return ll_change

	def __start_state(self, graph):
		self.state = State(graph, min_size=self.k)
		self.state.initialize()
		self.score = self.__likelihood()

	def apply_noop_change(self):
		self.apply_change(NoOp())

	def apply_change(self, state_change):
		if isinstance(state_change, Merge):
			i = state_change.i
			j = state_change.j
			nbrs = self.state.neighbors(j)
			if i in nbrs:
				self.nbr_merge += 1
			else:
				# is i a neighbor of j's neighbor?
				found = False
				for nbr in nbrs:
					if i in self.state.neighbors(nbr):
						found = True
						break
				if found:
					self.nbr_nbr_merge += 1
				else:
					self.nonnbr_merge += 1

		self.state.apply_change(state_change)
		if isinstance(state_change, NoOp):
			self.num_noops += 1
		else:
			self.num_changes += 1
			if isinstance(state_change, Split):
				self.num_splits += 1
			elif isinstance(state_change, Merge):
				self.num_merges += 1
			elif isinstance(state_change, MergeSplit):
				self.num_mergesplits += 1
			elif isinstance(state_change, Flip):
				self.num_flips += 1
			else:
				assert False, "Unrecognized change"
		self.score += state_change.get_score_change()

	def __check_likelihood(self):

		# check score matches actual likelihood
		temp_problem = Problem(self.state.g, self.k)
		temp_problem.set_state(self.state.copy())
		temp_score = temp_problem.get_score()
		assert abs(self.score - temp_score) < 0.0000000001, \
		"Actual score (%g) does not match reported score (%g)" % (temp_score, self.score)

		# check values in cache
		for i in self.state.get_partitions():
			if self.state.has_likelihood_partition(i):
				cached_ll = self.state.get_likelihood_partition(i)
				# must get appropriate partition in temp problem
				u = self.state.get_nodes(i)[0]
				ll = temp_problem.__likelihood_partition(temp_problem.state.get_partition_of_node(u))
				assert abs(cached_ll - ll) < 0.0000000001, \
				"Invalid likelihood cache for partition i=%d: %g vs. cached %g" % (i, ll, cached_ll)

	def copy_state(self):
		"Copy state used for saving the max state"
		return self.state.copy()

	def get_current_state(self):
		return self.state

	def get_score(self):
		if self.score == None:
			self.score = self.__likelihood()
		return self.score

	def merge_partition(self, i):
		successors = []
		if two_hop_only:
			candidate_partitions = self.state.neighbors_two_hop(i)
		else:
			candidate_partitions = self.state.get_partitions()
		for j in candidate_partitions:
			if i == j:
				continue
			successors.append(Merge(i,j))
		return successors

	def merge_and_split_partition(self, i):

		# first find best merge
		successors = []
		if two_hop_only:
			candidate_partitions = self.state.neighbors_two_hop(i)
		else:
			candidate_partitions = self.state.get_partitions()

		if len(candidate_partitions) == 0:
			return []

		for j in candidate_partitions:
			if i == j:
				continue
			successors.append(Merge(i,j))

		scores = []
		for merge in successors:
			score = self.score_change(merge)
			assert score != None and str(score) != 'nan'
			scores.append(score)
		merge_op = successors[utils.get_max(scores)]
		j = merge_op.j

		# then find best split of a merged i,j
		nodes = self.state.get_nodes(i)[:] + self.state.get_nodes(j)[:]

		g1 = nodes
		g2 = []
		g1_edges = {}
		g2_edges = {}
		edges_11 = self.state.edge_count(i) + self.state.edge_count(j) + self.state.edge_count(i,j)
		edges_12 = 0
		edges_22 = 0

		nbrs = self.state.neighbors([i,j])
		for k in nbrs:
			g1_edges[k] = self.state.edge_count(i, k) + self.state.edge_count(j, k)
			g2_edges[k] = 0

		while len(g2) < self.k:

			# find best node from g1 to move to g2
			max = None
			argmax = None

			if random_splitmerge and len(g2) == 0:
				argmax = random.choice(g1)
			else:
				for node in g1:
					ll = 0

					# compute change in score between g1 and g2 if we move node to g2
					edges_node_1 = self.state.edge_count([node], g1)
					edges_node_2 = self.state.edge_count([node], g2)
					tmp_edges_11 = edges_11 - edges_node_1 
					tmp_edges_12 = edges_12 - edges_node_2 + edges_node_1
					tmp_edges_22 = edges_22 + edges_node_2

					ll += self.__likelihood_partition_pair(tmp_edges_12, len(g1)-1, len(g2)+1)
					ll += self.__likelihood_partition_pair(tmp_edges_11, len(g1)-1)
					ll += self.__likelihood_partition_pair(tmp_edges_22, len(g2)+1)

					# compute change in edge counts and score if we move node to g2
					for k in nbrs:
						nodes_k = self.state.node_count(k)

						# compute change in edges
						edges_node_k = self.state.edge_count([node], self.state.get_nodes(k))
						edges_1k = g1_edges[k] - edges_node_k
						edges_2k = g2_edges[k] + edges_node_k

						ll += self.__likelihood_partition_pair(edges_1k, len(g1)-1, nodes_k)
						ll += self.__likelihood_partition_pair(edges_2k, len(g2)+1, nodes_k)

					if ll > max:
						max = ll
						argmax = node

			assert argmax != None
			edges_node_1 = self.state.edge_count([argmax], g1)
			edges_node_2 = self.state.edge_count([argmax], g2)
			edges_11 = edges_11 - edges_node_1 
			edges_12 = edges_12 - edges_node_2 + edges_node_1
			edges_22 = edges_22 + edges_node_2
			assert edges_12 >= 0 and edges_11 >= 0 and edges_22 >= 0

			for k in nbrs:
				edges_node_k = self.state.edge_count([argmax], self.state.get_nodes(k))
				g1_edges[k] = g1_edges[k] - edges_node_k
				g2_edges[k] = g2_edges[k] + edges_node_k
				assert g1_edges[k] >= 0 and g2_edges[k] >= 0 
			g1.remove(argmax)
			g2.append(argmax)

		s_g1 = set(g1)
		s_g2 = set(g2)
		s_i = set(self.state.get_nodes(i))
		s_j = set(self.state.get_nodes(j))

		if s_g1 == s_i:
			assert s_g2 == s_j
			return [ ]
		elif s_g1 == s_j:
			assert s_g2 == s_i
			return [ ]
		else:
			return [ MergeSplit(i, j, g1, g2) ]


	def get_stats(self):
		#s = "noops=%d splits=%d merges=%d cache=%g" % (self.num_noops, self.num_splits, self.num_merges, 1.*self.cache_hit/self.cache_tries)
		if self.cache_tries == 0:
			cache_rate = 0
		else:
			cache_rate = 1.*self.cache_hit/self.cache_tries
		t = (self.num_noops, self.num_splits, self.num_merges, self.num_mergesplits, self.num_flips, cache_rate)
		self.num_noops = self.num_splits = self.num_merges = self.num_mergesplits = self.num_flips = self.cache_hit = self.cache_tries = 0
		return t

	def sample_graph(self, enforce_min_degree=False, enforce_connected_comps=False):
		g2 = networkx.Graph()

		for i in self.state.partition.keys():
			edges_within = self.state.edge_count(i)
			nodes_i = self.state.get_nodes(i)
			g2.add_nodes_from(nodes_i)
			assert edges_within <= len(nodes_i) * (len(nodes_i)-1)/2 and edges_within >= 0
			while edges_within > 0:
				u = random.choice(nodes_i)
				v = random.choice(nodes_i)
				if u == v or g2.has_edge(u,v):
					continue
				else:
					g2.add_edge(u,v)
					edges_within -= 1

			for j in self.state.neighbors(i):
				if i <= j:
					continue
				edges_between = self.state.edge_count(i,j)
				nodes_j = self.state.get_nodes(j)
				assert edges_between <= len(nodes_i) * len(nodes_j) and edges_between >= 0
				while edges_between > 0:
					u = random.choice(nodes_i)
					v = random.choice(nodes_j)
					if g2.has_edge(u,v):
						continue
					else:
						g2.add_edge(u,v)
						edges_between -= 1

		if enforce_min_degree:
			self.min_degree(g2)
		if enforce_connected_comps:
			self.conn_comps(g2)

		if debug_sampling:
			#import pdb
			print "Checking sampled graph"
			for i in self.state.partition:
				nodes_i = self.state.get_nodes(i)
				assert self.state.edge_count(i) == len(networkx.subgraph(g2, nodes_i).edges())
				for j in self.state.partition:
					if i <= j:
						continue
					nodes_j = self.state.get_nodes(j)
					assert self.state.edge_count(i,j) == len(networkx.edge_boundary(g2, nodes_i, nodes_j))
		return g2

	def min_degree(self, g2):
		# originally, tried to sample uniformly by edge
		# very slow when partition is large because loop through entire partition
		# just to get a single random edge.
		# now, it just grabs a random node in the partition and moves the edge
		# -----------
		# nodes = g2.nodes()
		# random.shuffle(nodes)
		# for u in nodes:
		# 	if g2.degree(u) == 0:
		# 		i = self.state.get_partition_of_node(u)
		# 		nodes_i = self.state.get_nodes(i)
		# 		# sample by edges
		# 		edges = []
		# 		for v in nodes_i:
		# 			if u != v and g2.degree(v) >= 2:
		# 				edges += [ (v, w) for w in g2.neighbors(v) ]
		# 		(v, w) = random.choice(edges)
		# 		g2.remove_edge(v,w)
		# 		g2.add_edge(u,w)
		# 		assert g2.degree(u) > 0
		nodes = g2.nodes()
		zero_degree_nodes = [ u for u in nodes if g2.degree(u) == 0 ]
		random.shuffle(zero_degree_nodes)

		for u in zero_degree_nodes:
			i = self.state.get_partition_of_node(u)
			nodes_i = self.state.get_nodes(i)
			w = None
			while w == None:
				v = random.choice(nodes_i)
				if u != v and g2.degree(v) >= 2:
					w = random.choice(g2.neighbors(v))
			g2.remove_edge(v,w)
			g2.add_edge(u,w)
			assert g2.degree(u) > 0

	def conn_comps(self, g2):
		# then try to do connectedness
		num_e = len(g2.edges())
		conn_comps = networkx.connected_components(g2)
		conn_trials = 0
		while len(conn_comps) > 1:
			small_comps = conn_comps[1:]
			small_comps.reverse()   # start with smallest components, easiest to fix (?)
			for comp in small_comps:
				edges = []
				for u in comp:
					i = self.state.get_partition_of_node(u)
					nodes_i = self.state.get_nodes(i)
					# sample by edges
					for v in nodes_i:
						if u != v and g2.degree(v) >= 2:
							edges += [ (u, v, w) for w in g2.neighbors(v) \
							if (w != u and not g2.has_edge(u,w)) ]

				if len(edges) == 0:
					continue
				(u, v, w) = random.choice(edges)
				g2.remove_edge(v,w)
				assert u != w
				assert not g2.has_edge(u,w)
				g2.add_edge(u,w)
				assert g2.has_edge(u,w)
				assert num_e == len(g2.edges()), "expected %d vs. actual %d: u=%s v=%s w=%s" % (num_e, len(g2.edges()), str(u), str(v), str(w))
			conn_comps = networkx.connected_components(g2)
			conn_trials += 1
			if conn_trials > 50:
				print "After %d tries, could not connect graph, leaving %d components" % (conn_trials, len(conn_comps))
				break


	# SANITY CHECKS:
	# - state data structure represents a valid state:
	# - likelihood of state is accurate
	# - likelihood cache is accurate 
	#	(for every partition i, if i is in cache, its likelihood matches when computed from scratch)
	def sanity_check(self):
		if debug:
			self.state.check_state(self.k)
			self.__check_likelihood()

	def score_change(self, state_change):
		ll_change = 0
		if isinstance(state_change, Split):
			split_idx = state_change.partition_idx
			part1 = state_change.sub_partition_1
			part2 = state_change.sub_partition_2

			# subtract off contribution of current partition
			ll_change = -self.__likelihood_partition(split_idx)
			ll_change += self.__likelihood_split(split_idx, part1, part2)

		elif isinstance(state_change, Merge):
			i = state_change.i
			j = state_change.j

			# subtract off contribution of i and j
			ll_change = -self.__likelihood_partition(i)
			ll_change += -self.__likelihood_partition(j)

			# add back in contribution of edges_ij (subtracted twice in above)
			ll_change += self.__likelihood_partition_pair(self.state.edge_count(i,j), self.state.node_count(i), self.state.node_count(j))

			# add in contribution of merged ij
			ll_change += self.__likelihood_merge(i, j)

		elif isinstance(state_change, MergeSplit):
			i = state_change.i
			j = state_change.j

			# subtract off contribution of i and j
			ll_change = -self.__likelihood_partition(i)
			ll_change += -self.__likelihood_partition(j)

			# add back in contribution of edges_ij (subtracted twice in above)
			ll_change += self.__likelihood_partition_pair(self.state.edge_count(i,j), self.state.node_count(i), self.state.node_count(j))

			# add in contribution of merged ij
			ll_change += self.__likelihood_merge_and_split(i, j, state_change.g1, state_change.g2)

		elif isinstance(state_change, Flip):
			node = state_change.node
			i = state_change.i
			j = state_change.j
			assert self.state.get_partition_of_node(node) == i, "Node to flip is not in partition i!"
			ll_change = 0
			# subtract off contribution of i and j
			ll_change = -self.__likelihood_partition(i)
			ll_change += -self.__likelihood_partition(j)
			# add back in contribution of edges_ij (subtracted twice in above)
			ll_change += self.__likelihood_partition_pair(self.state.edge_count(i,j), self.state.node_count(i), self.state.node_count(j))
			ll_change += self.__likelihood_flip(node, i, j)

		elif not isinstance(state_change, NoOp):
			assert False, "Unrecognized change %s" % (NoOp.__class__)
		state_change.set_score_change(ll_change)
		return ll_change

	def set_state(self, state):
		self.state = state
		self.state.initialize()
		self.score = self.__likelihood()

	def split_partition(self, i):
		nodes = self.state.get_nodes(i)[:]

		g1 = nodes
		g2 = []
		g1_edges = {}
		g2_edges = {}
		edges_11 = self.state.edge_count(i)
		edges_22 = 0
		edges_12 = 0

		nbrs = self.state.neighbors(i)
		for j in nbrs:
			g1_edges[j] = self.state.edge_count(i, j)
			g2_edges[j] = 0

		while len(g2) < self.k:  

			# find best node from g1 to move to g2
			max = None
			argmax = None

			if random_split and len(g2) == 0:
				argmax = random.choice(g1)
			else:
				for node in g1:
					ll = 0

					# compute change in score between g1 and g2 if we move node to g2
					edges_node_1 = self.state.edge_count([node], g1)
					edges_node_2 = self.state.edge_count([node], g2)
					tmp_edges_11 = edges_11 - edges_node_1 
					tmp_edges_22 = edges_22 + edges_node_2
					tmp_edges_12 = edges_12 - edges_node_2 + edges_node_1

					ll += self.__likelihood_partition_pair(tmp_edges_11, len(g1)-1)
					ll += self.__likelihood_partition_pair(tmp_edges_22, len(g2)+1)
					ll += self.__likelihood_partition_pair(tmp_edges_12, len(g1)-1, len(g2)+1)

					# compute change in edge counts and score if we move node to g2
					for j in nbrs:
						nodes_j = self.state.node_count(j)

						# compute change in edges
						edges_node_j = self.state.edge_count([node], self.state.get_nodes(j))
						edges_1j = g1_edges[j] - edges_node_j
						edges_2j = g2_edges[j] + edges_node_j

						ll += self.__likelihood_partition_pair(edges_1j, len(g1)-1, nodes_j)
						ll += self.__likelihood_partition_pair(edges_2j, len(g2)+1, nodes_j)

					if ll > max:
						max = ll
						argmax = node

			assert argmax != None
			edges_node_1 = self.state.edge_count([argmax], g1)
			edges_node_2 = self.state.edge_count([argmax], g2)
			edges_11 = edges_11 - edges_node_1  
			edges_22 = edges_22 + edges_node_2
			edges_12 = edges_12 - edges_node_2 + edges_node_1
			assert edges_12 >= 0 and edges_11 >= 0 and edges_22 >= 0

			for j in nbrs:
				edges_node_j = self.state.edge_count([argmax], self.state.get_nodes(j))
				g1_edges[j] = g1_edges[j] - edges_node_j
				g2_edges[j] = g2_edges[j] + edges_node_j
				assert g1_edges[j] >= 0 and g2_edges[j] >= 0 
			g1.remove(argmax)
			g2.append(argmax)

		return [ Split(i, g1, g2) ]

	def successors(self):

		u = self.state.choose_random_node()
		i = self.state.get_partition_of_node(u)
		node_count = self.state.node_count(i)

		do_flip = False
		do_merge = False
		do_merge_split = False
		do_split = False

		if node_count == self.k:
			do_merge_split = True
		elif self.k < node_count and node_count < 2*self.k:
			do_flip = True
			do_merge_split = True
		elif 2*self.k <= node_count and node_count < 4*self.k:
			do_flip = True
			do_merge_split = True
			do_split = True
		else:
			assert node_count >= 4*self.k
			do_flip = True
			do_split = True

		successors = []
		if do_flip:
			for j in self.state.neighbors_two_hop(i):
				successors.append(Flip(u,i,j))
		if do_merge:
			successors += self.merge_partition(i)
		if do_merge_split:
			successors += self.merge_and_split_partition(i)
		if do_split:
			successors += self.split_partition(i)	

		return successors

	def temperature(self, time):
		if time > 0 and time % self.cycle_length == 0:
			if self.num_changes < self.min_changes_per_cycle:
				print "Only", self.num_changes, "changes in the last", self.cycle_length, "steps, exiting early."
				return 0
			else:
				self.num_changes = 0  # reset flip count
		if time < self.max_steps:
			return self.start_temp * pow(self.alpha, time)
		else:
			print "Reached max number of steps", self.max_steps
			return 0


