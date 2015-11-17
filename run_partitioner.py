# ----------------------------------------------------------------------------
# README
#
# This code illustrates how to invoke the partitioning algorithm described
# in:
#
# 	Resisting structural re-identification in anonymized social networks
# 	Michael Hay, Gerome Miklau, David Jensen, Don Towsley, and Philipp Weis
# 	Proceedings of the VLDB, 2008
#
# It first constructs a synthetic graph that will be used as input.  The graph
# is clustered, with edge density being high within clusters and low between 
# clusters.  The algorithm when run on this input will produce a generalized
# graph whose supernodes will generally correspond to the clusters (i.e., 
# nodes in the same cluster will be assigned to the same supernode).
# Each node in the synthetic graph has a name like "g10n2" indicating it is 
# node 2 in group 10.  Thus, in the generalized graph, if the nodes within 
# each supernode have the same graph number, this is an indication that the 
# algorithm partitioned the nodes into the "right" groups.
#
# This code also shows how to sample a simple graph from the generalized graph
# representation.  It also compares the clustering coefficient of the input 
# graph with the clustering coefficient of the sampled graph.
# ----------------------------------------------------------------------------

# external python modules
import networkx
import random

# internal python modules
import generalized_graph
import partitioner


# INITIALIZE PARAMETERS AND MAKE INPUT GRAPH
tmp_dir = "/tmp/"
group_size = 10

# ABOUT INPUT GRAPH:
# input graph is a toy graph that is highly clustered:
# 	- 20 clusters, each with 10 nodes, a total of 200 nodes
#	- for each possible edge (200 choose 2)
#	- insert edge between (u,v) with probability p where 
#	- p = .25 if (u,v) in same cluster
#	- p = .05 if (u,v) in different clusters
input_graph = networkx.Graph() 
random.seed(0)
for grp_id in range(20):
	for node_id in range(10):
		input_graph.add_node("g%dn%d" % (grp_id, node_id))
nodes = input_graph.nodes()
for u in nodes:
	for v in nodes:
		if u <= v:
			continue
		u_grp_id = u.split("n")[0]
		v_grp_id = v.split("n")[0]
		rand_val = random.random()
		if rand_val <= 0.002 or (rand_val <= 0.5 and u_grp_id == v_grp_id):
			input_graph.add_edge(u, v)
input_graph.name = "test_graph"
print "Created input graph"


# RUN PARTITIONING ALGORITHM
# partitioner.debug = True # turn on debugging
# partitioner.debug_sampling = True
partitioner = partitioner.MinNumWorldsPartitioner(g=input_graph, k=group_size, working_dir=tmp_dir, max_steps=5000)
p = partitioner.partition()

print "Printing the node partition"
grp_cnt = 1
for grp in p:
	print "Group #%d, Members:" % grp_cnt,
	print p.get_members(grp)
	grp_cnt += 1

# SAMPLE SIMPLE GRAPH FROM GENERALIZED GRAPH
gen_graph = generalized_graph.GeneralizedGraph(input_graph, p, alg="Hay et al. 2008", k=group_size)
print "Created generalized graph"

sampled_graph = gen_graph.sample_graph()
print "Sampled a simple graph from generalized graph"
print "Input graph has %d nodes and %d edges" % (input_graph.number_of_nodes(), input_graph.number_of_edges())
print "Sampled graph has %d nodes and %d edges" % (sampled_graph.number_of_nodes(), sampled_graph.number_of_edges())

orig_clustering = networkx.average_clustering(input_graph)
clustering = networkx.average_clustering(sampled_graph)
print "Input graph had clustering coefficient of %0.2g\nSampled graph has clustering of %0.2g" % (orig_clustering, clustering)
