# ----------------------------------------------------------------------------
# This is an implementation of local search (simulated annealing) to find a
# partition of the nodes that maximizes the likelihood (similar to minimizing
# number of possible worlds).
#
# Notice search relies on a Problem object, which essentially manages the 
# problem-specific details (state space, scoring current state, proposing 
# new states, etc.).
# ----------------------------------------------------------------------------

import math
import pickle
import random
import sys
random.seed(1)

import partition
import utils_lite as utils

sample_successor = False

def annealing(problem, pickle_filename=None, working_dir=None):	
	logging_cycle = 10
	checkpoint_cycle = 100

	t = 0
	max_score = problem.get_score()
	argmax_score = problem.copy_state()
	max_saved_score = None
	
	uphill = 0
	downhill = 0
	stationery = 0

	while True:

		problem.sanity_check()

		score = problem.get_score()
		assert score <= 0, "Positive score! Expected score is log-likelihood which is <= 0"
		if score > max_score:
			argmax_score = problem.copy_state()
			max_score = score
			if 0-score < 0.0000001:
				print "Found state with score=%g, exiting" % (round(score, 3))
				return argmax_score
	
		if t % checkpoint_cycle == 0:
			state = problem.copy_state()
			filename_state = working_dir + '/%s.%d.i.%d.partition' % (state.g.name, problem.k, t)
			print "checkpoint: saving state to filename=%s" % filename_state
			intermediate_partition = []
			for gid in state.get_partitions():
				intermediate_partition.append(state.get_nodes(gid))
			p = partition.Partition(groups=intermediate_partition)
			p.save(filename_state)
	
			if max_score > max_saved_score:
				state = argmax_score
				filename_best = working_dir + '/%s.%d.b.partition' % (state.g.name, problem.k)
				print "checkpoint: saving best (with score=%g) to filename=%s" % (max_score, filename_best)
				intermediate_partition = []
				for gid in state.get_partitions():
					intermediate_partition.append(state.get_nodes(gid))
				p = partition.Partition(groups=intermediate_partition)
				p.save(filename_best)
				max_saved_score = max_score
			
			
		if t % logging_cycle == 0:

			avg_size = 1. * sum(map(len, problem.get_current_state().partition.values())) \
			/ problem.get_current_state().num_partitions()
			(noops, splits, merges, mergesplits, flips, cache_hit_rate) = problem.get_stats()
			s = "noops=%d splits=%d merges=%d mergesplits=%d flips=%d cache=%g" % (noops, splits, merges, mergesplits, flips, cache_hit_rate)
			
			if merges > 0:
				(nbr_merge, nbr_nbr_merge, nonnbr_merge) = \
				(1.*problem.nbr_merge/merges,\
				1.*problem.nbr_nbr_merge/merges, \
				1.*problem.nonnbr_merge/merges)
				s2 = "nbr_merge=%g nbr_nbr_merge=%g nonnbr_merge=%g" % (nbr_merge, nbr_nbr_merge, nonnbr_merge)
				problem.nbr_merge = problem.nbr_nbr_merge = problem.nonnbr_merge = 0
			else:
				s2 = "nbr_merge=%g nbr_nbr_merge=%g nonnbr_merge=%g" % (0,0,0)
			
			assert t == 0 or (uphill + downhill + stationery) == logging_cycle, "Some moves unnaccounted!"
			print "steps=%d n=%d k=%d avg_size=%g uphill=%g downhill=%g stationery=%g %s %s ll=%g" % \
			(t, problem.n, problem.k, round(avg_size,2), 1.*uphill/logging_cycle,  \
			1.*downhill/logging_cycle, \
			1.*stationery/logging_cycle, \
			s, s2, score)
			uphill = downhill = stationery = 0
				
				
			sys.stdout.flush()
		
		T = problem.temperature(t)
		if T == 0:
			return argmax_score

		state_changes = problem.successors()
		scores = []
		for state_change in state_changes:
			score = problem.score_change(state_change)
			assert str(score) != 'nan'
			scores.append(score)
		
		if len(scores) > 0:
			if sample_successor:
				probs = utils.normalize(scores, 1./T)
				idx = utils.sample(probs)
				score_change = scores[idx]
			else:
				idx = utils.get_max(scores)
				score_change = scores[idx]
			
			if score_change > 0: 
				uphill += 1
				problem.apply_change(state_changes[idx])
			elif random.random() < math.exp(score_change/T):
				downhill += 1
				problem.apply_change(state_changes[idx])
			else:
				stationery += 1
				problem.apply_noop_change()
		else:
			stationery += 1
			problem.apply_noop_change()
		t += 1
