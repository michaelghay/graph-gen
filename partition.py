
class Partition(object):
	def __init__(self, groups):
		"Takes a list of lists"
		self.id_to_gid = {}
		self.gid_to_ids = {} 
		gid = 0
		for group in groups:
			for item_id in group:
				assert item_id not in self.id_to_gid
				self.id_to_gid[item_id] = gid
				if gid not in self.gid_to_ids:
					self.gid_to_ids[gid] = []
				self.gid_to_ids[gid].append(item_id)
			gid += 1
	
	def __iter__(self):
		return self.gid_to_ids.__iter__()
		
	def keys(self):
		return self.gid_to_ids.keys()
		
	def nodes(self):
		return self.id_to_gid.keys()

	def get_group(self, u):
		return self.id_to_gid[u]

	def get_members(self, gid):
		return self.gid_to_ids[gid][:]
	
	def get_min_group_size(self):
		return min(map(len, self.gid_to_ids.values()))

	def get_size(self, gid):
		return len(self.gid_to_ids[gid])

	def save(self, filename):
		f = open(filename, 'w')
		for item_id in self.id_to_gid:
			f.write("%s %s\n" % (str(item_id), str(self.id_to_gid[item_id])))
		f.close()

def load(filename):
	p = Partition([])
	f = open(filename, 'r')
	for line in f:
		(item_id, gid) = line.split()
		p.id_to_gid[item_id] = gid
		if gid not in p.gid_to_ids:
			p.gid_to_ids[gid] = []
		p.gid_to_ids[gid].append(item_id)
	f.close()
	return p

