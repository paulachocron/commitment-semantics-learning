import random
import copy
import os, sys, getopt
from operator import itemgetter
import json
import math, string
from collections import namedtuple
import threading
from multiprocessing import Pipe


__location__ = os.path.realpath(
	os.path.join(os.getcwd(), os.path.dirname(__file__)))



#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**# COMMITMENT DEFINITION #**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#

# A commitment operation is a tuple (op,v,v) or None

class Commitment(namedtuple('Commitment', 'operation, antecedent, consequent')):
	__slots__ = ()
	
	def __str__(self):
		'Return a nicely formatted representation string'
		if self.operation==None:
			return 'none'
		else:
			return '{}({}, {})'.format(self.operation, self.antecedent, self.consequent)

	def __repr__(self):
		'Return a nicely formatted representation string'
		if self.operation==None:
			return 'none'
		else:
			return '{}({}, {})'.format(self.operation, self.antecedent, self.consequent)


#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#** GENERATORS #**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#

def regula_generator(vocabulary, type='cancel'):
	"""Generates a set of meanings.
		Receives a vocabulary and a parameter cancels (true if there are cancels in the operations)
		Idem for releases (true if there are releases in the operations)
		Returns a dictionary relating each word in the vocabulary with one Axiom or Commitment"""
	found = False
	while not found:

		regula = {}

		for v in vocabulary:
			uncancelled = [(r.antecedent,r.consequent) for r in regula.values() if r.operation=='create' and not (r.antecedent==v or r.consequent==v) and not [r2 for r2 in regula.values() if r2.operation=='cancel' and r2.antecedent==r.antecedent and r2.consequent==r.consequent]]
			unreleased = [(r.antecedent,r.consequent) for r in regula.values() if r.operation=='create' and not (r.antecedent==v or r.consequent==v) and not [r2 for r2 in regula.values() if r2.operation=='release' and r2.antecedent==r.antecedent and r2.consequent==r.consequent]]
			options = ['none', 'create']
			if not type=='create':
				if unreleased:
					options.append('release')
	
				if type=='cancel':
					if uncancelled:
						if not any(regula[v].operation=='cancel' for v in regula.keys()):
							options = ['cancel']
						else:
							options.append('cancel')			
			operation = random.choice(options)

			if operation == 'none':
				regula[v]= Commitment(None,None,None)
			else:
				if operation=='cancel':
					# only cancel already created commitments
					antecedent, consequent = random.choice(uncancelled)			
				elif operation=='release':
					# only release already created commitments
					antecedent, consequent = random.choice(unreleased)			
				else:		
					antecedent = random.choice([w for w in vocabulary if not w==v])
					consequent = random.choice([y for y in vocabulary if not y==v and not y==antecedent])
				regula[v] = Commitment(operation, antecedent, consequent)
				
				if not type=='cancel':
					found = True
	
		if type=='cancel':
			if any(regula[v].operation=='cancel' for v in vocabulary):
				found = True
	return regula


def policies_generator(regula, size, asterisks=0):
	"""Generates a set of cancel policies: restrictions over a vocabulary.
		Receives a regula (only the creates that appear in the regula should be considered)
		And a size (number of constraints)
	"""
	rcancels = [op for op in regula.values() if op.operation == 'create']
	policy = {}
	if not rcancels:
		return policy

	for i in range(size):

		if not rcancels:
			return policy
		cancelc = random.choice(rcancels)
		rcancels.remove(cancelc)
		if asterisks:
			cancel = Commitment('cancel', cancelc.antecedent, '*')
		else:
			cancel = cancelc
		poss = [v for v in regula.keys() if not (regula[v].operation=='cancel' or v==cancelc.consequent or v==cancelc.antecedent or Commitment('create', cancelc.antecedent, cancelc.consequent)==regula[v])] # is there any restriction on what the word could be?
		word = random.choice(poss)

		policy[cancel] = word
		found = True
	return policy


def policy_ok(cancelop, interaction, policy):
	""" Necessary to create an interaction that complies with a policy"""
	
	prevs = []
	if cancelop.operation=='cancel':
		cancelop1 = Commitment('cancel','*',cancelop.consequent)
		cancelop2 = Commitment('cancel',cancelop.antecedent, '*')
		cancelop3 = Commitment('cancel','*', '*')

		for op in [cancelop, cancelop1, cancelop2, cancelop3]:
			if op in policy:
				prevs.append(policy[op])

		for p in prevs:
			if not (0,p) in interaction or (1,p) in interaction:
				return False
	return True


def interaction_generator(regula, vocabulary, bound, policy, times):
	"""Generates an interaction.
		Receives a regula, a vocabulary, a lenght 
		If fails is true, the method creates a wrong interaction with 1/3 of probability
		Returns a secuence of length bound of pairs (agent, message) with pattern [0,1,0,1,...]"""
	
	guilty_canc = []
	found = False

	while not found:
		speaker = 1
		interaction = []
		for b in range(bound):
			speaker = 1-speaker

			ok = [v for v in vocabulary if policy_ok(regula[v], interaction, policy)]
			hards = [v for v in policy.values() if v in ok and not (0,v) in interaction or (1,v) in interaction]

			all_poss = [v for v in ok if not (is_activeBy(regula,v,speaker,interaction) or is_detachedBy(regula,v,speaker,interaction))]

			det = get_detachedBy(regula, speaker, interaction)

			det_oth = get_detachedBy(regula, 1-speaker, interaction)

			voc_oth = [r.consequent for r in det_oth]
			to_det = [regula[v].antecedent for v in vocabulary if is_activeBy(regula, v, 1-speaker, interaction) and regula[v].antecedent in ok]

			positive = [v for v in ok if regula[v].operation=='create']
			poss = [v for v in ok if not (regula[v].operation=='cancel' or regula[v].operation=='release')]			
			cancel = [v for v in ok if regula[v].operation=='cancel' and (regula[v].antecedent, regula[v].consequent)  in [(r.antecedent, r.consequent) for r in det]]
			
			release = [v for v in ok if regula[v].operation=='release' and (regula[v].antecedent, regula[v].consequent)  in [(r.antecedent, r.consequent) for r in det_oth]]
			cancel_nd = [v for v in ok if regula[v].operation=='cancel' if not (regula[v].antecedent, regula[v].consequent)  in [(r.antecedent, r.consequent) for r in det_oth]]
			disch = [r.consequent for r in det if r.consequent in ok] 
					
			if not poss:
				break
			if det:
				chdisch = []
				for i in xrange(times):
					chdisch.extend(disch)
				choices = [v for v in chdisch+to_det+cancel+all_poss]
				if choices:
					ut = random.choice(choices)
				else:
					ut = random.choice(all_poss)
			else:
				if to_det or release:
					ap = min(3, len(all_poss))
					choices = to_det+to_det+release+random.sample(ok,ap)
					ut = random.choice(choices)
				else:
					if positive:
						ut = random.choice(positive+positive+ok)
					else:
						ut = random.choice(ok+hards)

			interaction.append((speaker,ut))

		if not(get_detachedBy(regula, 0, interaction) or  get_detachedBy(regula, 1, interaction)):
			if any((m[0]==0 and regula[m[1]].operation=='cancel') for m in interaction):
				guilty_canc.append(0)
			if any((m[0]==1 and regula[m[1]].operation=='cancel') for m in interaction):
				guilty_canc.append(1)
			found = True
		
	return interaction, guilty_canc


#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#* Operations on Interactions #**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#

def saidBy(interaction, agent, word):
	"""Returns true if the agent has said the word in the interaction"""
	if (agent, word) in interaction:
		return True
	else:
		return False

def wSaid(interaction, word):
	"""Returns the first agent that said word in the interaction, or None if it was not said"""
	l = [t for t in interaction if t[1]==word]
	if l:
		return l[0][0]
	else:
		return None

def said(interaction, word):
	"""Returns true if the word was said by any agent in the interaction"""
	return not wSaid(interaction,word)==None

def cancelled(regula, interaction, agent, r):
	"""Returns true if agent has cancelled the commitmment created by r in the interaction"""
	found = [m for m in interaction if regula[m[1]].operation=='cancel' and regula[m[1]].antecedent==r.antecedent and regula[m[1]].consequent==r.consequent and m[0]==agent]	
	return len(found)>0

def released(regula, interaction, agent, r):
	"""Returns true if agent has released the commitmment created by r in the interaction"""
	found = [m for m in interaction if regula[m[1]].operation=='release' and regula[m[1]].antecedent==r.antecedent and regula[m[1]].consequent==r.consequent and m[0]==agent]	
	return len(found)>0

def get_detachedBy(regula, agent, interaction):
	""" Returns all the commitments where agent is debtor that are detached in interaction"""
	detached = []
	for v in regula.keys():
		c = regula[v]
		if is_detachedBy(regula, v, agent, interaction):
			detached.append(Commitment(c.operation, c.antecedent, c.consequent))
	return detached

def get_activeBy(regula, agent, interaction):
	""" Returns all the commitments where agent is debtor that are detached in interaction"""
	active = []
	for v in regula.keys():
		c = regula[v]
		if is_activeBy(regula, v, agent, interaction):
			active.append(Commitment(c.operation, c.antecedent, c.consequent))
	return active

	
def unsaid(vocabulary, interaction, i):
	return [v for v in vocabulary if not v in interaction[i:]]

def unsaidBy(vocabulary, interaction, i, ag):
	return [v for v in vocabulary if not (ag, v) in interaction[i:]]


def is_detachedBy(regula, v, agent, interaction):
	""" Returns true if the commitment c was detached with agent as debtor"""
	c = regula[v]
	if saidBy(interaction, agent, v) and c.operation=='create':
		
		indexes_n = [i for i in range(len(interaction)) if interaction[i]==((agent,v))]

		for index_n in indexes_n:
			new_int = interaction[index_n:]
			if saidBy(new_int,1-agent, c.antecedent):
				index_a = new_int.index((1-agent,c.antecedent))
				#before
				# if not (saidBy(new_int[index_a:],agent,c.consequent) or cancelled(regula, new_int[index_a:], agent, c) or released(regula, new_int[index_a:], 1-agent, c)):
				# now
				if not (saidBy(new_int[index_a:],agent,c.consequent) or cancelled(regula, new_int[index_n:], agent, c) or released(regula, new_int[index_n:], 1-agent, c)):
					return True
	return False


def is_activeBy(regula,v, agent, interaction):
	""" Returns true if the commitment c is active in the interaction with agent as debtor"""
	c = regula[v]
	if c.operation == 'create':
		for i in range(len(interaction)):
			if interaction[i][0]==agent and interaction[i][1]==v:
				return not (1-agent,c.antecedent) in interaction[i:]
	return False


def is_dischargedBy(v,c, agent1, agent2, interaction):
	""" Returns true if the commitment c was discharged, with agent1 as debtor and agent2 as creditor"""
	if saidBy(interaction, agent1, v) and c.operation=='create':
		index_n = interaction.index((agent1,v))
		if saidBy(interaction[index_n:],1-agent1, c.antecedent):
			index_a = interaction.index((1-agent1,c.antecedent))
			if saidBy(interaction[index_a:],agent2,c.consequent):
				return True

def get_discharged(regula, interaction):
	""" Returns all discharged commitments in the interaction"""
	discharged = []
	for r in regula:
		if r.operation=='create' and r.word in interaction:
			index_n = interaction.index(r.word)
			if r.antecedent in interaction[index_n:]:
				index_a = interaction.index(r.antecedent)
				if r.consequent in interaction[index_a:]:
					discharged.append(r)
	return discharged


def is_openBy(v, c, agent, interaction):
	""" Returns true if the commitment c was detached with agent as debtor (from the student's point of view)"""

	if saidBy(interaction, agent, v) and c.operation=='create':		
		indexes_n = [i for i in range(len(interaction)) if interaction[i]==((agent,v))]

		for index_n in indexes_n:
			new_int = interaction[index_n:]
			if saidBy(new_int,1-agent, c.antecedent):
				index_a = new_int.index((1-agent,c.antecedent))
				if not saidBy(new_int[index_a:],agent,c.consequent):
					return True
	return False


#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**# STUDENTS *#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#

class Student(object):
	"""The offline student agent that learns from observing interactions"""

	def __init__(self, params):
		self.alignment = {}
		self.params = params

	def update_creates(self, interaction, i, pun=0):
		"""Update for the create commitments for interaction[i]
			Adds new ones and modifies the value of existing ones"""

		debtor = interaction[i][0]
		pos_ant = []
		possible_comm = []

		for j in range(i+1, len(interaction)):
				
			if interaction[j][0] == 1-debtor and not interaction[j][1] in pos_ant:
				pos_ant.append(interaction[j][1])
				for h in range(j+1, len(interaction)):
					if interaction[h][0]==debtor:
						if not (interaction[j][1]==interaction[i][1] or interaction[h][1]==interaction[i][1] or interaction[h][1]==interaction[j][1]):
							possible_comm.append(Commitment('create',interaction[j][1], interaction[h][1]))
		for c in possible_comm:
			if c in self.alignment[interaction[i][1]]:	
				self.alignment[interaction[i][1]][c] += self.params['p0']
			else:
				self.alignment[interaction[i][1]][c] = self.params['p0']

			if verbose:
				print "rew {} {}".format(interaction[i][1],c)


	def update_cancels_policy(self, interaction, policy):

		for i in range(len(interaction)):
			w = interaction[i][1]
			a = interaction[i][0]

			if w in self.alignment.keys():
				poss_cancels = (com for com in self.alignment[w] if com.operation=='cancel')

				for pc in poss_cancels:
					dependencies = []
					pc1 = Commitment('cancel','*',pc.consequent)
					pc2 = Commitment('cancel',pc.antecedent, '*')
					pc3 = Commitment('cancel','*', '*')

					for op in [pc, pc1, pc2, pc3]:
						if op in policy:
							dependencies.append(policy[op])

					for d in dependencies:
						if not (0,d) in interaction[:i] or (1,d) in interaction[:i]:
							self.alignment[w][pc] -= self.params['p5']
							if verbose:
								print "policy punish {} {}".format(w, pc)
		return
			
	def nocancels(self, interaction, agent):
		"""Update for cancel commitments when the debtor was not punished """

		for i in xrange(len(interaction)):
			if interaction[i][0] == agent:			
				v = interaction[i][1]
				debtor = interaction[i][0]
				poss_create = [c for c in self.alignment[v] if c.operation=='create']
				
				for c in poss_create:
					cancel = Commitment('cancel',c.antecedent, c.consequent)
					for j in range(i, len(interaction)):
						if interaction[j] == (1-agent, c.antecedent):
							#before
							# for m in interaction[j:]:
							#now
							for m in interaction[i:]:
								if m[0]==debtor and cancel in self.alignment[m[1]]:
									self.alignment[m[1]][cancel] -= self.params['p4']

									if verbose:
										print "punish no can {} {}".format(m[1],cancel)

	def punish_creates_canc(self, interaction):
		"""Update for create commitments (for punishment and policy) """

		for m in interaction:
			debtor = m[0]
			v = m[1]	

			comm = 	[c for c in self.alignment[v] if c.operation=='create']
			for c in comm:
				cc = Commitment('cancel', c.antecedent, c.consequent)
				cr = Commitment('release', c.antecedent, c.consequent)
				if is_openBy(v,c, debtor, interaction) and all((not cc in normalizeV(self.alignment,vv[1]) or normalizeV(self.alignment,vv[1])[cc]<self.params['ep2']) and (not cr in normalizeV(self.alignment,vv[1]) or normalizeV(self.alignment,vv[1])[cr]<self.params['ep2']) for vv in interaction):							
					self.alignment[v][c] -= self.params['p6']
					if verbose:
						print "punish create can {} {}".format(v,c)

	def update_cancels(self, interaction, guilty_canc):
		"""Updating for the cancel commitments for interaction[i]
			Adds new ones and modifies the value of exiting ones"""

		if verbose:		
			print "guilty cancels: {}".format(guilty_canc)

		if not 1 in guilty_canc:
			self.nocancels(interaction, 1)
		if not 0 in guilty_canc:
			self.nocancels(interaction, 0)

		for i in xrange(len(interaction)):		
			v = interaction[i][1]
			debtor = interaction[i][0]
			creditor = 1-debtor
			norm = normalizeV(self.alignment, v)
			comm = (k for k in self.alignment[v].keys() if k.operation=='create' and k in norm.keys())
			updc = []
			updr = []

			for c in comm:
				values = []

				detached = False
					
				for h in xrange(i+1,len(interaction)):
					if interaction[h]==(creditor, c.antecedent):
						detached=True
						break

				if not detached:
					continue

				if not (debtor, c.consequent) in interaction[h:]:

					#before
					# for j in xrange(h+1, len(interaction)):
					#now
					for j in xrange(i+1, len(interaction)):
						m = interaction[j]
						w = m[1]
									
						if not (w==v or w==c.antecedent or w==c.consequent):
							if m[0] == debtor and debtor in guilty_canc and not (w,c.antecedent,c.consequent) in updc:
								canres = Commitment('cancel',c.antecedent, c.consequent)
								upd = self.params['p1']
								updc.append((w,c.antecedent,c.consequent))
							elif m[0]==creditor and not (w,c.antecedent,c.consequent) in updr:
								canres = Commitment('release',c.antecedent, c.consequent)
								upd = self.params['p2']
								updr.append((w,c.antecedent,c.consequent))
							else:
								continue

							values.append(1)
							
							if not canres in self.alignment[w]:
								self.alignment[w][canres] = 0

							val = norm[c]
							self.alignment[w][canres] +=  upd * val * val
							if verbose:
								print "rew {} {} {}".format(w,canres,val)

					if not values:
						self.alignment[v][c] -= self.params['p3']
						if verbose:
							print "punish create {} {}".format(v,c)
		return


	def initialize(self, interaction):
		"""Initialize dict with new words"""
		for m in interaction:
			if not m[1] in self.alignment.keys():
				self.alignment[m[1]] = {}


	def learn_base(self, interaction):
		"""Implementation of create learning"""
		self.initialize(interaction)
		for i in range(len(interaction)):	
			self.update_creates(interaction,i)

	def learn_release(self, interaction, policy):
		"""Implementation of commin-release (with cancels but nor violations)"""		
		self.initialize(interaction)
		for i in range(len(interaction)):	
			self.update_creates(interaction,i)

		self.update_cancels(interaction, [0,1])

		if policy != {}:
			self.update_cancels_policy(interaction, policy)
			self.punish_creates_canc(interaction)

		self.clean_dict()


	def learn_puncanc(self, interaction, policy, guilty_canc):
		"""Implementation of commin-release (with cancels but nor violations)"""

		self.initialize(interaction)		
		for i in xrange(len(interaction)):	
			self.update_creates(interaction,i, pun=0)
		
		# Now update the cancels
		self.update_cancels(interaction, guilty_canc)

		self.punish_creates_canc(interaction)
		self.clean_dict()
	
		
	def clean_dict(self):
		""" Cleans the dictionary removing low values (performance only)"""
		maxi = {}
		for k in self.alignment.keys():
			if [w for w in self.alignment[k].keys()]:
				maxi[k] = max({w: self.alignment[k][w] for w in self.alignment[k].keys()}.values())

		for v in self.alignment.keys():
			to_delete = []
			for w in self.alignment[v].keys():
				if self.alignment[v][w]<0 or (v in maxi and maxi[v]-self.alignment[v][w]>(self.params['ep'])):
					to_delete.append(w)

			for w in to_delete:
				del self.alignment[v][w]

	# def clean_dict(self):
	# 	# pass
	# 	maxncreate = {}
	# 	for k in self.alignment.keys():
	# 		if [w for w in self.alignment[k].keys() if w.operation!='create']:
	# 			maxncreate[k] = max({w: self.alignment[k][w] for w in self.alignment[k].keys() if w.operation!='create'}.values())

	# 	for v in self.alignment.keys():
	# 		to_delete = []
	# 		for w in self.alignment[v].keys():
	# 			# if w.operation!='create' and :
	# 				# if self.alignment[v][w]<0 or (maxcreate[v]>2 and self.alignment[v][w]<1) or maxcreate[v]-self.alignment[v][w]>4:
	# 			# if self.alignment[v][w]<0:
	# 			if self.alignment[v][w]<0 or (v in maxncreate and maxncreate[v]-self.alignment[v][w]>10):
	# 				# if (maxcreate[v]>2 and self.alignment[v][w]<1) or maxcreate[v]-self.alignment[v][w]>4:
	# 				to_delete.append(w)

	# 		for w in to_delete:
	# 			del self.alignment[v][w]

#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#** Interacting Agents *#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#


def runAg(agent, connection, pattern):
	result = agent.interact(connection, pattern)
	return result

def start_interaction(agent1, agent2, pattern):
	""" Starts interaction between two agents"""
	first_conn, second_conn = Pipe()
	result_1 = []
	result_2 = []

	a1 = threading.Thread(target=runAg, args=(agent1, first_conn, pattern))
	a2 = threading.Thread(target=runAg, args=(agent2, second_conn, pattern))

	a1.start()
	a2.start()
	a1.join()
	a2.join()

	return agent1.interaction

class Agent(object):
	def __init__(self, id, regula):
		self.id = id
		self.regula = regula
		self.interaction = []
		self.interloc = 1-self.id

	def interact(self, connection, pattern):
		"""Start an interaction with an agent"""
		self.interaction = []
		bound = len(pattern)
		for t in pattern: 
			if t==self.id:
				utterance = self.choose_utterance(bound)
				if not utterance:
					connection.send('failed')
					if verbose:
						print "failed by sender"
					return 0

				connection.send(utterance)
				self.interaction.append((self.id, utterance))
				conf = connection.recv()
				if conf != 'ok':
					return 0
			else:
				received = connection.recv()
				if received=='failed':
					return 0
				self.interaction.append((self.interloc, received))
				if not received in self.regula:
					self.regula[received] = Commitment(None, None, None)
				connection.send('ok')

		return self.interaction

	def choose_utterance(self, bound):
		remaining = (bound - len(self.interaction))-1
		if self.id==1:
			my_rem = remaining/2
			their_rem = remaining/2
		else:
			my_rem = remaining/2
			their_rem = remaining/2 +1

		possible = []
		for v in self.regula.keys():
			inter2 = copy.copy(self.interaction)
			inter2.append((self.id, v))
			detached = get_detachedBy(self.regula, self.id, inter2)
			condet = [c.consequent for c in detached]
			active = get_activeBy(self.regula, self.id, inter2)
			conact = [c.consequent for c in active]

			if len(list(set(condet)))+min(their_rem,len(list(set(conact))))<=my_rem:
				possible.append(v)

		if self.id==0:
			possible = self.regula.keys()

		if not possible:
			return None

		if self.id==1:
			better = []
		else:
			better = [v for v in possible if [c for c in get_activeBy(self.regula, 1, self.interaction) if c.antecedent==v]]
		if better:
			chosen = random.choice(better)
		else:
			chosen = random.choice(possible)
		return chosen


#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#** Operations on Alignments *#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#


def precision_recall(regula,alignment,ep=20):
	if not alignment: 
		return 0,0
	else:
		max_alg = get_maxalg(alignment,ep)
		correct = sum(1 for k in alignment.keys() if max_alg[k] == regula[k])
		incorrect = {k : (regula[k], max_alg[k]) for k in max_alg if not max_alg[k] == regula[k]}
		
		return (float(correct)/float(len(alignment.keys())), float(correct)/float(len(regula.keys())), incorrect)

def normalizeV(alignment, v):
	new_dict = {}
	sumV = sum([val for val in alignment[v].values() if val>0])
	if not sumV==0:
		for k in alignment[v].keys():
			if alignment[v][k] > 0:
				new_dict[k] = alignment[v][k] / float(sumV)
	return new_dict

def normalize( alignment):
	new_dict = {}
	for v in alignment:
		new_dict[v] = normalizeV(alignment, v)
	return new_dict


def get_maxalg(alignment, ep=15):
	maxalg = {}
	if not alignment: 
		return 0

	for k in alignment:
		maxalg[k] = Commitment(None, None, None)
		if alignment[k]:
			maxtup = max(alignment[k].iteritems(), key=itemgetter(1))
			# maxalg[k] = maxtup[0]	
			
			if any(kk != maxtup[0] and  maxtup[1]-ep<alignment[k][kk] for kk in alignment[k]):
				maxalg[k] = Commitment(None, None, None)
			else:
				maxalg[k] = maxtup[0]

	return maxalg


#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#** Experiments *#**#**#**#**#**#**#**##**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#

def learn_regula(interactions, regula, params):
	""" Experiment for the offline student """

	bounds = [4,6,8,10]
	vocab = regula.keys()
	st = Student(params)
	policy = {}
		
	for j in range(interactions):
		bound = random.choice(bounds)
		interaction, pun = interaction_generator(regula, vocab, bound, policy,1)
		st.learn_release(interaction, policy)

		if verbose:
			print "\n Interaction {}".format(j)
			print interaction

	return get_maxalg(st.alignment, ep=params['epp'])


def experiment1(voc, outiter, initer, interactions):
	vocab = random.sample(list(string.lowercase), voc)
	verbose1 = 0

	params = {'p0': 4,'p1': 2,'p2': 2,'p3': 200,'p4': 0.7,'p5': 2,'p6': 0.5, 'ep': 10, 'epp': 10}
	params['ep2'] = 3.0/len(vocab)
	success_exp = []

	for i in range(outiter):
		reg0 = regula_generator(vocab)
		if verbose1:
			print "original regula: {}".format(reg0)
			
		bound = 6

		success_reg = []
		reg1 = learn_regula(interactions,reg0, params)
		if verbose1:
			print "learned regula: {}".format(reg1)
			
		# the agent with the original regula
		a0 = Agent(0,reg0)
		# the agent with the learned regula
		a1 = Agent(1,reg1)


		patterns = [[0,1] for p in range(bound/2)]
		pattern = [e for l in patterns for e in l]

		for it in range(initer):
			interaction = start_interaction(a0, a1, pattern)
			detached = get_detachedBy(reg0, 1, interaction)

			if verbose1:
		 		print "interaction: {}".format(interaction)
				print "detached: {}".format(detached)
		 		print "-------"

		 	if not detached:
		 		success_reg.append(1)
 	
		success_exp.append(sum(success_reg)/float(initer))
		print "success for {} : {}".format(interactions, sum(success_reg)/float(initer)) 

	print "success rate for {} : {}".format(interactions, sum(success_exp)/float(outiter))



def experiment2(iterations, int, voc, type, times):
	
	""" Experiment for the offline student """
	
	results = []
	allTemp = []
	conv = []
	precTot = []

	vocab = random.sample(list(string.lowercase), voc)
	bounds = [4,6,8,10]


	# Set particular variables for each experiment type
	limit = 0
	# params = {'p0': 2,'p1': 1,'p2': 1,'p3': 200,'p4': 200,'p5': 2,'p6': 0.2, 'ep': 10, 'epp': 60}
	# # params['epp'] = 30

	# if type == 'punish':
	# 	params = {'p0': 2,'p1': 4,'p2': 1.5,'p3': 200,'p4': 20,'p5': 2,'p6': 0.8, 'ep': 10, 'epp': 10}

	# if type == 'policy':
	# 	params = {'p0': 1.5,'p1': 4,'p2': 0.5,'p3': 200,'p4': 20,'p5': 20,'p6': 0.8, 'ep': 10, 'epp': 5}
		
	# if type=='frequency':
	# 	limit = int/10


	# params['ep2'] = 2.0/len(vocab)
	
	params = {'p0': 2,'p1': 2,'p2': 2,'p3': 200,'p4': 200,'p5': 2,'p6': 0.2, 'ep': 10, 'epp': 30}

	if type == 'punish':
		params = {'p0': 3,'p1': 3,'p2': 1,'p3': 200,'p4': 20,'p5': 2,'p6': 0.8, 'ep': 10, 'epp': 30}

	if type == 'policy':
		# original
		# params = {'p0': 3,'p1': 4, 'p2': 1,'p3': 200,'p4': 20,'p5': 1,'p6': 0.5, 'ep': 10, 'epp': 30}
		params = {'p0': 2,'p1': 2, 'p2': 0.5,'p3': 200,'p4': 20,'p5': 2,'p6': 0.5, 'ep': 10, 'epp': 10}
		
	if type=='frequency':
		limit = int/10

	params['ep2'] = 2.0/len(vocab)

	for i in range(iterations):
		
		# Create the specification
		if type == 'create':
			regula = regula_generator(vocab, 'create')
		elif type == 'release':
			regula = regula_generator(vocab, 'release')
		else:
			regula = regula_generator(vocab)
		
		# Create policy
		if type=='policy': 
			spolicy = len([c for c in regula if regula[c].operation=='create'])
			policy = policies_generator(regula, spolicy, 1)
		else:
			policy = {}

		# Create the student
		st = Student(params)
		resultsTemp = []
		timeTemp = []

		print "\n Iteration: {}".format(i)
		# print "regula: {}".format(regula)
		# print "\n policy {}".format(policy)
		
		for j in range(int):
			bound = random.choice(bounds)

			# Create the interaction
			interaction, guilty_canc = interaction_generator(regula, vocab, bound, policy, times)

			if verbose:
				print "\n Interaction {}".format(j)
				print interaction

			if j<limit:
				st.learn_base(interaction)
			else:
				if type=='punish':
					if verbose:
						print "guilty cancels: {}".format(guilty_canc)
					st.learn_puncanc(interaction, policy, guilty_canc)
				else:
					st.learn_release(interaction, policy)

			ep = params['epp']
			prect,rect, incorrect = precision_recall(regula, st.alignment, ep)
			
			if verbose:
				print "alignment {} ".format("\n \n".join([v + " : " + str(sorted(st.alignment[v].items(),key=itemgetter(1))) for v in st.alignment.keys()]))
				print "\n regula: {}".format(regula)
				print "\n policy {}".format(policy)
				print ""
				print "maxalg:{}".format(get_maxalg(st.alignment),ep)
				print "p {} r {} ".format(prect,rect)
				print "incorrect: {}".format(incorrect)

			resultsTemp.append((prect,rect))
			
			if prect ==1.0 and rect == 1.0:
				precTot.append(prect)
				conv.append(j)
				print j
				if verbose:
					print j
				for h in range(j+1, int):
					resultsTemp.append((1.0,1.0))
				break	

		# print "maxalg:{}".format(get_maxalg(st.alignment),ep)
		print "precision: {}, recall: {}".format(prect,rect)
		print ""
		print "incorrect: {}".format(incorrect)
		
		if not (prect == 1.0 and rect == 1.0):
			conv.append(int*2)
			precTot.append(prect)
		allTemp.append(resultsTemp)		

	results = [(sum([t[i][0] for t in allTemp])/iterations, sum([t[i][1] for t in allTemp])/iterations) for i in range(int)]
	
	# Print results
	convfin = sum(conv)/float(len(conv))
	print "conv: {}, {}".format(conv, convfin)
	precProm = sum(precTot)/float(len(precTot))
	print precProm

	return [results, convfin]

# parameters: 
# p0: create updates 
# p1: cancel updates 
# p2: release updates
# p3: punish create original
# p4: punish cancels punishment
# p5: punish cancels policy
# p6: punish create punishment/policy
# ep: cleaning parameter 
# epp: maxalg epsilon


#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#* Main *#**#**#**#**#**#**#**#**#**#**#
#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#**#

def main(argv):

	iterations=10
	ints=1000
	voc=12
	type='basic'
	times=1
	write=0
	experiment = 2
	global verbose
	verbose = 0

	try:
		opts, args = getopt.getopt(argv,"e:t:i:r:v:b:f:w:",["experiment=","type=","interactions=","repetitions=","voc=","verbose=","frequency=","write="])
	except getopt.GetoptError:
		print '-e experiment : 1, 2 \n -t type for exp2 : basic,create, release, punish, frequency, or policy  \n -v vocabulary size \n -r number of repetitions \n -i number of interactions, \n -b verbosity, \n -w write option, \n -f frequency (only for exp2, type frequency) '
		sys.exit(2)

	options = [p[0] for p in opts]
	# if not ('-e' in options or '--experiment' in options):
	# 	print 'experiment argument is mandatory'
	# 	sys.exit(2)

	for opt, arg in opts:
		if opt == '-h':
			print '-e experiment : 1, 2 \n -t type for exp2 : basic,create, release, punish, frequency, or policy  \n -v vocabulary size \n -r number of repetitions \n -i number of interactions, \n -b verbosity, \n -w write option, \n -t frequency (only for exp2, type frequency) '
			sys.exit()
		if arg:
			if opt in ("-e", "--experiment"):
				experiment = int(arg)
				if not experiment in [1,2]:
					print "Experiment must be 1 or 2"
					sys.exit(2)	
				if experiment==1 and ('-t' in options or '--type' in options):
					print "type argument only allowed for experiment 2"
					sys.exit(2)	
				if experiment==1 and ('-f' in options or '--frequency' in options):
					print "frequency argument only allowed for experiment 2"
					sys.exit(2)	

			if opt in ("-t", "--type"):
				type = arg
				if not type in ['basic','create','release','punish','frequency','policy']:
					print "Type must be basic, create, release, punish, frequency, or policy"
					sys.exit(2)				
			if opt in ("-i", "--interactions"):
				ints = int(arg)
			if opt in ("-v", "--vocabulary"):
				voc = int(arg)
				if voc>25:
					print "Vocabulary size must be lower than 25"
					sys.exit(2)				
			
			if opt in ("-r", "--repetitions"):
				iterations = int(arg)
			if opt in ("-b", "--verbosity"):
				verbose = int(arg)
			if opt in ("-f", "--frequency"):
				times = int(arg)
			if opt in ("-w", "--write"):
				write = int(arg)

	# types = ['basic', 'punish', 'policy']
	types = ['policy']
	for type in types:
		print type
		name = type
		if experiment==1:
			if not [t for t in opts if t[0] in ("-i", "--interactions")]:
				ints = 200
			res = experiment1(voc, iterations, iterations, ints)

		else:
			res = experiment2(iterations, ints, voc, type, times)
			
			if write: 
				name = str(voc)+'-'+type+'-'+str(times)

				with open('results-'+name, 'w+') as f:
					f.write(json.dumps(res[0]))
					f.close()
	

if __name__ == "__main__":
	main(sys.argv[1:])
