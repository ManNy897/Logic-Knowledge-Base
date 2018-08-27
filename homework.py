import copy
import time

class KB:

	 def __init__(self, sentence=None):
		self.clauses = {}
		if sentence:
			self.tell(sentence)

	 def tell(self, sentence):
		#add sentence to kb
		#index on each predicate of sentence
		"""if sentence.op == '|':
			for predicate in sentence.args:
				add_to_KB(self, predicate, sentence)
		else add_to_KB(self, sentence, sentence)"""
		#print(sentence.args[0].args[0].args[0].op)
		if sentence not in self.clauses:
			self.clauses[sentence] = sentence

	 def ask_if_true(self, query):
		#ask if query is true given kb
		#return entails(self, self.clauses.copy(), query)
		return entails(self, copy.deepcopy(self.clauses), query)

	 def print_KB(self):
		for clause in self.clauses.values():
			print(print_helper(clause))
		print("###################################")


class Expr:
	def __init__(self, op, args):
		self.op = op
		self.args = args

	def __hash__(self):
		return hash(self.op) ^ hash(tuple(self.args))
	def __eq__(self, other):
		return self.op == other.op and self.args == other.args

def print_helper(expr):
	if not expr.args:
		return expr.op + ','
	elif expr.op == '|':
		s = ''
		for arg in expr.args:
			s = s + print_helper(arg) + '|'
		return s[:-1]
	elif expr.op == '~':
		s = '~' + print_helper(expr.args[0])
		return s
	else:
		s = expr.op + '('
		for arg in expr.args:
			s = s + print_helper(arg)
		s = s[:-1] + ')'
		return s

def standardize_apart(expr, cnt):
	if is_variable(expr):
		if expr.op[-1].isdigit():
			expr.op = expr.op[0] + str(int(expr.op[-1]) + cnt)
		else:
			expr.op = expr.op + str(cnt)
	else:
		for arg in expr.args:
			standardize_apart(arg, cnt)

def standardize_together(expr):
	if is_variable(expr):
		expr.op = ''.join([i for i in expr.op if not i.isdigit()])
	else:
		for arg in expr.args:
			standardize_together(arg)

def expr(line):
	#make Expr object from string
	#if it contains '|' make Expr with op = '|''
		#split on '|'
		#for each part 
		#if starts with '~'
			#make Expr with op = '~'
		#make Expr with op=
	#else make predicate
	if '|' in line:
		return make_conjunction(line)
	else:
		return make_predicate(line)

def make_conjunction(line):
	conjucts = line.replace(' ', '').split('|')
	conjuct_expressions = []
	for conjuct in conjucts:
		conjuct_expressions.append(make_predicate(conjuct))
	return Expr(op = '|', args = conjuct_expressions)

def make_predicate(line):
	is_negation = '~' in line
	args_expressions = []
	temp = line.replace('~', '')
	open_paren_index = temp.index('(')
	close_paren_index = temp.index(')')
	predicate_name = temp[0:open_paren_index]
	#args = temp[split_index+1:len(temp)-1].split(',')
	args = temp[open_paren_index+1:close_paren_index].split(',')
	#args = temp[split:len(temp)-1].split(',')
	for arg in args:
		args_expressions.append(make_arg(arg))
	if is_negation:
		return Expr(op = '~', args = [Expr(op = predicate_name, args = args_expressions)])
	return Expr(op = predicate_name, args = args_expressions)

def make_arg(argument):
	return Expr(op = argument, args = [])
	
#for each line read
 #if line is num record
 #else build Expr object on string

def entails(test, clauses, alpha):
	#copy KB
	#add negation of alpha
	#run resolution
	KB_temp = KB()
	KB_temp.clauses = clauses
	#for k in test.clauses.keys():
	#	test.clauses[k].args = []
	print('*************************************')
	print('QUERY:')
	print(print_helper(alpha))
	print('KB')
	KB_temp.print_KB()
	if alpha.op == '~':
		KB_temp.tell(alpha.args[0])
	else:
		KB_temp.tell(Expr(op='~', args=[alpha]))
	return resolution(test,KB_temp)


def resolution(test,KB1):
	timeout = time.time() + 60*5
	new = {}
	standardize_apart_counter = 0
	while True:
		if time.time() > timeout:
			return False
		standardize_apart_counter += 1
		print('STEP OF RESOLUTION:')
		KB1.print_KB()
		values = list(KB1.clauses.values())
		pairs = [(values[i], values[j]) for i in range(0,len(values)) for j in range(i+1,len(values))]
		#print('Length of pairs: ' + str(len(pairs)))
		for ci, cj in pairs:
			if time.time() > timeout:
				return False
			#print('KB TEST before apart')
			#KB1.print_KB()
			standardize_apart(cj, standardize_apart_counter)
			#print('KB TEST after apart')
			#KB1.print_KB()
			resolvents = resolve(test,ci, cj, KB1)
			#print('KB TEST')
			#KB1.print_KB()
			if None in resolvents:
				print('EMPTY CLAUSE DISCOVERED... RETURNING TRUE')
				return True
			new.update(resolvents)
			standardize_together(cj)
			#print("PRINTING NEW")
			#for k,v in new.iteritems():
			#	print(print_helper(v))

		#print('PRINTING NEW ITEMS')
		#for k,v in new.iteritems():
		#	print(print_helper(v))
		if set(new).issubset(set(KB1.clauses)):
			print('RESOLUTION FAILED... RETURNING FALSE')
			return False
		KB1.clauses.update(new)


def resolve(test,c1, c2, KB1):
	new_clauses = {}
	for di in disjuncts(c1):
		for dj in disjuncts(c2):
			if negated_predicates(di, dj):
				#print('NEGATED PREDICATES')
				#print(print_helper(di) + '  ' + print_helper(dj))
				#print(print_helper(c1) + '----' + print_helper(c2))
				if di.op == '~':
					theta = unify(di.args[0].args, dj.args)
				else:
					theta = unify(di.args, dj.args[0].args)
				#for k,v in theta.iteritems():
				#	print('{' + print_helper(k) + ':' + print_helper(v) + '}')
				if not theta is None:
					#print('UNIFICATION EXISTS')
					#print('THETA')
					#for k,v in theta.iteritems():
					#	print('{' + print_helper(k) + ' : ' + print_helper(v) + '}')

					'''print('DISJUNCTS OF C1')
					s = ''
					for d in disjuncts(c1):
						s = s + print_helper(d) + '|'
					print(s)
					print('DISJUNCTS OF C2')
					s = ''
					for d in disjuncts(c2):
						s = s + print_helper(d) + '|'
					print(s)'''
					#print("DISJUNCTS AFTER REMOVE")
					d1_new = copy.deepcopy(disjuncts(c1))
					d2_new = copy.deepcopy(disjuncts(c2))
					d1_new.remove(di)
					d2_new.remove(dj)
					#print('TEMP KB AFTER REMOVE')
					#KB1.print_KB()
					#print(print_helper(Expr(op = '|', args = d1_new)) + '----' + print_helper(Expr(op = '|', args = d2_new)))
					new_clause = perform_unification(test,d1_new, d2_new, theta)
					if new_clause is None:
						print('EMPTY CLAUSE FOUND')
						print(print_helper(c1) + '------' + print_helper(c2))
					if not new_clause is None:
						standardize_together(new_clause)
						#print('NEW CLAUSE')
						#print(print_helper(new_clause))
					new_clauses[new_clause] = new_clause
				#print('@@@@@@@@@@@@@@@@@')
	#print('NEW CLAUSES')
	#print(new_clauses)
	'''if len(new_clauses) > 0:
		for k,v in new_clauses.iteritems():
			if not k is None:
				print('{' + print_helper(k) + ':' + print_helper(v) + '}')'''

	return new_clauses

def perform_unification(test,c1, c2, theta):
	#look at each predicate for c1
	#if any of the args for the predicate are in theta change its value
	#do the same for c2
	#return disjunction of c1 and c2
	'''print('THETA')
	for k,v in theta.iteritems():
		print('{' + print_helper(k) + ' : ' + print_helper(v) + '}')
	for c in c1:
		print(print_helper(c))
	for c in c2:
		print(print_helper(c))'''
	if not c1 and not c2:
		'''print("EMPTY CLAUSE")
		print(str(c1) + '   ' + str(c2))'''
		return None
	c1 = update_args(c1, theta)
	c2 = update_args(c2, theta)
	c = extend(c1,c2)
	return Expr(op = '|', args = c)

def extend(c1,c2):
	c = c1
	c.extend(c2)
	return c

def update_args(clause, theta):
	clause_update = []
	for predicate in clause:
		if predicate.op == '~':
			predicate = predicate.args[0]
			args = []
			for i in range(0, len(predicate.args)):
				if predicate.args[i] in theta:
					args.append(Expr(op = theta[predicate.args[i]].op, args = []))
				else:
					args.append(Expr(op = predicate.args[i].op, args = []))
			clause_update.append(Expr(op = '~', args = [Expr(op = predicate.op, args = args)]))
		else:
			args = []
			for i in range(0, len(predicate.args)):
				if predicate.args[i] in theta:
					args.append(Expr(op = theta[predicate.args[i]].op, args = []))
				else:
					args.append(Expr(op = predicate.args[i].op, args = []))
			clause_update.append(Expr(op = predicate.op, args = args))
					#predicate.args[i] = theta[predicate.args[i]]
	'''print('UPDATED ARGS')
	for p in clause:
		print(print_helper(p))'''
	return clause_update

def negated_predicates(p1, p2):
	if p1.op == '~' and p2.op != '~' or p1.op != '~' and p2.op == '~':
		if get_predicate_name(p1) == get_predicate_name(p2):
			return True
	return False
def get_predicate_name(p):
	if p.op == '~':
		return p.args[0].op
	return p.op

def disjuncts(clause):
	if clause.op == '|':
		return clause.args
	return [clause]

def unify(expr1, expr2):
	"""if s == None:
			return None
		elif expr1.args == expr2.args && expr1.op == expr2.op:
			return s
		elif is_variable(expr1):
			unify_var(expr1, expr2, s)
		elif is_variable(expr2):
			unify_var(expr2, expr1, s)"""
	s = {}

	'''print("UNIFY:")
	p = '('
	for d in expr1:
		p = p + print_helper(d)
	p = p + ')   ('
	for d in expr2:
		p = p + print_helper(d)
	p = p + ')'
	print(p)'''

	for i in range(0, len(expr1)):
		if expr1[i].op == expr2[i].op:
			continue
		elif is_variable(expr1[i]) and not is_variable(expr2[i]):
			s = unify_var(expr1[i], expr2[i], s)
		elif is_variable(expr2[i]) and not is_variable(expr1[i]):
			s = unify_var(expr2[i], expr1[i], s)
		else:
			return None
	return s


def unify_var(x, y, s):
	#print('UNIFYING VAR:')
	#print(print_helper(x) + '  ' + print_helper(y))
	#print("UNIFYING VAR")
	if x in s:
		return s
	s2 = s.copy()
	s2[x] = y
	#print("Curr_THETA")
	#for k,v in s2.iteritems():
	#	print('{' + print_helper(k) + ':' + print_helper(v) + '}')
	return s2

def is_variable(expr1):
	return expr1.op.islower()

def read_file():
	with open("input.txt") as f:
		file = f.readlines()
	num_queries = int(file[0])
	query_list = []
	for i in range(1, 1+num_queries):
		query_list.append(file[i].strip())
	num_sentences = int(file[num_queries+1].strip())
	sentence_list = []
	for j in range(num_queries+2, num_sentences+num_queries+2):
		sentence_list.append(file[j])
	return query_list, sentence_list

def output_file(query_answers):
	with open("output.txt", 'w') as w:
		for answer in query_answers:
			w.write(str(answer).upper() + '\n')

def main():
	query_list, sentence_list = read_file()
	KB1 = KB()
	for sentence in sentence_list:
		KB1.tell(expr(sentence))
	KB1.print_KB()
	query_answers = []
	for query in query_list:
		print('ORIGINAL KB')
		KB1.print_KB()
		query_answers.append(KB1.ask_if_true(expr(query)))
	output_file(query_answers)

if __name__== "__main__":
	main()


