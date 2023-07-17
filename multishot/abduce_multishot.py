import sys
import clingo
from time import time as stopwatch
from collections import defaultdict
from pathlib import Path

REPORT_LINE = "%%%%%%%%%%%%%%%%%%%%%%%"
REPORT_NODES = "% #nodes:\t{}"
REPORT_ATOMS = "% #atoms:\t{}"
REPORT_GROUNDING = "% Grounding:\t{:.3f}s"
REPORT_SOLVING = "% Solving:\t{:.3f}s"
REPORT_TOTAL = "% Total:\t{:.3f}s"
REPORT_TOTAL_S = "% Total (S): \t{:.3f}s"
REPORT_TOTAL_G = "% Total (G): \t{:.3f}s"

def recursive_labeling(node, graph, labels):
	label = labels[node]
	children = sorted(graph[node])
	if label in {'~', 'G', 'F', 'X'}:
		return '({}({}))'.format(label, recursive_labeling(children[0], graph, labels))
	elif label in {'->', '&', '|', 'U'}:
		lhs = recursive_labeling(children[0], graph, labels)
		rhs = recursive_labeling(children[1], graph, labels)
		return '({}{}{})'.format(lhs, label, rhs)
	else: # proposition
		return "({})".format(label)

def rebuild_formula(atoms):
	decode_symbols = {
		'always': 'G',
		'eventually': 'F',
		'neg': '~',
		'implies': '->',
		'and': '&',
		'or': '|',
		'next': 'X',
		'until': 'U'
	}

	graph = defaultdict(lambda: [], dict())
	label = dict()
	for atom in atoms:
		if atom.match('edge', 2):
			graph[atom.arguments[0].number].append(atom.arguments[1].number)
		if atom.match('label', 2):
			sym = atom.arguments[1].name
			lab = sym if sym not in decode_symbols else decode_symbols[sym]
			label[atom.arguments[0].number] = lab

	return recursive_labeling(1, graph, label)


class InterceptModel:
	def __init__(self):
		self.atoms = None

	def __call__(self, model):
		self.atoms = model.symbols(shown=True)
		return False

SEARCH_LP = Path(__file__).parent / 'search.lp'

if __name__ == '__main__':
	log = sys.argv[1]
	ctl = clingo.Control([])
	ctl.load(SEARCH_LP.as_posix())
	ctl.load(log)

	if '--bfs' in sys.argv:
		ctl.add("base", [], "bfs_pruning.")
		print("BFS-based pruning.")

	ctl.ground([("base", [])])

	continue_searching = True
	max_tree_size = 20
	tree_size = 1

	model = InterceptModel()

	total_time_start = stopwatch()
	total_time_ground = 0
	total_time_solve = 0
	print(REPORT_LINE)
	while continue_searching and tree_size <= max_tree_size:
		print(REPORT_NODES.format(tree_size))
		ground_time = stopwatch()
		ctl.ground([("search", [clingo.Number(tree_size)])])
		ctl.ground([("eval",   [clingo.Number(tree_size)])])
		ground_time = stopwatch() - ground_time
		total_time_ground += ground_time
		print(REPORT_GROUNDING.format(ground_time))
		symbolic_atoms = len(ctl.symbolic_atoms)
		print(REPORT_ATOMS.format(symbolic_atoms))
		
		# Release
		ctl.release_external(clingo.Function("shot", [clingo.Number(tree_size-1)]))
		ctl.cleanup()

		# Push
		ctl.assign_external(clingo.Function("shot", [clingo.Number(tree_size)]), True)
		solving_time = stopwatch()
		ans = ctl.solve(on_model=model)
		solving_time = stopwatch() - solving_time
		print(REPORT_SOLVING.format(solving_time))
		total_time_solve += solving_time

		total_time = stopwatch() - total_time_start
		print(REPORT_TOTAL.format(total_time))
		print(REPORT_TOTAL_G.format(total_time_ground))
		print(REPORT_TOTAL_S.format(total_time_solve))
		print(REPORT_LINE)

		if ans.satisfiable:
			continue_searching = False
			readable_formula = rebuild_formula(model.atoms)

			print("Result: {} {:.3f}".format(readable_formula, total_time_ground + total_time_solve))

		tree_size += 1

	if tree_size > max_tree_size:
		print("No formula below {} nodes can separate the strings.".format(max_tree_size))
