from sage.groups.perm_gps.permgroup import PermutationGroup
from sage.combinat.set_partition import SetPartition
from sage.combinat.set_partition import SetPartitions
from sage.combinat.subset import Subsets
from sage.graphs.graph import Graph
from copy import deepcopy
from sage.combinat.posets.posets import Poset
from sage.combinat.permutation import Permutations
from sage.groups.perm_gps.permgroup_named import SymmetricGroup

def ColoringGroup (pi):
    gens = [];
    
    for block in pi:
        gen = [];
        for e in block:
            gen.append((e[0], e[1]));
        gens.append(gen);
    
    return PermutationGroup(gens);

class EdgeColoring:
    def __init__ (self, G, pi = None):
        # If no pi is given, interpret G as a set partition of edges
        if pi == None:
            self._pi = [[(e[0],e[1]) for e in block] for block in G];
            self._G = Graph();
            self._group = None;
            for block in G:
                for e in block:
                    self._G.add_edge(e[0], e[1]);
        else:
            self._G = G;
            self._group = None;
            self._pi = sorted(pi, key=len);
    def plot (self):
        for i in range(0, len(self._pi)):
            block=self._pi[i];
            for edge in block:
                self._G.set_edge_label(edge[0], edge[1], i);
        return self._G.plot(color_by_label=True);
    def group (self):
        if self._group == None:
            self._group = ColoringGroup(self._pi);

        return self._group;

    def coxeter_elements (self):
        G = self.group();
        gens = G.gens();
        for pi in Permutations(gens):
            elt = G.one();
            
            for p in pi:
                elt = elt * p;
            
            yield elt;

    # Returns the poset of the absolute order (could certainly be done faster)
    def absolute_order(self):
        G = self.group();
        simples = G.gens();
        transpositions = set();

        for s in simples:
            for g in G:
                transpositions.add(g*s*(g**(-1)));

        GT = PermutationGroup(tuple(transpositions));

        C = GT.cayley_graph();

        def compute_length (g):
            return C.shortest_path_length(GT.identity(), g);

        relations = set();

        for g1 in GT:
            for g2 in GT:
                # No need to check if they are the same or already compare the other way
                if g1 != g2 and (g2,g1) not in relations:
                    # g1 < g2
                    if compute_length(g2) == compute_length(g1) + compute_length((g1**(-1))*g2):
                        relations.add((g1,g2));

        return Poset((GT, relations));

    # Returns the poset of the absolute order with transpositions as anything conjugate in the symmetric group (could certainly be done faster)
    def super_absolute_order(self):
        G = self.group();
        simples = G.gens();
        transpositions = set();

        for s in simples:
            for g in SymmetricGroup(self._G.order()):
                transpositions.add(g*s*(g**(-1)));

        GT = PermutationGroup(tuple(transpositions));

        C = GT.cayley_graph();

        def compute_length (g):
            return C.shortest_path_length(GT.identity(), g);

        relations = set();

        for g1 in GT:
            for g2 in GT:
                # No need to check if they are the same or already compare the other way
                if g1 != g2 and (g2,g1) not in relations:
                    # g1 < g2
                    if compute_length(g2) == compute_length(g1) + compute_length((g1**(-1))*g2):
                        relations.add((g1,g2));

        return Poset((GT, relations));

    # Returns a product of all the generators
    def long_product(self):
        H = self.group();
        out = H([(e[0],e[1]) for e in self._pi[0]]);

        for i in range(1, len(self._pi)):
            out = out * H([(e[0],e[1]) for e in self._pi[i]]);

        return out;
    # Check whether the graph coloring has a symmetric edge (if the graph is a tree,
    # we then know the coloring group is the full symmetric group)
    def has_symmetric_edge (self):
        T = self._G;
        pi = self._pi;
        
        edges = [];

        for i in range(0, len(pi)):
            for edge in pi[i]:
                edges.append((edge, i));
        
        def incident_edges (x):
            return [(edge, color) for (edge, color) in edges if x in edge];
        
        for ((x,y),color) in edges:
            colors = [c for (e,c) in incident_edges(x) if (e != (x,y))] + [c for (e,c) in incident_edges(y) if (e!=(x,y))];
            # incident colors are unique
            if len(colors) == len(set(colors)):
                # First, if the color is unique, we're done
                if len(pi[color]) == 1:
                    return True;
                # Range over all additional colors to remove
                for color_set in Subsets(set(range(0, len(pi))).difference(colors)):
                    removed_colors = set(list(colors) + list(color_set));
                    H = Graph();
                    for (edge, color) in edges:
                        if color not in removed_colors:
                            H.add_edge(edge);
                    components = H.connected_components_sizes();
                    if sum([1 for j in components if j % 2 == 0]) == 1:
                        return True;
        return False;


# Insert x into blocks of pi without putting it with
# any of the disallowed values with max block size k
def insert_to_blocks (pi, x, disallowed, k = None):
    out = [];
    for i in range(0, len(pi)):
        block = pi[i];
        if all([y not in block for y in disallowed]):
            nu = deepcopy(pi);
            nu[i].append(x);
            out.append(nu);
    if len(out) == 0 and (k == None or len(pi) < k):
        out.append(deepcopy(pi) + [[x]]);
    return out;

def coarsest_proper_edge_colorings (G, k = None):
    edges = [(x,y) for (x,y,z) in G.edges()];
    colorings = [[[]]];

    for edge in edges:
        (x,y) = edge;
        # Disallow adjacent edges
        disallowed = [e for e in edges if e != edge and (x in e or y in e)];
        colorings = sum([insert_to_blocks(pi, edge, disallowed, k) for pi in colorings],[]);

    return [SetPartition(pi) for pi in colorings];



# Iterates over all edge colorings of G with k colors
def EdgeColorings (G, k = None):
    yielded = set();
    if k == None:
        # First find the coarsest colorings, then any refinement of them is already proper
        for coarse_pi in coarsest_proper_edge_colorings(G):
            for pi in coarse_pi.refinements():
                if pi not in yielded:
                    yielded.add(pi);
                    yield EdgeColoring(G, pi);
    else:
        for coarse_pi in coarsest_proper_edge_colorings(G):
            for pi in coarse_pi.refinements():
                if len(pi) == k and pi not in yielded:
                    yielded.add(pi);
                    yield EdgeColoring(G, pi);