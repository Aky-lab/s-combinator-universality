"""One-occurrence S contraction and explicit deterministic strategies."""
from dataclasses import dataclass
from typing import Iterator

from .terms import App, S, Term, nodes

Path = tuple[int, ...]
STRATEGIES = ("normal", "applicative", "head")


def root_arguments(term: Term):
    if (isinstance(term, App) and isinstance(term.left, App)
            and isinstance(term.left.left, App) and term.left.left.left == S):
        return term.left.left.right, term.left.right, term.right
    return None


def redex_paths(term: Term) -> Iterator[Path]:
    """Redex occurrences in root-left-right preorder."""
    stack = [(term, ())]
    while stack:
        node, path = stack.pop()
        if root_arguments(node) is not None:
            yield path
        if isinstance(node, App):
            stack.extend([(node.right, path + (1,)), (node.left, path + (0,))])


def at(term: Term, path: Path) -> Term:
    for direction in path:
        if type(direction) is not int or direction not in (0, 1) or not isinstance(term, App):
            raise ValueError("invalid occurrence path")
        term = term.left if direction == 0 else term.right
    return term


def contract_at(term: Term, path: Path) -> Term:
    """Rewrite exactly one occurrence, even when immutable nodes are shared."""
    context = []
    focus = term
    for direction in path:
        if type(direction) is not int or direction not in (0, 1) or not isinstance(focus, App):
            raise ValueError("invalid occurrence path")
        context.append((focus, direction))
        focus = focus.left if direction == 0 else focus.right
    arguments = root_arguments(focus)
    if arguments is None:
        raise ValueError("selected occurrence is not an S redex")
    x, y, z = arguments
    result = App(App(x, z), App(y, z))
    for parent, direction in reversed(context):
        result = App(result, parent.right) if direction == 0 else App(parent.left, result)
    return result


def select_path(term: Term, strategy: str = "normal") -> Path | None:
    if strategy not in STRATEGIES:
        raise ValueError(f"unknown strategy: {strategy}")
    if strategy == "normal":
        return next(redex_paths(term), None)
    if strategy == "head":
        path = ()
        while isinstance(term, App):
            if root_arguments(term) is not None:
                return path
            term = term.left
            path += (0,)
        return None
    stack = [(term, (), False)]
    while stack:
        node, path, visited = stack.pop()
        if not isinstance(node, App):
            continue
        if visited:
            if root_arguments(node) is not None:
                return path
        else:
            stack.extend([(node, path, True), (node.right, path + (1,), False),
                          (node.left, path + (0,), False)])
    return None


@dataclass(frozen=True)
class Reduction:
    initial: Term
    final: Term
    strategy: str
    paths: tuple[Path, ...]
    status: str
    max_steps: int
    max_nodes: int


def reduce(term: Term, strategy: str = "normal", max_steps: int = 1000,
           max_nodes: int = 100000) -> Reduction:
    """Bounded reduction. Limits are inclusive and never certify divergence."""
    if strategy not in STRATEGIES:
        raise ValueError(f"unknown strategy: {strategy}")
    if type(max_steps) is not int or max_steps < 0:
        raise ValueError("max_steps must be a nonnegative integer")
    if type(max_nodes) is not int or max_nodes < 1:
        raise ValueError("max_nodes must be a positive integer")
    initial = term
    paths = []
    while True:
        if nodes(term) > max_nodes:
            status = "node_limit"
            break
        path = select_path(term, strategy)
        if path is None:
            status = "normal_form" if next(redex_paths(term), None) is None else "head_normal_form"
            break
        if len(paths) == max_steps:
            status = "step_limit"
            break
        # Exactly |z|-1 leaves are added. Reject before constructing the next term.
        x, y, z = root_arguments(at(term, path))
        if nodes(term) + nodes(z) - 1 > max_nodes:
            status = "node_limit"
            break
        term = contract_at(term, path)
        paths.append(path)
    return Reduction(initial, term, strategy, tuple(paths), status, max_steps, max_nodes)
