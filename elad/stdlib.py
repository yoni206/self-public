# This file contains the type signatures for various library functions.

from typing import List, Set, Dict


""""""
def len[T](l: List[T]) -> int: ...


def len[T](s: Set[T]) -> int: ...

def range(i1: int, i2: int, i3: int) -> List[int]: ...

def range(i1: int, i2: int) -> List[int]: ...

def range(i1: int) -> List[int]: ...

def str[T](t: T) -> str: ...

def isinstance[T1, T2](t1: T1, t2: T2) -> bool: ...


"""sys"""


def exit(p: int): ...


"""json"""

def dump[T1, T2](d: Dict[T1, T2]) -> str: ...