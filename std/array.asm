/// This is a built-in function taking an array argument and returning
/// the length of the array.
/// This symbol is not an empty array, the actual semantics are overridden.
let<T> len: T[] -> int = [];

/// Evaluates to the array [f(0), f(1), ..., f(length - 1)].
let<T> new: int, (int -> T) -> T[] = |length, f| std::utils::fold(length, f, [], |acc, e| (acc + [e]));

/// Evaluates to the array [f(arr[0]), f(arr[1]), ..., f(arr[len(arr) - 1])].
let<T1, T2> map: T1[], (T1 -> T2) -> T2[] = |arr, f| new(len(arr), |i| f(arr[i]));

/// Evaluates to the array [f(0, arr[0]), f(1, arr[1]), ..., f(len(arr) - 1, arr[len(arr) - 1])].
let<T1, T2> map_enumerated: T1[], (int, T1 -> T2) -> T2[] = |arr, f| new(len(arr), |i| f(i, arr[i]));

/// Computes folder(...folder(folder(initial, arr[0]), arr[1]) ..., arr[len(arr) - 1])
let<T1, T2> fold: T1[], T2, (T2, T1 -> T2) -> T2 = |arr, initial, folder| std::utils::fold(len(arr), |i| arr[i], initial, folder);

/// Returns the sum of the array elements.
// TODO: Should make use of the Default or Zero trait instead of FromLiteral (then we can also
// use this function to flatten an array of arrays.
let<T: Add + FromLiteral> sum: T[] -> T = |arr| fold(arr, 0, |a, b| a + b);

/// Zips two arrays
/// TODO: Assert that lengths are equal when expressions are supported.
let<T1, T2, T3> zip: T1[], T2[], (T1, T2 -> T3) -> T3[] = |array1, array2, fn| new(len(array1), |i| fn(array1[i], array2[i]));

let find_map_enumerated = |arr, f| internal::find_map_enumerated(arr, len(arr), 0, f);
let find_map = |arr, f| find_map_enumerated(arr, |i, x| f(x));

let<T> find_index = |arr, f| internal::find_index(arr, 0, f);

mod internal {
    let find_index = |arr, i, f| if i >= std::array::len(arr) {
        Option::None
    } else {
        if f(arr[i]) {
            Option::Some(i)
        } else {
            find_index(arr, i + 1, f)
        }
    }

    let find_map_enumerated = |arr, l, i, f| if i >= l { Option::None } else {
        match f(i, arr[i]) {
            Option::Some(x) => Option::Some(x),
            Option::None => find_map_enumerated(arr, l, i + 1, f),
        }
    };
}

enum Option<T> {
    None,
    Some(T)
}

let unwrap_or_else = |x, f| match x {
    Option::None => f(),
    Option::Some(_) => x,
};


/// This is a 2-3-4-tree, which means that each node has
/// up to 3 items and a number of children that is one more
/// than the number of items.
enum BTreeNode<K> {
    Inner(K[], BTreeNode<K>[]),
    Lead(K[]),
}

enum CmpResult {
    Less,
    Equal,
    Greater,
}

let b_tree_search = |b_tree, k, cmp| match b_tree {
    BTreeNode::Inner(items, children) => match b_tree_search_in_node(items, k, cmp) {
        NodeSearchResult::InNode(i) => Option::Some(value_of_item(items[i])),
        NodeSearchResult::InChild(i) => b_tree_search(children[i], k, cmp),
    },
    BTreeNode::Leaf(items) => find_map(items, |(key, value)| match cmp(k, key) {
        CmpResult::Equal => Option::Some(value),
        _ => Option::None,
    });
};

let value_of_item = |(_, value)| value;

enum NodeSearchResult<V> {
    InNode(int),
    InChild(int),
}

let b_tree_search_in_node = |items, k, cmp| {
    let r = find_map_enumerated(items, |i, (key, _)| match cmp(k, key) {
        CmpResult::Less => Option::Some(NodeSearchResult::InChild(i)),
        CmpResult::Equal => Option::Some(NodeSearchResult::InNode(i)),
        CmpResult::Greater => Option::None,
    });
    unwrap_or_else(r, || NodeSearchResult::InChild(std::array::len(items)))
};

// TODO this does not detect if a key already exists.
let b_tree_insert = |b_tree, k, v, cmp| match b_tree {
    BTreeNode::N([i1, i2, i3], [c1, c2, c3, c4]) => {

    },
    BTreeNode::N(items, children) => {

    },
};

mod internal_insert {
    let b_tree_insert = |b_tree, k, v, cmp| match b_tree {
        BTreeNode::Leaf([v1, v2, v3]) => (Option::Some(v2), BTreeNode::Leaf(sort([v1, v3, (k, v)], cmp))),
        BTreeNode::Leaf(items) => (Option::None, BTreeNode::

        BTreeNode::Inner(items, children) => {

        },
    };
}