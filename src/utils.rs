pub(crate) fn opt_or(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), r) | (r, Some(false)) => r,
        (None, None) => None,
    }
}

pub(crate) fn opt_and(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), r) | (r, Some(true)) => r,
        (None, None) => None,
    }
}
