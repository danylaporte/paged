use std::cmp::Ordering;

pub trait PagedIterExt: Iterator {
    /// Retains items that fit the page according to the sort.
    ///
    /// # Example
    ///
    /// ```
    /// use paged::PagedIterExt;
    ///
    /// let actual = (0..10).into_iter().page(4);
    /// assert_eq!(actual, vec![0, 1, 2, 3]);
    /// ```
    fn page(self, page_size: usize) -> Vec<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.page_by(page_size, asc)
    }

    fn page_by<C>(self, page_size: usize, mut cmp: C) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item, &Self::Item) -> Ordering,
        Self: Sized,
    {
        let mut page = Page::new(page_size);

        if page_size > 0 {
            for item in self {
                page.insert_sorted_by(item, &mut cmp);
            }
        }

        page.into_sorted_vec_by(&mut cmp)
    }

    fn page_by_key<C, K>(self, page_size: usize, key: C) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item) -> K,
        K: Ord,
        Self: Sized,
    {
        self.page_by(page_size, key_cmp(key))
    }

    fn scroll(self, page_size: usize) -> Vec<Self::Item>
    where
        Self: Sized,
        Self::Item: Ord,
    {
        self.scroll_by(page_size, asc)
    }

    /// Fill a page with filtered items.
    ///
    /// # Usage for scroll
    ///
    /// A standard usage of this method is to use it for scrolling.
    ///
    /// ```
    /// use paged::PagedIterExt;
    ///
    /// let last_shown_item = 2;
    /// let page_size = 5;
    ///
    /// let view = (0..10)
    ///     .into_iter()
    ///     .filter(|i| *i < last_shown_item)
    ///     .scroll_by(page_size, |a, b| a.cmp(b));
    ///
    /// // since the page size can contains more items, we include the rejected items.
    /// assert_eq!(view, vec![0, 1]);
    /// ```

    fn scroll_by<C>(self, page_size: usize, cmp: C) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item, &Self::Item) -> Ordering,
        Self: Sized,
    {
        let mut vec = self.page_by(page_size, rev_cmp(cmp));
        vec.reverse();
        vec
    }

    fn scroll_by_key<C, K>(self, page_size: usize, key: C) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item) -> K,
        K: Ord,
        Self: Sized,
    {
        self.scroll_by(page_size, key_cmp(key))
    }

    /// Fill a page with prefered items.
    /// If there is still room for items after the iterator has completed, fill with not prefered items.
    ///
    /// # example
    ///
    /// ```
    /// use paged::PagedIterExt;
    ///
    /// // case where there is more room for items that don't fit the prefered predicate.
    /// let actual = (0..10).into_iter().scroll_full(5, |i| *i < 2);
    /// assert_eq!(actual, vec![0, 1, 2, 3, 4]);
    ///
    /// // case where there is no more room for items, only prefered items fit.
    /// let actual = (0..10).into_iter().scroll_full(3, |i| *i < 5);
    /// assert_eq!(actual, vec![2, 3, 4]);
    /// ```
    fn scroll_full<F>(self, page_size: usize, filter: F) -> Vec<Self::Item>
    where
        F: FnMut(&Self::Item) -> bool,
        Self: Sized,
        Self::Item: Ord,
    {
        self.scroll_full_by(page_size, asc, filter)
    }

    /// Fill a page with filtered items and complete the page (if there is still some place) with
    /// rejected items.
    ///
    /// # Usage for scroll
    ///
    /// A standard usage of this method is to use it for scrolling. When scrolling the filter is used
    /// to include items based on the position of the items. Items that are previously shown are
    /// rejected by the filter.
    ///
    /// ```
    /// use paged::PagedIterExt;
    ///
    /// let last_shown_item = 2;
    /// let page_size = 5;
    ///
    /// let view = (0..10)
    ///     .into_iter()
    ///     .scroll_full_by(page_size, |a, b| a.cmp(b), |i| *i < last_shown_item);
    ///
    /// // since the page size can contains more items, we include the rejected items.
    /// assert_eq!(view, vec![0, 1, 2, 3, 4]);
    /// ```
    fn scroll_full_by<C, F>(self, page_size: usize, mut cmp: C, mut filter: F) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item, &Self::Item) -> Ordering,
        F: FnMut(&Self::Item) -> bool,
        Self: Sized,
    {
        let mut accepted = Page::new(page_size);
        let mut rejected = Page::new(page_size);

        if page_size > 0 {
            for item in self {
                if filter(&item) {
                    accepted.insert_sorted_by(item, rev_cmp(&mut cmp));
                } else {
                    rejected.insert_sorted_by(item, &mut cmp);
                }
            }

            let mut accepted = accepted.into_sorted_vec_by(rev_cmp(&mut cmp));
            accepted.reverse();

            if accepted.len() < page_size {
                let mut rejected = rejected.into_sorted_vec_by(&mut cmp);
                rejected.reverse();

                while let Some(rejected) = rejected.pop() {
                    accepted.push(rejected);

                    if accepted.len() == page_size {
                        break;
                    }
                }
            }

            accepted
        } else {
            Vec::new()
        }
    }

    fn scroll_full_by_key<C, F, K>(self, page_size: usize, key: C, filter: F) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item) -> K,
        F: FnMut(&Self::Item) -> bool,
        K: Ord,
        Self: Sized,
    {
        self.scroll_full_by(page_size, key_cmp(key), filter)
    }
}

impl<T> PagedIterExt for T where T: Iterator {}

struct Page<T>(Vec<T>);

impl<T> Page<T> {
    fn new(size: usize) -> Self {
        Self(Vec::with_capacity(size))
    }

    fn insert_sorted_by<C>(&mut self, element: T, mut compare: C) -> Option<T>
    where
        C: FnMut(&T, &T) -> Ordering,
    {
        if self.is_at_capacity() {
            if self.0.is_empty() || compare(&element, &self.0[self.0.len() - 1]) != Ordering::Less {
                return Some(element);
            }

            let last = self.0.pop();

            let index = match self.0.binary_search_by(|probe| compare(probe, &element)) {
                Ok(index) => index + 1,
                Err(index) => index,
            };

            self.0.insert(index, element);

            last
        } else {
            self.0.push(element);

            if self.is_at_capacity() {
                self.0.sort_unstable_by(compare);
            }

            None
        }
    }

    fn into_sorted_vec_by<C>(mut self, compare: C) -> Vec<T>
    where
        C: FnMut(&T, &T) -> Ordering,
    {
        if !self.is_at_capacity() {
            self.0.sort_unstable_by(compare);
        }

        self.0
    }
    fn is_at_capacity(&self) -> bool {
        self.0.capacity() == self.0.len()
    }
}

/// An ascending comparer function.
pub fn asc<T: Ord>(a: &T, b: &T) -> Ordering {
    a.cmp(&b)
}

/// A descending comparer function.
pub fn desc<T: Ord>(a: &T, b: &T) -> Ordering {
    b.cmp(&a)
}

/// Creates a comparer function based on a key function.
pub fn key_cmp<'a, F, K, T>(mut key: F) -> impl FnMut(&T, &T) -> Ordering + 'a
where
    F: FnMut(&T) -> K + 'a,
    K: Ord,
{
    move |a, b| key(a).cmp(&key(b))
}

/// Reverse a comparer function.
pub fn rev_cmp<'a, F, T>(mut f: F) -> impl FnMut(&T, &T) -> Ordering + 'a
where
    F: FnMut(&T, &T) -> Ordering + 'a,
{
    move |a, b| f(b, a)
}

#[test]
fn test_filled_prefered_page() {
    let actual = (0..10).into_iter().scroll_full(5, |i| *i < 2);
    assert_eq!(actual, vec![0, 1, 2, 3, 4]);
}

#[test]
fn test_only_prefered_page() {
    let actual = (0..10).into_iter().scroll_full(3, |i| *i < 5);
    assert_eq!(actual, vec![2, 3, 4]);
}

#[test]
fn test_rev_filled_prefered_page() {
    let actual = (0..10).rev().scroll_full(5, |i| *i < 2);
    assert_eq!(actual, vec![0, 1, 2, 3, 4]);
}

#[test]
fn test_rev_only_prefered_page() {
    let actual = (0..10).rev().scroll_full(3, |i| *i < 5);
    assert_eq!(actual, vec![2, 3, 4]);
}
