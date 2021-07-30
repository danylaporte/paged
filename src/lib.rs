use std::cmp::{min, Ordering};

pub trait Comparer<T> {
    fn compare(&mut self, a: &T, b: &T) -> Ordering;
}

impl<T, U> Comparer<T> for &mut U
where
    U: Comparer<T>,
{
    fn compare(&mut self, a: &T, b: &T) -> Ordering {
        (**self).compare(a, b)
    }
}

#[derive(Clone, Copy)]
/// A Fn comparer
pub struct FnComparer<C>(C);

impl<C, T> Comparer<T> for FnComparer<C>
where
    C: FnMut(&T, &T) -> Ordering,
{
    #[inline]
    fn compare(&mut self, a: &T, b: &T) -> Ordering {
        (self.0)(a, b)
    }
}

#[derive(Clone, Copy)]
// Reverse Comparer
pub struct Rev<C>(C);

impl<C, T> Comparer<T> for Rev<C>
where
    C: Comparer<T>,
{
    #[inline]
    fn compare(&mut self, a: &T, b: &T) -> Ordering {
        self.0.compare(b, a)
    }
}

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

    fn page_by<C>(self, page_size: usize, cmp: C) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item, &Self::Item) -> Ordering,
        Self: Sized,
    {
        let mut page = Page::new(page_size);
        let mut cmp = FnComparer(cmp);

        if page_size > 0 {
            self.for_each(|item| page.push(item, &mut cmp));
        }

        page.to_vec(cmp)
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
        let mut page = ScrollPage::new(page_size, FnComparer(cmp));
        self.for_each(|item| page.push(item));
        page.to_vec()
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
        F: Fn(&Self::Item) -> bool,
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
    fn scroll_full_by<C, F>(self, page_size: usize, cmp: C, filter: F) -> Vec<Self::Item>
    where
        C: Fn(&Self::Item, &Self::Item) -> Ordering,
        F: FnMut(&Self::Item) -> bool,
        Self: Sized,
    {
        let mut page = ScrollFullPage::new(page_size, FnComparer(&cmp), filter);

        self.for_each(|item| page.push(item));
        page.to_vec()
    }

    fn scroll_full_by_key<C, F, K>(self, page_size: usize, key: C, filter: F) -> Vec<Self::Item>
    where
        C: Fn(&Self::Item) -> K,
        F: FnMut(&Self::Item) -> bool,
        K: Ord,
        Self: Sized,
    {
        self.scroll_full_by(page_size, |a, b| key(a).cmp(&key(b)), filter)
    }

    fn scroll_page_index(self, page_size: usize, page: usize) -> Vec<Self::Item>
    where
        Self::Item: Ord,
        Self: Sized,
    {
        self.scroll_page_index_by(page_size, page, asc)
    }

    fn scroll_page_index_by<C>(self, page_size: usize, page: usize, cmp: C) -> Vec<Self::Item>
    where
        C: FnMut(&Self::Item, &Self::Item) -> Ordering,
        Self: Sized,
    {
        let mut page = ScrollPageIndex::new(page_size, page, FnComparer(cmp));
        self.for_each(|item| page.push(item));
        page.to_vec()
    }

    fn scroll_page_index_by_key<C, K>(
        self,
        page_size: usize,
        page: usize,
        key: C,
    ) -> Vec<Self::Item>
    where
        C: Fn(&Self::Item) -> K,
        K: Ord,
        Self: Sized,
    {
        self.scroll_page_index_by(page_size, page, |a, b| key(a).cmp(&key(b)))
    }
}

impl<T> PagedIterExt for T where T: Iterator {}

struct Page<T>(Vec<T>);

impl<T> Page<T> {
    fn new(size: usize) -> Self {
        Self(Vec::with_capacity(size))
    }

    fn insert<C: Comparer<T>>(&mut self, element: T, mut cmp: C) -> Option<T> {
        if self.is_at_capacity() {
            if self.0.is_empty()
                || cmp.compare(&element, &self.0[self.0.len() - 1]) != Ordering::Less
            {
                return Some(element);
            }

            let last = self.0.pop();

            let index = match self
                .0
                .binary_search_by(|probe| cmp.compare(probe, &element))
            {
                Ok(index) => index + 1,
                Err(index) => index,
            };

            self.0.insert(index, element);

            last
        } else {
            self.0.push(element);

            if self.is_at_capacity() {
                self.sort(cmp);
            }

            None
        }
    }

    fn is_at_capacity(&self) -> bool {
        self.0.capacity() == self.0.len()
    }

    pub fn push<C: Comparer<T>>(&mut self, item: T, cmp: C) {
        self.insert(item, cmp);
    }

    fn sort<C: Comparer<T>>(&mut self, mut cmp: C) {
        self.0.sort_unstable_by(|a, b| cmp.compare(a, b));
    }

    pub fn to_vec<C: Comparer<T>>(mut self, cmp: C) -> Vec<T> {
        if !self.is_at_capacity() {
            self.sort(cmp);
        }

        self.0
    }
}

pub struct ScrollFullPage<C, F, T> {
    accepted: Page<T>,
    cmp: C,
    filter: F,
    page_size: usize,
    rejected: Page<T>,
}

impl<C, F, T> ScrollFullPage<C, F, T>
where
    C: Comparer<T> + Copy,
    F: FnMut(&T) -> bool,
{
    pub fn new(page_size: usize, cmp: C, filter: F) -> Self {
        Self {
            accepted: Page::new(page_size),
            cmp,
            filter,
            page_size,
            rejected: Page::new(page_size),
        }
    }

    pub fn push(&mut self, item: T) {
        if self.page_size > 0 {
            if (self.filter)(&item) {
                self.accepted.push(item, Rev(&mut self.cmp));
            } else {
                self.rejected.push(item, &mut self.cmp);
            }
        }
    }

    pub fn to_vec(mut self) -> Vec<T> {
        if self.page_size > 0 {
            let mut accepted = self.accepted.to_vec(Rev(&mut self.cmp));
            accepted.reverse();

            if accepted.len() < self.page_size {
                let mut rejected = self.rejected.to_vec(&mut self.cmp);
                rejected.reverse();

                while let Some(rejected) = rejected.pop() {
                    accepted.push(rejected);

                    if accepted.len() == self.page_size {
                        break;
                    }
                }
            }

            accepted
        } else {
            Vec::new()
        }
    }
}

pub struct ScrollPageIndex<C, T> {
    cmp: C,
    page: Page<T>,
    first: usize,
}

impl<C, T> ScrollPageIndex<C, T>
where
    C: Comparer<T>,
{
    pub fn new(page_size: usize, page: usize, cmp: C) -> Self {
        let first = page_size * page;
        Self {
            cmp,
            first,
            page: Page::new(first + page_size),
        }
    }

    pub fn push(&mut self, item: T) {
        self.page.push(item, &mut self.cmp);
    }

    pub fn to_vec(mut self) -> Vec<T> {
        let mut vec = self.page.to_vec(&mut self.cmp);
        let v = min(self.first, vec.len());
        vec.drain(..v);
        vec
    }
}

pub struct ScrollPage<C, T> {
    cmp: Rev<C>,
    page: Page<T>,
}

impl<C, T> ScrollPage<C, T>
where
    C: Comparer<T>,
{
    pub fn new(page_size: usize, cmp: C) -> Self {
        Self {
            cmp: Rev(cmp),
            page: Page::new(page_size),
        }
    }

    pub fn push(&mut self, item: T) {
        self.page.push(item, &mut self.cmp);
    }

    pub fn to_vec(mut self) -> Vec<T> {
        let mut vec = self.page.to_vec(&mut self.cmp);
        vec.reverse();
        vec
    }
}

/// An ascending comparer function.
pub fn asc<T: Ord>(a: &T, b: &T) -> Ordering {
    a.cmp(&b)
}

/// Creates a comparer function based on a key function.
pub fn key_cmp<'a, F, K, T>(mut key: F) -> impl FnMut(&T, &T) -> Ordering + 'a
where
    F: FnMut(&T) -> K + 'a,
    K: Ord,
{
    move |a, b| key(a).cmp(&key(b))
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

#[test]
fn test_scroll_page_index() {
    let actual = (0..10).rev().scroll_page_index(3, 0);
    assert_eq!(actual, vec![0, 1, 2]);

    let actual = (0..10).rev().scroll_page_index(3, 1);
    assert_eq!(actual, vec![3, 4, 5]);

    let actual = (0..10).scroll_page_index(3, 2);
    assert_eq!(actual, vec![6, 7, 8]);

    let actual = (0..10).scroll_page_index_by(3, 0, |a, b| b.cmp(&a));
    assert_eq!(actual, vec![9, 8, 7]);

    let actual = (0..10).scroll_page_index(0, 0);
    assert_eq!(actual, vec![]);

    let actual = (0..10).scroll_page_index(1, 10);
    assert_eq!(actual, vec![]);
}
