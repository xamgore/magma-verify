//! Minimal input/output borrowing adapter for the Aeneas verification model.
//! It provides the get_in/get_out operations used by the original methods.
//! This is NOT a definition of the real cipher::InOut implementation.

pub struct InOut<'a, 'b, T> {
    pub(crate) input: &'a T,
    pub(crate) output: &'b mut T,
}

impl<'a, 'b, T> InOut<'a, 'b, T> {
    pub fn get_in(&self) -> &T {
        self.input
    }

    pub fn get_out(&mut self) -> &mut T {
        self.output
    }
}
