#ifndef COUNTER_HPP
#define COUNTER_HPP

/**
 * Simple counter class for generating unique IDs
 */
class Counter {
 public:
  /**
   * Initialize counter with starting value
   * @param n Initial counter value (default 0)
   */
  explicit Counter(int n = 0) : n_(n) {}

  /**
   * Increment and return the next value
   * @return The next ID
   */
  int increase() { return ++n_; }

  /**
   * Get the current counter value
   * @return Current value
   */
  int value() const { return n_; }

 private:
  int n_;
};

#endif  // COUNTER_HPP
