#pragma once

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <tuple>
#include <vector>

namespace {
struct SimpleRootedDigraphHash;

// A rooted simple directed graph.
//
// The root node is the first node, and there are no edges to that node.
class SimpleRootedDigraph {
public:
  friend struct SimpleRootedDigraphHash;

  // The out-degrees are listed as a closed range with INT_MAX meaning infinity.
  // So an edge with 2 edges out is [2, 2] while an edge with 2 or more is
  // [2, INT_MAX] and an edge with zero through five is [0, 5].
  explicit SimpleRootedDigraph(
      std::vector<std::tuple<uint8_t, uint8_t>> &out_degree_)
      : out_degree_(out_degree_) {
    const int size = out_degree_.size();
    for (auto [minlen, maxlen] : out_degree_) {
      assert(minlen <= maxlen);
      assert(minlen <= size);
      if (maxlen > size) {
        maxlen = size;
      }
      adjacency_list.emplace_back(std::vector<uint8_t>());
      if (maxlen < minlen * 2) {
        adjacency_list.back().reserve(maxlen);
      } else {
        adjacency_list.back().reserve(minlen);
      }
    }
    assert(out_degree_.size() == adjacency_list.size());
  }

  ~SimpleRootedDigraph() = default;
  SimpleRootedDigraph(const SimpleRootedDigraph &) = default;
  SimpleRootedDigraph(SimpleRootedDigraph &&) noexcept = default;
  SimpleRootedDigraph &operator=(const SimpleRootedDigraph &other) {
    // assert that out_degree_ == other.out_degree_.
    adjacency_list = other.adjacency_list;
    return *this;
  }

  bool operator==(const SimpleRootedDigraph &other) const {
    assert(adjacency_list.size() == other.adjacency_list.size());
    for (int i = 0, e = adjacency_list.size(); i != e; ++i) {
      if (adjacency_list[i].size() < other.adjacency_list[i].size())
        return false;
      // Note: we use an O(n^2) algorithm here because it's faster on small
      // graphs. The alternative is to sort adjacency_list[i] and
      // other.adjacency_list[i] O(n log n) and use linear time comparison.
      for (auto lhs : adjacency_list[i]) {
        if (std::find(other.adjacency_list[i].begin(),
                      other.adjacency_list[i].end(),
                      lhs) == other.adjacency_list[i].end())
          return false;
      }
      /*
      // untested O(n log n) implementation:
      auto lhs = adjacency_list[i];
      auto rhs = other.adjacency_list[i];
      std::sort(lhs.begin(), lhs.end());
      std::sort(rhs.begin(), rhs.end());
      if (lhs != rhs)
        return false;
      */
    }
    return true;
  }

  bool operator!=(const SimpleRootedDigraph &other) const {
    return !this->operator==(other);
  }

  void add_edge(uint8_t from, uint8_t to) {
    assert(to != 0);
    assert(edge(from, to) == false);
    assert(adjacency_list[from].size() < std::get<1>(out_degree_[from]));
    adjacency_list[from].push_back(to);
  }

  bool edge(uint8_t from, uint8_t to) const {
    assert(from != to);
    assert(from < adjacency_list.size());
    assert(to < adjacency_list.size());
    return std::find(adjacency_list[from].begin(), adjacency_list[from].end(),
                     to) != adjacency_list[from].end();
  }

  uint8_t out_degree(uint8_t node) const {
    assert(node < adjacency_list.size());
    return adjacency_list[node].size();
  }

  const std::tuple<uint8_t, uint8_t> &out_degree_spec(uint8_t node) const {
    assert(node < out_degree_.size());
    return out_degree_[node];
  }

  bool all_reachable() const {
    // "visited" indicates either we've added its adjancencies or we've added
    // it to the node_stack.
    std::vector<bool> visited(adjacency_list.size(), false);
    visited[0] = true;
    std::vector<int> node_stack;
    node_stack.emplace_back(0);
    do {
      auto node = node_stack.back();
      node_stack.pop_back();

      for (int adjacent : adjacency_list[node]) {
        if (!visited[adjacent]) {
          visited[adjacent] = true;
          node_stack.emplace_back(adjacent);
        }
      }
    } while (!node_stack.empty());

    for (bool b : visited) {
      if (!b)
        return false;
    }
    return true;
  }

  // Check whether this graph contains a cycle. This data structure is never
  // supposed to contain cycles, so this should only be used to verify that
  // assertion. If you want to know whether there's a cycle outside debugging,
  // the answer is 'no'.
  bool is_acyclic() const {
#ifndef NDEBUG
    std::vector<bool> visited(adjacency_list.size(), false);
    std::vector<std::pair<int, int>> node_stack;
    node_stack.reserve(adjacency_list.size());
    node_stack.emplace_back(0, 1);
    do {
      auto [node, adjacency_index] = node_stack.back();
      node_stack.pop_back();
      visited[node] = true;

      int out_degree_count = out_degree(node);
      for (int i = adjacency_index; i < out_degree_count; ++i) {
        int a = adjacency_list[node][i];
        assert(edge(node, a));
        if (visited[a]) {
          // Cycle found.
          return false;
        }
        // Save our current state in our current node.
        if (i != out_degree_count - 1)
          node_stack.emplace_back(node, i + 1);
        // Depth first visit, switch to child node now.
        node_stack.emplace_back(a, 1);
        break;
      }
    } while (!node_stack.empty());
#endif
    return true;
  }

  bool has_path(uint8_t from, uint8_t to) const {
    assert(to != 0);
    assert(from < adjacency_list.size());
    assert(to < adjacency_list.size());
    std::vector<bool> visited(adjacency_list.size(), false);
    std::vector<int> worklist;
    worklist.reserve(adjacency_list.size());
    worklist.emplace_back(from);
    do {
      int node = worklist.back();
      worklist.pop_back();
      for (int adjacency : adjacency_list[node]) {
        if (adjacency == to)
          return true;
        if (visited[adjacency])
          continue;
        worklist.push_back(adjacency);
        visited[adjacency] = true;
      }
    } while (!worklist.empty());
    return false;
  }

  unsigned size() const {
    return adjacency_list.size();
  }

  const std::vector<std::vector<uint8_t>> &graph() const {
    return adjacency_list;
  }

  void dump() const {
    for (int i = 0, e = adjacency_list.size(); i < e; ++i) {
      for (auto a : adjacency_list[i])
        printf("n%d -> n%d\n", i, a);
    }
    printf("\n");
  }

private:
  //const std::vector<std::tuple<uint8_t, uint8_t>> out_degree_;
  const std::vector<std::tuple<uint8_t, uint8_t>> &out_degree_;

  std::vector<std::vector<uint8_t>> adjacency_list;
};

struct SimpleRootedDigraphHash {
  uint32_t operator()(SimpleRootedDigraph const &g) const noexcept {
    uint32_t hash = 0;
    for (int x = 0, xe = g.adjacency_list.size(); x != xe; ++x) {
      hash = hash_combine(lowbias32(x), hash);
      for (const auto &y : g.adjacency_list[x]) {
        hash = hash_combine(lowbias32(y), hash);
      }
    }
    return hash;
  }

private:
  // https://github.com/skeeto/hash-prospector
  static uint32_t lowbias32(uint32_t x) {
    x ^= x >> 16;
    x *= UINT32_C(0x7feb352d);
    x ^= x >> 15;
    x *= UINT32_C(0x846ca68b);
    x ^= x >> 16;
    return x;
  }

  // https://stackoverflow.com/questions/2590677/how-do-i-combine-hash-values-in-c0x
  static uint32_t hash_combine(uint32_t x, uint32_t y) {
    return y + 0x9e3779b9 + (x << 6) + (x >> 2);
  }
};

} // namespace
