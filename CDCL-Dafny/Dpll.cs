// Dafny program Dpll.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219

using System; // for Func
using System.Numerics;

namespace Dafny
{
  using System.Collections.Generic;
// set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;

  public class Set<T>
  {
    readonly ImmutableHashSet<T> setImpl;
    Set(ImmutableHashSet<T> d) {
      this.setImpl = d;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty);
    public static Set<T> FromElements(params T[] values) {
      return FromElements((IEnumerable<T>)values);
    }
    public static Set<T> FromElements(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      foreach (T t in values)
        d.Add(t);
      return new Set<T>(d.ToImmutable());
    }
    public static Set<T> FromCollection(ICollection<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      foreach (T t in values)
        d.Add(t);
      return new Set<T>(d.ToImmutable());
    }
    public int Length {
      get { return this.setImpl.Count; }
    }
    public long LongLength {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".  Each set returned is the same
    /// Set<T> object (but this Set<T> object is fresh; in particular, it is not "this").
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          yield return new Set<T>(s.ToImmutable());
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
        return this.setImpl.SetEquals(other.setImpl);
    }
    public override bool Equals(object other) {
        var otherSet = other as Set<T>;
        return otherSet != null && this.Equals(otherSet);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (t.GetHashCode()+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      foreach (var t in this.setImpl) {
        s += sep + t.ToString();
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
        return IsProperSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
        return IsSubsetOf(other);
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSupersetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSupersetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
      ImmutableHashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return this.setImpl.Contains(t);
    }
    public Set<T> Union(Set<T> other) {
        return new Set<T>(this.setImpl.Union(other.setImpl));
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl));
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl));
    }
  }
  public partial class MultiSet<T>
  {

    readonly ImmutableDictionary<T, int> dict;
    MultiSet(ImmutableDictionary<T, int> d) {
      dict = d;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty);
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values.Elements) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromSet(Set<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values.Elements) {
        d[t] = 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      foreach (var kv in dict) {
        var t = kv.Key.ToString();
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t.ToString();
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return dict.ContainsKey(t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count == 0)
        return other;
      else if (other.dict.Count == 0)
        return this;
        var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return other;
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r[t] = other.dict[t] < dict[t] ? other.dict[t] : dict[t];
        }
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return this;
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r[t] = dict[t];
        } else if (other.dict[t] < dict[t]) {
          r[t] = dict[t] - other.dict[t];
        }
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public IEnumerable<T> Elements {
      get {
        foreach (T t in dict.Keys) {
          int n;
          dict.TryGetValue(t, out n);
          for (int i = 0; i < n; i ++) {
            yield return t;
          }
        }
      }
    }
  }

  public partial class Map<U, V>
  {
    readonly ImmutableDictionary<U, V> dict;
    Map(ImmutableDictionary<U, V> d) {
      dict = d;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty);
    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d.ToImmutable());
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d.ToImmutable());
    }
    public int Length {
      get { return dict.Count; }
    }
    public long LongLength {
      get { return dict.Count; }
    }
    public bool Equals(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        V v1, v2;
        if (!dict.TryGetValue(u, out v1)) {
          return false; // this shouldn't happen
        }
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!v1.Equals(v2)) {
          return false;
        }
      }
      foreach (U u in other.dict.Keys) {
        if (!dict.ContainsKey(u)) {
          return false; // this shouldn't happen
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      foreach (var kv in dict) {
        s += sep + kv.Key.ToString() + " := " + kv.Value.ToString();
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains(U u) {
      return dict.ContainsKey(u);
    }
    public V Select(U index) {
      return dict[index];
    }
    public Map<U, V> Update(U index, V val) {
      return new Map<U, V>(dict.SetItem(index, val));
    }
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
  }
#else // !def DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  public class Set<T>
  {
    HashSet<T> set;
    Set(HashSet<T> s) {
      this.set = s;
    }
    public static Set<T> Empty {
      get {
        return new Set<T>(new HashSet<T>());
      }
    }
    public static Set<T> FromElements(params T[] values) {
      var s = new HashSet<T>();
      foreach (T t in values)
        s.Add(t);
      return new Set<T>(s);
    }
    public static Set<T> FromCollection(ICollection<T> values) {
      HashSet<T> s = new HashSet<T>();
      foreach (T t in values)
        s.Add(t);
      return new Set<T>(s);
    }
    public int Length {
      get { return this.set.Count; }
    }
    public long LongLength {
      get { return this.set.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.set;
      }
    }
    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".  Each set returned is the same
    /// Set<T> object (but this Set<T> object is fresh; in particular, it is not "this").
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list
        var elmts = new List<T>();
        elmts.AddRange(this.set);
        var n = elmts.Count;
        var which = new bool[n];
        var s = new Set<T>(new HashSet<T>());
        while (true) {
          yield return s;
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.set.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.set.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
      return this.set.Count == other.set.Count && IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var t in this.set) {
        hashCode = hashCode * (t.GetHashCode()+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      foreach (var t in this.set) {
        s += sep + t.ToString();
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.set.Count < other.set.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
      if (other.set.Count < this.set.Count)
        return false;
      foreach (T t in this.set) {
        if (!other.set.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return this.set.Contains(t);
    }
    public Set<T> Union(Set<T> other) {
      if (this.set.Count == 0)
        return other;
      else if (other.set.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.set.Count == 0)
        return this;
      else if (other.set.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.set.Count == 0)
        return this;
      else if (other.set.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.set) {
        if (!other.set.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
  }
  public class MultiSet<T>
  {
    Dictionary<T, int> dict;
    MultiSet(Dictionary<T, int> d) {
      dict = d;
    }
    public static MultiSet<T> Empty {
      get {
        return new MultiSet<T>(new Dictionary<T, int>(0));
      }
    }
    public static MultiSet<T> FromElements(params T[] values) {
      Dictionary<T, int> d = new Dictionary<T, int>(values.Length);
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values.Elements) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values.Elements) {
        d[t] = 1;
      }
      return new MultiSet<T>(d);
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      foreach (var kv in dict) {
        var t = kv.Key.ToString();
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t.ToString();
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return dict.ContainsKey(t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count == 0)
        return other;
      else if (other.dict.Count == 0)
        return this;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return other;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return this;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r);
    }
    public IEnumerable<T> Elements {
      get {
        List<T> l = new List<T>();
        foreach (T t in dict.Keys) {
          int n;
          dict.TryGetValue(t, out n);
          for (int i = 0; i < n; i ++) {
            l.Add(t);
          }
        }
        return l;
      }
    }
  }

  public class Map<U, V>
  {
    Dictionary<U, V> dict;
    Map(Dictionary<U, V> d) {
      dict = d;
    }
    public static Map<U, V> Empty {
      get {
        return new Map<U, V>(new Dictionary<U,V>());
      }
    }
    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
      Dictionary<U, V> d = new Dictionary<U, V>(values.Length);
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
      Dictionary<U, V> d = new Dictionary<U, V>(values.Count);
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d);
    }
    public int Length {
      get { return dict.Count; }
    }
    public long LongLength {
      get { return dict.Count; }
    }
    public bool Equals(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        V v1, v2;
        if (!dict.TryGetValue(u, out v1)) {
          return false; // this shouldn't happen
        }
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!v1.Equals(v2)) {
          return false;
        }
      }
      foreach (U u in other.dict.Keys) {
        if (!dict.ContainsKey(u)) {
          return false; // this shouldn't happen
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      foreach (var kv in dict) {
        s += sep + kv.Key.ToString() + " := " + kv.Value.ToString();
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains(U u) {
      return dict.ContainsKey(u);
    }
    public V Select(U index) {
      return dict[index];
    }
    public Map<U, V> Update(U index, V val) {
      Dictionary<U, V> d = new Dictionary<U, V>(dict);
      d[index] = val;
      return new Map<U, V>(d);
    }
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
  }
#endif
  public class Sequence<T>
  {
    T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public int Length {
      get { return elmts.Length; }
    }
    public long LongLength {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ elmts[i].GetHashCode();
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + t.ToString();
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!elmts[i].Equals(other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains(T t) {
      int n = elmts.Length;
      for (int i = 0; i < n; i++) {
        if (t.Equals(elmts[i]))
          return true;
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static System.Predicate<BigInteger> PredicateConverter_byte(System.Predicate<byte> pred) {
      return x => pred((byte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_sbyte(System.Predicate<sbyte> pred) {
      return x => pred((sbyte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ushort(System.Predicate<ushort> pred) {
      return x => pred((ushort)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_short(System.Predicate<short> pred) {
      return x => pred((short)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_uint(System.Predicate<uint> pred) {
      return x => pred((uint)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_int(System.Predicate<int> pred) {
      return x => pred((int)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ulong(System.Predicate<ulong> pred) {
      return x => pred((ulong)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_long(System.Predicate<long> pred) {
      return x => pred((long)x);
    }
    // Computing forall/exists quantifiers
    public static bool QuantBool(bool frall, System.Predicate<bool> pred) {
      if (frall) {
        return pred(false) && pred(true);
      } else {
        return pred(false) || pred(true);
      }
    }
    public static bool QuantChar(bool frall, System.Predicate<char> pred) {
      for (int i = 0; i < 0x10000; i++) {
        if (pred((char)i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantInt(BigInteger lo, BigInteger hi, bool frall, System.Predicate<BigInteger> pred) {
      for (BigInteger i = lo; i < hi; i++) {
        if (pred(i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSet<U>(Dafny.Set<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantMap<U,V>(Dafny.Map<U,V> map, bool frall, System.Predicate<U> pred) {
      foreach (var u in map.Domain) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSeq<U>(Dafny.Sequence<U> seq, bool frall, System.Predicate<U> pred) {
      foreach (var u in seq.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantDatatype<U>(IEnumerable<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public delegate Dafny.Set<T> ComprehensionDelegate<T>();
    public delegate Dafny.Map<U, V> MapComprehensionDelegate<U, V>();
    public static IEnumerable<bool> AllBooleans {
      get {
        yield return false;
        yield return true;
      }
    }
    public static IEnumerable<char> AllChars {
      get {
        for (int i = 0; i < 0x10000; i++) {
          yield return (char)i;
        }
      }
    }
    public static IEnumerable<BigInteger> AllIntegers {
      get {
        yield return new BigInteger(0);
        for (var j = new BigInteger(1);; j++) {
          yield return j;
          yield return -j;
        }
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public delegate Result Function<Input,Result>(Input input);

    public static A Id<A>(A a) {
      return a;
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    BigInteger num, den;  // invariant 1 <= den
    public override string ToString() {
      return string.Format("({0}.0 / {1}.0)", num, den);
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (0 <= num) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
      var xx = a.den / gcd;
      var yy = b.den / gcd;
      // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
      aa = a.num * yy;
      bb = b.num * xx;
      dd = a.den * yy;
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return 0 < a.CompareTo(b);
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return 0 <= a.CompareTo(b);
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}
namespace Dafny {
  public partial class Helpers {
      public static T[] InitNewArray1<T>(BigInteger size0) {
        int s0 = (int)size0;
        T[] a = new T[s0];
        BigInteger[] b = a as BigInteger[];
        if (b != null) {
          BigInteger z = new BigInteger(0);
          for (int i0 = 0; i0 < s0; i0++)
            b[i0] = z;
        }
        return a;
      }
  }
}
namespace @_System {



  public abstract class Base___tuple_h4<@T0,@T1,@T2,@T3> { }
  public class __tuple_h4____hMake4<@T0,@T1,@T2,@T3> : Base___tuple_h4<@T0,@T1,@T2,@T3> {
    public readonly @T0 @_0;
    public readonly @T1 @_1;
    public readonly @T2 @_2;
    public readonly @T3 @_3;
    public __tuple_h4____hMake4(@T0 @_0, @T1 @_1, @T2 @_2, @T3 @_3) {
      this.@_0 = @_0;
      this.@_1 = @_1;
      this.@_2 = @_2;
      this.@_3 = @_3;
    }
    public override bool Equals(object other) {
      var oth = other as _System.@__tuple_h4____hMake4<@T0,@T1,@T2,@T3>;
      return oth != null && this.@_0.Equals(oth.@_0) && this.@_1.Equals(oth.@_1) && this.@_2.Equals(oth.@_2) && this.@_3.Equals(oth.@_3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@_0.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@_1.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@_2.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@_3.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += @_0.ToString();
      s += ", ";
      s += @_1.ToString();
      s += ", ";
      s += @_2.ToString();
      s += ", ";
      s += @_3.ToString();
      s += ")";
      return s;
    }
  }
  public struct @__tuple_h4<@T0,@T1,@T2,@T3> {
    Base___tuple_h4<@T0,@T1,@T2,@T3> _d;
    public Base___tuple_h4<@T0,@T1,@T2,@T3> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @__tuple_h4(Base___tuple_h4<@T0,@T1,@T2,@T3> d) { this._d = d; }
    static Base___tuple_h4<@T0,@T1,@T2,@T3> theDefault;
    public static Base___tuple_h4<@T0,@T1,@T2,@T3> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@__tuple_h4____hMake4<@T0,@T1,@T2,@T3>(default(@T0), default(@T1), default(@T2), default(@T3));
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @__tuple_h4<@T0,@T1,@T2,@T3> && _D.Equals(((@__tuple_h4<@T0,@T1,@T2,@T3>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is____hMake4 { get { return _D is __tuple_h4____hMake4<@T0,@T1,@T2,@T3>; } }
    public @T0 dtor__0 { get { return ((__tuple_h4____hMake4<@T0,@T1,@T2,@T3>)_D).@_0; } }
    public @T1 dtor__1 { get { return ((__tuple_h4____hMake4<@T0,@T1,@T2,@T3>)_D).@_1; } }
    public @T2 dtor__2 { get { return ((__tuple_h4____hMake4<@T0,@T1,@T2,@T3>)_D).@_2; } }
    public @T3 dtor__3 { get { return ((__tuple_h4____hMake4<@T0,@T1,@T2,@T3>)_D).@_3; } }
  }
} // end of namespace _System
namespace @DafnyIO {

  public class @byte {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
  }

  public class @uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
  }

  public class @int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public class @uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
  }

  public class @uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
  }

  public class @nat32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
  }

  public partial class @HostEnvironment {
  }

  public partial class @HostConstants {
  }

  public partial class @OkState {
  }

  public partial class @FileSystemState {
  }

  public partial class @FileStream {
  }

  public partial class @__default {
  }
} // end of namespace DafnyIO
namespace @_2_PropLogic_Compile {

  public abstract class Base_Option<@T> { }
  public class Option_Some<@T> : Base_Option<@T> {
    public readonly @T @value;
    public Option_Some(@T @value) {
      this.@value = @value;
    }
    public override bool Equals(object other) {
      var oth = other as _2_PropLogic_Compile.@Option_Some<@T>;
      return oth != null && this.@value.Equals(oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@value.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_2_PropLogic_Compile.Option.Some";
      s += "(";
      s += @value.ToString();
      s += ")";
      return s;
    }
  }
  public class Option_None<@T> : Base_Option<@T> {
    public Option_None() {
    }
    public override bool Equals(object other) {
      var oth = other as _2_PropLogic_Compile.@Option_None<@T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_2_PropLogic_Compile.Option.None";
      return s;
    }
  }
  public struct @Option<@T> {
    Base_Option<@T> _d;
    public Base_Option<@T> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Option(Base_Option<@T> d) { this._d = d; }
    static Base_Option<@T> theDefault;
    public static Base_Option<@T> Default {
      get {
        if (theDefault == null) {
          theDefault = new _2_PropLogic_Compile.@Option_None<@T>();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Option<@T> && _D.Equals(((@Option<@T>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Some { get { return _D is Option_Some<@T>; } }
    public bool is_None { get { return _D is Option_None<@T>; } }
    public @T dtor_value { get { return ((Option_Some<@T>)_D).@value; } }
  }

  public abstract class Base_Bool { }
  public class Bool_True : Base_Bool {
    public Bool_True() {
    }
    public override bool Equals(object other) {
      var oth = other as _2_PropLogic_Compile.@Bool_True;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_2_PropLogic_Compile.Bool.True";
      return s;
    }
  }
  public class Bool_False : Base_Bool {
    public Bool_False() {
    }
    public override bool Equals(object other) {
      var oth = other as _2_PropLogic_Compile.@Bool_False;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_2_PropLogic_Compile.Bool.False";
      return s;
    }
  }
  public struct @Bool {
    Base_Bool _d;
    public Base_Bool _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Bool(Base_Bool d) { this._d = d; }
    static Base_Bool theDefault;
    public static Base_Bool Default {
      get {
        if (theDefault == null) {
          theDefault = new _2_PropLogic_Compile.@Bool_True();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Bool && _D.Equals(((@Bool)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_True { get { return _D is Bool_True; } }
    public bool is_False { get { return _D is Bool_False; } }
    public static System.Collections.Generic.IEnumerable<@Bool> AllSingletonConstructors {
      get {
        yield return new @Bool(new Bool_True());
        yield return new @Bool(new Bool_False());
        yield break;
      }
    }
  }

  public abstract class Base_Literal { }
  public class Literal_V : Base_Literal {
    public readonly BigInteger @v;
    public readonly @_2_PropLogic_Compile.@Bool @s;
    public Literal_V(BigInteger @v, @_2_PropLogic_Compile.@Bool @s) {
      this.@v = @v;
      this.@s = @s;
    }
    public override bool Equals(object other) {
      var oth = other as _2_PropLogic_Compile.@Literal_V;
      return oth != null && this.@v.Equals(oth.@v) && this.@s.Equals(oth.@s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@v.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@s.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string ss = "_2_PropLogic_Compile.Literal.V";
      ss += "(";
      ss += @v.ToString();
      ss += ", ";
      ss += @s.ToString();
      ss += ")";
      return ss;
    }
  }
  public class Literal_C : Base_Literal {
    public readonly @_2_PropLogic_Compile.@Bool @b;
    public Literal_C(@_2_PropLogic_Compile.@Bool @b) {
      this.@b = @b;
    }
    public override bool Equals(object other) {
      var oth = other as _2_PropLogic_Compile.@Literal_C;
      return oth != null && this.@b.Equals(oth.@b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@b.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_2_PropLogic_Compile.Literal.C";
      s += "(";
      s += @b.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Literal {
    Base_Literal _d;
    public Base_Literal _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Literal(Base_Literal d) { this._d = d; }
    static Base_Literal theDefault;
    public static Base_Literal Default {
      get {
        if (theDefault == null) {
          theDefault = new _2_PropLogic_Compile.@Literal_V(BigInteger.Zero, new @_2_PropLogic_Compile.@Bool());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Literal && _D.Equals(((@Literal)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_V { get { return _D is Literal_V; } }
    public bool is_C { get { return _D is Literal_C; } }
    public BigInteger dtor_v { get { return ((Literal_V)_D).@v; } }
    public @_2_PropLogic_Compile.@Bool dtor_s { get { return ((Literal_V)_D).@s; } }
    public @_2_PropLogic_Compile.@Bool dtor_b { get { return ((Literal_C)_D).@b; } }
  }






  public partial class @__default {
  }
} // end of namespace _2_PropLogic_Compile
namespace @DimacsUtils {



  public partial class @Dimacs {
    public static void @convert__dimacs(int[][] @benchmark, out Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi)
    {
      @phi = Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>>.Empty;
    TAIL_CALL_START: ;
      @phi = Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>>.FromElements();
      BigInteger @_223_i = BigInteger.Zero;
      @_223_i = new BigInteger(0);
      while ((@_223_i) < (new BigInteger((@benchmark).@Length)))
      {
        Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @_224_clause = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.Empty;
        @_224_clause = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.FromElements();
        BigInteger @_225_j = BigInteger.Zero;
        @_225_j = new BigInteger(0);
        if (((@benchmark)[(int)(@_223_i)]) != (object) ((object)null))
        {
          while ((@_225_j) < ((new BigInteger(((@benchmark)[(int)(@_223_i)]).@Length)) - (new BigInteger(1))))
          {
            BigInteger @_226_lit = BigInteger.Zero;
            @_226_lit = new BigInteger(((@benchmark)[(int)(@_223_i)])[(int)(@_225_j)]);
            @_2_PropLogic_Compile.@Bool @_227_s = new @_2_PropLogic_Compile.@Bool();
            @_227_s = ((@_226_lit) < (new BigInteger(0))) ? (new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_False())) : (new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_True()));
            @_224_clause = (@_224_clause).@Concat(Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.FromElements(new @_2_PropLogic_Compile.@Literal(new _2_PropLogic_Compile.@Literal_V(((@_226_lit) < (new BigInteger(0))) ? (((new BigInteger(0)) - (new BigInteger(1))) * (@_226_lit)) : (@_226_lit), @_227_s))));
            @_225_j = (@_225_j) + (new BigInteger(1));
          }
        }
        @phi = (@phi).@Concat(Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>>.FromElements(@_224_clause));
        @_223_i = (@_223_i) + (new BigInteger(1));
      }
    }
  }

  public partial class @__default {
  }
} // end of namespace DimacsUtils
namespace @_8_DPLL_Compile {




  public partial class @__default {
    public static void @get__fmla__vars(Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, out Dafny.Sequence<BigInteger> @vars)
    {
      @vars = Dafny.Sequence<BigInteger>.Empty;
    TAIL_CALL_START: ;
      @vars = Dafny.Sequence<BigInteger>.FromElements();
      BigInteger @_228_i = BigInteger.Zero;
      @_228_i = new BigInteger(0);
      while ((@_228_i) < (new BigInteger((@phi).Length)))
      {
        BigInteger @_229_j = BigInteger.Zero;
        @_229_j = new BigInteger(0);
        Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @_230_c = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.Empty;
        @_230_c = (@phi).Select(@_228_i);
        while ((@_229_j) < (new BigInteger((@_230_c).Length)))
        {
          if ((((@_230_c).Select(@_229_j)).@is_V) && (!(@vars).@Contains(((@_230_c).Select(@_229_j)).@dtor_v)))
          {
            @vars = (@vars).@Concat(Dafny.Sequence<BigInteger>.FromElements(((@_230_c).Select(@_229_j)).@dtor_v));
          }
          @_229_j = (@_229_j) + (new BigInteger(1));
        }
        @_228_i = (@_228_i) + (new BigInteger(1));
      }
    }
    public static void @eval__literal(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, @_2_PropLogic_Compile.@Literal @a, out @_2_PropLogic_Compile.@Option<bool> @b)
    {
      @b = new @_2_PropLogic_Compile.@Option<bool>();
    TAIL_CALL_START: ;
      if ((@a).@is_C)
      {
        if (((@a).@dtor_b).@Equals(new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_True())))
        {
          @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(true));
          return;
        }
        else
        {
          @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(false));
          return;
        }
      }
      else
      {
        if (!(@I).@Contains((@a).@dtor_v))
        {
          @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_None<bool>());
          return;
        }
        if ((((@I).Select((@a).@dtor_v)).@dtor__0).@Equals((@a).@dtor_s))
        {
          @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(true));
          return;
        }
        else
        {
          @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(false));
          return;
        }
      }
    }
    public static void @sat__clause(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @c, out @_2_PropLogic_Compile.@Option<bool> @b)
    {
      @b = new @_2_PropLogic_Compile.@Option<bool>();
    TAIL_CALL_START: ;
      BigInteger @_231_i = BigInteger.Zero;
      @_231_i = new BigInteger(0);
      BigInteger @_232_counter = BigInteger.Zero;
      @_232_counter = new BigInteger(0);
      while ((@_231_i) < (new BigInteger((@c).Length)))
      {
        @_2_PropLogic_Compile.@Option<bool> @_233_v = new @_2_PropLogic_Compile.@Option<bool>();
        @_2_PropLogic_Compile.@Option<bool> _out0;
        @_8_DPLL_Compile.@__default.@eval__literal(@I, (@c).Select(@_231_i), out _out0);
        @_233_v = _out0;
        if (((@_233_v).@is_Some) && ((@_233_v).@dtor_value))
        {
          @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(true));
          return;
        }
        else
        {
          if ((@_233_v).@is_None)
          {
            @_232_counter = (@_232_counter) + (new BigInteger(1));
          }
        }
        @_231_i = (@_231_i) + (new BigInteger(1));
      }
      if (!(@_232_counter).@Equals(new BigInteger(0)))
      {
        @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_None<bool>());
        return;
      }
      @b = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(false));
      return;
    }
    public static void @is__unit(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @c, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      @_2_PropLogic_Compile.@Option<bool> @_234_sat__c = new @_2_PropLogic_Compile.@Option<bool>();
      @_2_PropLogic_Compile.@Option<bool> _out1;
      @_8_DPLL_Compile.@__default.@sat__clause(@I, @c, out _out1);
      @_234_sat__c = _out1;
      if ((@_234_sat__c).@is_Some)
      {
        @b = false;
        return;
      }
      BigInteger @_235_counter = BigInteger.Zero;
      @_235_counter = new BigInteger(0);
      BigInteger @_236_i = BigInteger.Zero;
      @_236_i = new BigInteger(0);
      while ((@_236_i) < (new BigInteger((@c).Length)))
      {
        @_2_PropLogic_Compile.@Option<bool> @_237_assigned = new @_2_PropLogic_Compile.@Option<bool>();
        @_2_PropLogic_Compile.@Option<bool> _out2;
        @_8_DPLL_Compile.@__default.@eval__literal(@I, (@c).Select(@_236_i), out _out2);
        @_237_assigned = _out2;
        if ((@_237_assigned).@is_None)
        {
          @_235_counter = (@_235_counter) + (new BigInteger(1));
        }
        @_236_i = (@_236_i) + (new BigInteger(1));
      }
      if ((@_235_counter).@Equals(new BigInteger(1)))
      {
        { }
        @b = true;
        return;
      }
      else
      {
        @b = false;
        return;
      }
    }
    public static void @exist__units(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, out bool @b, out Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @c)
    {
      @b = false;
      @c = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.Empty;
    TAIL_CALL_START: ;
      BigInteger @_238_i = BigInteger.Zero;
      @_238_i = new BigInteger(0);
      while ((@_238_i) < (new BigInteger((@phi).Length)))
      {
        bool @_239_u = false;
        bool _out3;
        @_8_DPLL_Compile.@__default.@is__unit(@I, (@phi).Select(@_238_i), out _out3);
        @_239_u = _out3;
        if (@_239_u)
        {
          bool _rhs0 = true;
          Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _rhs1 = (@phi).Select(@_238_i);
          @b = _rhs0;
          @c = _rhs1;
          return;
        }
        { }
        @_238_i = (@_238_i) + (new BigInteger(1));
      }
      bool _rhs2 = false;
      Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _rhs3 = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.FromElements();
      @b = _rhs2;
      @c = _rhs3;
      return;
    }
    public static void @propagate(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @c, BigInteger @level, out Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I_k)
    {
      @I_k = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.Empty;
    TAIL_CALL_START: ;
      bool @_240_b = false;
      bool _out4;
      @_8_DPLL_Compile.@__default.@is__unit(@I, @c, out _out4);
      @_240_b = _out4;
      if (!(@_240_b))
      {
        @I_k = @I;
        return;
      }
      BigInteger @_241_i = BigInteger.Zero;
      @_241_i = new BigInteger(0);
      BigInteger @_242_v = BigInteger.Zero;
      @_242_v = (new BigInteger(0)) - (new BigInteger(1));
      @_2_PropLogic_Compile.@Bool @_243_s = new @_2_PropLogic_Compile.@Bool();
      @_243_s = new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_True());
      Dafny.Set<BigInteger> @_244_d = Dafny.Set<BigInteger>.Empty;
      @_244_d = Dafny.Set<BigInteger>.FromElements();
      @I_k = @I;
      { }
      while ((@_241_i) < (new BigInteger((@c).Length)))
      {
        if ((((@c).Select(@_241_i)).@is_V) && (!(@I).@Contains(((@c).Select(@_241_i)).@dtor_v)))
        {
          @_242_v = ((@c).Select(@_241_i)).@dtor_v;
          @_243_s = ((@c).Select(@_241_i)).@dtor_s;
        }
        else
        {
          if ((((@c).Select(@_241_i)).@is_V) && ((@I).@Contains(((@c).Select(@_241_i)).@dtor_v)))
          {
            Dafny.Set<BigInteger> @_245_di = Dafny.Set<BigInteger>.Empty;
            @_245_di = ((@I).Select(((@c).Select(@_241_i)).@dtor_v)).@dtor__2;
            @_244_d = (@_244_d).@Union(@_245_di);
          }
        }
        @_241_i = (@_241_i) + (new BigInteger(1));
      }
      @I_k = (@I_k).Update(@_242_v, new @_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>(new _System.@__tuple_h4____hMake4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>(@_243_s, false, @_244_d, @level)));
    }
    public static void @decide(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, BigInteger @level, out Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I_k, out BigInteger @succ__level)
    {
      @I_k = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.Empty;
      @succ__level = BigInteger.Zero;
    TAIL_CALL_START: ;
      @I_k = @I;
      BigInteger @_246_i = BigInteger.Zero;
      @_246_i = new BigInteger(0);
      Dafny.Sequence<BigInteger> @_247_vars = Dafny.Sequence<BigInteger>.Empty;
      Dafny.Sequence<BigInteger> _out5;
      @_8_DPLL_Compile.@__default.@get__fmla__vars(@phi, out _out5);
      @_247_vars = _out5;
      while ((@_246_i) < (new BigInteger((@_247_vars).Length)))
      {
        if (!(@I).@Contains((@_247_vars).Select(@_246_i)))
        {
          @succ__level = (@level) + (new BigInteger(1));
          @I_k = (@I_k).Update((@_247_vars).Select(@_246_i), new @_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>(new _System.@__tuple_h4____hMake4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>(new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_True()), true, Dafny.Set<BigInteger>.FromElements((@_247_vars).Select(@_246_i)), @succ__level)));
          Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _rhs4 = @I_k;
          BigInteger _rhs5 = @succ__level;
          @I_k = _rhs4;
          @succ__level = _rhs5;
          return;
        }
        @_246_i = (@_246_i) + (new BigInteger(1));
      }
      { }
      Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _rhs6 = @I;
      BigInteger _rhs7 = @level;
      @I_k = _rhs6;
      @succ__level = _rhs7;
      return;
    }
    public static void @has__decision(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      BigInteger @_248_i = BigInteger.Zero;
      @_248_i = new BigInteger(0);
      Dafny.Sequence<BigInteger> @_249_vars = Dafny.Sequence<BigInteger>.Empty;
      Dafny.Sequence<BigInteger> _out6;
      @_8_DPLL_Compile.@__default.@get__fmla__vars(@phi, out _out6);
      @_249_vars = _out6;
      while ((@_248_i) < (new BigInteger((@_249_vars).Length)))
      {
        if (((@I).@Contains((@_249_vars).Select(@_248_i))) && (((@I).Select((@_249_vars).Select(@_248_i))).@dtor__1))
        {
          @b = true;
          return;
        }
        @_248_i = (@_248_i) + (new BigInteger(1));
      }
      @b = false;
      return;
    }
    public static void @sat__formula(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, out @_2_PropLogic_Compile.@Option<bool> @b, out Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @c)
    {
      @b = new @_2_PropLogic_Compile.@Option<bool>();
      @c = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.Empty;
    TAIL_CALL_START: ;
      BigInteger @_250_i = BigInteger.Zero;
      @_250_i = new BigInteger(0);
      BigInteger @_251_counter = BigInteger.Zero;
      @_251_counter = new BigInteger(0);
      while ((@_250_i) < (new BigInteger((@phi).Length)))
      {
        @_2_PropLogic_Compile.@Option<bool> @_252_v = new @_2_PropLogic_Compile.@Option<bool>();
        @_2_PropLogic_Compile.@Option<bool> _out7;
        @_8_DPLL_Compile.@__default.@sat__clause(@I, (@phi).Select(@_250_i), out _out7);
        @_252_v = _out7;
        if (((@_252_v).@is_Some) && (!((@_252_v).@dtor_value)))
        {
          @_2_PropLogic_Compile.@Option<bool> _rhs8 = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(false));
          Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _rhs9 = (@phi).Select(@_250_i);
          @b = _rhs8;
          @c = _rhs9;
          return;
        }
        else
        {
          if ((@_252_v).@is_None)
          {
            @_251_counter = (@_251_counter) + (new BigInteger(1));
          }
        }
        @_250_i = (@_250_i) + (new BigInteger(1));
      }
      if (!(@_251_counter).@Equals(new BigInteger(0)))
      {
        @_2_PropLogic_Compile.@Option<bool> _rhs10 = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_None<bool>());
        Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _rhs11 = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.FromElements();
        @b = _rhs10;
        @c = _rhs11;
        return;
      }
      @_2_PropLogic_Compile.@Option<bool> _rhs12 = new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_Some<bool>(true));
      Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _rhs13 = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.FromElements();
      @b = _rhs12;
      @c = _rhs13;
      return;
    }
    public static void @Var__set__to__seq(Dafny.Set<BigInteger> @s, Dafny.Sequence<BigInteger> @sv, out Dafny.Sequence<BigInteger> @s_k)
    {
      @s_k = Dafny.Sequence<BigInteger>.Empty;
    TAIL_CALL_START: ;
      BigInteger @_253_i = BigInteger.Zero;
      @_253_i = new BigInteger(0);
      @s_k = Dafny.Sequence<BigInteger>.FromElements();
      while ((@_253_i) < (new BigInteger((@sv).Length)))
      {
        if ((@s).@Contains((@sv).Select(@_253_i)))
        {
          @s_k = (@s_k).@Concat(Dafny.Sequence<BigInteger>.FromElements((@sv).Select(@_253_i)));
        }
        @_253_i = (@_253_i) + (new BigInteger(1));
      }
      @s_k = @s_k;
      return;
    }
    public static void @cut__interpretation(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, BigInteger @level, Dafny.Sequence<BigInteger> @sv, out Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I_k)
    {
      @I_k = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.Empty;
    TAIL_CALL_START: ;
      BigInteger @_254_i = BigInteger.Zero;
      @_254_i = new BigInteger(0);
      @I_k = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.FromElements();
      while ((@_254_i) < (new BigInteger((@sv).Length)))
      {
        if (((@I).@Contains((@sv).Select(@_254_i))) && ((((@I).Select((@sv).Select(@_254_i))).@dtor__3) <= (@level)))
        {
          @I_k = (@I_k).Update((@sv).Select(@_254_i), (@I).Select((@sv).Select(@_254_i)));
        }
        @_254_i = (@_254_i) + (new BigInteger(1));
      }
      @I_k = @I_k;
      return;
    }
    public static void @get__conflict__causes(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @c, Dafny.Sequence<BigInteger> @sv, out Dafny.Sequence<BigInteger> @s_k)
    {
      @s_k = Dafny.Sequence<BigInteger>.Empty;
    TAIL_CALL_START: ;
      BigInteger @_255_i = BigInteger.Zero;
      @_255_i = new BigInteger(0);
      Dafny.Set<BigInteger> @_256_s = Dafny.Set<BigInteger>.Empty;
      @_256_s = Dafny.Set<BigInteger>.FromElements();
      while ((@_255_i) < (new BigInteger((@c).Length)))
      {
        if ((((@c).Select(@_255_i)).@is_V) && ((@I).@Contains(((@c).Select(@_255_i)).@dtor_v)))
        {
          @_256_s = (@_256_s).@Union(((@I).Select(((@c).Select(@_255_i)).@dtor_v)).@dtor__2);
        }
        @_255_i = (@_255_i) + (new BigInteger(1));
      }
      Dafny.Sequence<BigInteger> _out8;
      @_8_DPLL_Compile.@__default.@Var__set__to__seq(@_256_s, @sv, out _out8);
      @s_k = _out8;
    }
    public static void @backjump(Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I, Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @c, Dafny.Sequence<BigInteger> @sv, Dafny.Sequence<BigInteger> @s, BigInteger @level, out Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I_k, out Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi_k, out BigInteger @jump__level)
    {
      @I_k = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.Empty;
      @phi_k = Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>>.Empty;
      @jump__level = BigInteger.Zero;
    TAIL_CALL_START: ;
      BigInteger @_257_k = BigInteger.Zero;
      @_257_k = new BigInteger(0);
      Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @_258_learned__clause = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.Empty;
      @_258_learned__clause = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.FromElements();
      while ((@_257_k) < (new BigInteger((@s).Length)))
      {
        @_258_learned__clause = (@_258_learned__clause).@Concat(Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.FromElements(new @_2_PropLogic_Compile.@Literal(new _2_PropLogic_Compile.@Literal_V((@s).Select(@_257_k), new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_False())))));
        @_257_k = (@_257_k) + (new BigInteger(1));
      }
      @phi_k = (@phi).@Concat(Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>>.FromElements(@_258_learned__clause));
      BigInteger @_259_i = BigInteger.Zero;
      @_259_i = new BigInteger(0);
      while ((@_259_i) <= (@level))
      {
        Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _out9;
        @_8_DPLL_Compile.@__default.@cut__interpretation(@I, @_259_i, @sv, out _out9);
        @I_k = _out9;
        BigInteger @_260_j = BigInteger.Zero;
        @_260_j = new BigInteger(0);
        BigInteger @_261_counter = BigInteger.Zero;
        @_261_counter = new BigInteger(0);
        BigInteger @_262_l = BigInteger.Zero;
        @_262_l = (new BigInteger(0)) - (new BigInteger(1));
        while ((@_260_j) < (new BigInteger((@s).Length)))
        {
          if (!(@I_k).@Contains((@s).Select(@_260_j)))
          {
            @_261_counter = (@_261_counter) + (new BigInteger(1));
            @_262_l = (@s).Select(@_260_j);
          }
          @_260_j = (@_260_j) + (new BigInteger(1));
        }
        if ((@_261_counter).@Equals(new BigInteger(1)))
        {
          Dafny.Set<BigInteger> @_263_cause__set = Dafny.Set<BigInteger>.Empty;
          @_263_cause__set = ((Dafny.Helpers.ComprehensionDelegate<BigInteger>)delegate() { var _coll0 = new System.Collections.Generic.List<BigInteger>(); foreach (var @_264_z in (@s).Elements) { if ((@s).@Contains(@_264_z)) {_coll0.Add(@_264_z); }}return Dafny.Set<BigInteger>.FromCollection(_coll0); })();
          System.Console.Write(Dafny.Sequence<char>.FromString("Jumping to level : "));
          System.Console.Write(@_259_i);
          System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
          @_263_cause__set = (@_263_cause__set).@Difference(Dafny.Set<BigInteger>.FromElements(@_262_l));
          @I_k = (@I_k).Update(@_262_l, new @_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>(new _System.@__tuple_h4____hMake4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>(new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_False()), false, @_263_cause__set, @_259_i)));
          Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _rhs14 = @I_k;
          Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> _rhs15 = @phi_k;
          BigInteger _rhs16 = @_259_i;
          @I_k = _rhs14;
          @phi_k = _rhs15;
          @jump__level = _rhs16;
          return;
        }
        @_259_i = (@_259_i) + (new BigInteger(1));
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("Backjumping failed.\n"));
    }
    public static void @CDCL(Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, out bool @sat, out Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @I)
    {
      @sat = false;
      @I = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.Empty;
    TAIL_CALL_START: ;
      Dafny.Sequence<BigInteger> @_265_vars = Dafny.Sequence<BigInteger>.Empty;
      Dafny.Sequence<BigInteger> _out10;
      @_8_DPLL_Compile.@__default.@get__fmla__vars(@phi, out _out10);
      @_265_vars = _out10;
      Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @_266_phi_k = Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>>.Empty;
      @_266_phi_k = @phi;
      @I = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.FromElements();
      BigInteger @_267_decision__level = BigInteger.Zero;
      @_267_decision__level = new BigInteger(0);
      while (true)
      {
        bool @_268_has__units = false;
        Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @_269_unit = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.Empty;
        bool _out11;
        Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _out12;
        @_8_DPLL_Compile.@__default.@exist__units(@I, @_266_phi_k, out _out11, out _out12);
        @_268_has__units = _out11;
        @_269_unit = _out12;
        while (@_268_has__units)
        {
          Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _out13;
          @_8_DPLL_Compile.@__default.@propagate(@I, @_269_unit, @_267_decision__level, out _out13);
          @I = _out13;
          bool _out14;
          Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _out15;
          @_8_DPLL_Compile.@__default.@exist__units(@I, @_266_phi_k, out _out14, out _out15);
          @_268_has__units = _out14;
          @_269_unit = _out15;
        }
        Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _out16;
        BigInteger _out17;
        @_8_DPLL_Compile.@__default.@decide(@I, @_266_phi_k, @_267_decision__level, out _out16, out _out17);
        @I = _out16;
        @_267_decision__level = _out17;
        @_2_PropLogic_Compile.@Option<bool> @_270_sat = new @_2_PropLogic_Compile.@Option<bool>();
        Dafny.Sequence<@_2_PropLogic_Compile.@Literal> @_271_conflict = Dafny.Sequence<@_2_PropLogic_Compile.@Literal>.Empty;
        @_2_PropLogic_Compile.@Option<bool> _out18;
        Dafny.Sequence<@_2_PropLogic_Compile.@Literal> _out19;
        @_8_DPLL_Compile.@__default.@sat__formula(@I, @_266_phi_k, out _out18, out _out19);
        @_270_sat = _out18;
        @_271_conflict = _out19;
        if (((@_270_sat).@is_Some) && (!((@_270_sat).@dtor_value)))
        {
          bool @_272_has__d = false;
          bool _out20;
          @_8_DPLL_Compile.@__default.@has__decision(@I, @_266_phi_k, out _out20);
          @_272_has__d = _out20;
          if (!(@_272_has__d))
          {
            System.Console.Write(Dafny.Sequence<char>.FromString("Decisions exhausted. \n"));
            bool _rhs17 = false;
            Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _rhs18 = @I;
            @sat = _rhs17;
            @I = _rhs18;
            return;
          }
          Dafny.Sequence<BigInteger> @_273_s = Dafny.Sequence<BigInteger>.Empty;
          Dafny.Sequence<BigInteger> _out21;
          @_8_DPLL_Compile.@__default.@get__conflict__causes(@I, @_271_conflict, @_265_vars, out _out21);
          @_273_s = _out21;
          if ((@_273_s).@Equals(Dafny.Sequence<BigInteger>.FromElements()))
          {
            System.Console.Write(Dafny.Sequence<char>.FromString("Conflict causes exhausted.\n"));
            bool _rhs19 = false;
            Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _rhs20 = @I;
            @sat = _rhs19;
            @I = _rhs20;
            return;
          }
          Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _out22;
          Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> _out23;
          BigInteger _out24;
          @_8_DPLL_Compile.@__default.@backjump(@I, @_266_phi_k, @_271_conflict, @_265_vars, @_273_s, @_267_decision__level, out _out22, out _out23, out _out24);
          @I = _out22;
          @_266_phi_k = _out23;
          @_267_decision__level = _out24;
        }
        else
        {
          if (((@_270_sat).@is_Some) && ((@_270_sat).@dtor_value))
          {
            bool _rhs21 = true;
            Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _rhs22 = @I;
            @sat = _rhs21;
            @I = _rhs22;
            return;
          }
        }
      }
    }
    public static void @DPLL(Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, out @_2_PropLogic_Compile.@Option<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>> @alpha)
    {
      @alpha = new @_2_PropLogic_Compile.@Option<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>>();
    TAIL_CALL_START: ;
      Dafny.Sequence<BigInteger> @_274_vars = Dafny.Sequence<BigInteger>.Empty;
      Dafny.Sequence<BigInteger> _out25;
      @_8_DPLL_Compile.@__default.@get__fmla__vars(@phi, out _out25);
      @_274_vars = _out25;
      bool @_275_sat = false;
      Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> @_276_I = Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>>.Empty;
      bool _out26;
      Dafny.Map<BigInteger,@_System.@__tuple_h4<@_2_PropLogic_Compile.@Bool,bool,Dafny.Set<BigInteger>,BigInteger>> _out27;
      @_8_DPLL_Compile.@__default.@CDCL(@phi, out _out26, out _out27);
      @_275_sat = _out26;
      @_276_I = _out27;
      Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool> @_277_alpha_k = Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>.Empty;
      @_277_alpha_k = Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>.FromElements();
      if (@_275_sat)
      {
        BigInteger @_278_i = BigInteger.Zero;
        @_278_i = new BigInteger(0);
        while ((@_278_i) < (new BigInteger((@_274_vars).Length)))
        {
          if ((@_276_I).@Contains((@_274_vars).Select(@_278_i)))
          {
            @_277_alpha_k = (@_277_alpha_k).Update((@_274_vars).Select(@_278_i), ((@_276_I).Select((@_274_vars).Select(@_278_i))).@dtor__0);
          }
          @_278_i = (@_278_i) + (new BigInteger(1));
        }
        @alpha = new @_2_PropLogic_Compile.@Option<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>>(new _2_PropLogic_Compile.@Option_Some<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>>(@_277_alpha_k));
        return;
      }
      else
      {
        @alpha = new @_2_PropLogic_Compile.@Option<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>>(new _2_PropLogic_Compile.@Option_None<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>>());
        return;
      }
    }
    public static void @print__assignment(Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool> @alpha)
    {
    TAIL_CALL_START: ;
      Dafny.Sequence<BigInteger> @_279_vars = Dafny.Sequence<BigInteger>.Empty;
      Dafny.Sequence<BigInteger> _out28;
      @_8_DPLL_Compile.@__default.@get__fmla__vars(@phi, out _out28);
      @_279_vars = _out28;
      BigInteger @_280_i = BigInteger.Zero;
      @_280_i = new BigInteger(0);
      while ((@_280_i) < (new BigInteger((@_279_vars).Length)))
      {
        if ((@alpha).@Contains((@_279_vars).Select(@_280_i)))
        {
          System.Console.Write(Dafny.Sequence<char>.FromString("  "));
          System.Console.Write((@_279_vars).Select(@_280_i));
          System.Console.Write(Dafny.Sequence<char>.FromString(" => "));
          System.Console.Write((((@alpha).Select((@_279_vars).Select(@_280_i))).@Equals(new @_2_PropLogic_Compile.@Bool(new _2_PropLogic_Compile.@Bool_True()))) ? (Dafny.Sequence<char>.FromString("T")) : (Dafny.Sequence<char>.FromString("F")));
          System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
        }
        @_280_i = (@_280_i) + (new BigInteger(1));
      }
    }
    public static void @run__benchmark(Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @phi, Dafny.Sequence<char> @name, @_2_PropLogic_Compile.@Option<bool> @expected__result)
    {
    TAIL_CALL_START: ;
      @_2_PropLogic_Compile.@Option<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>> @_281_alpha = new @_2_PropLogic_Compile.@Option<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>>();
      @_2_PropLogic_Compile.@Option<Dafny.Map<BigInteger,@_2_PropLogic_Compile.@Bool>> _out29;
      @_8_DPLL_Compile.@__default.@DPLL(@phi, out _out29);
      @_281_alpha = _out29;
      Dafny.Sequence<char> @_282_pre = Dafny.Sequence<char>.Empty;
      @_282_pre = ((Dafny.Sequence<char>.FromString("\n[")).@Concat(@name)).@Concat(Dafny.Sequence<char>.FromString("]: "));
      if ((@expected__result).@is_Some)
      {
        Dafny.Sequence<char> @_283_expected = Dafny.Sequence<char>.Empty;
        @_283_expected = ((@expected__result).@dtor_value) ? (Dafny.Sequence<char>.FromString("sat")) : (Dafny.Sequence<char>.FromString("unsat"));
        if (!((@_281_alpha).@is_Some).@Equals((@expected__result).@dtor_value))
        {
          System.Console.Write((((@_282_pre).@Concat(Dafny.Sequence<char>.FromString("failed (expected "))).@Concat(@_283_expected)).@Concat(Dafny.Sequence<char>.FromString(")\n")));
        }
        else
        {
          System.Console.Write((((@_282_pre).@Concat(Dafny.Sequence<char>.FromString("succeeded with "))).@Concat(@_283_expected)).@Concat(Dafny.Sequence<char>.FromString("\n")));
        }
      }
      else
      {
        System.Console.Write(((@_282_pre).@Concat(Dafny.Sequence<char>.FromString("returned "))).@Concat(((@_281_alpha).@is_Some) ? (Dafny.Sequence<char>.FromString("sat\n")) : (Dafny.Sequence<char>.FromString("unsat\n"))));
      }
      if ((@_281_alpha).@is_Some)
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("satisfying assignment:\n"));
        @_8_DPLL_Compile.@__default.@print__assignment(@phi, (@_281_alpha).@dtor_value);
      }
      System.Console.Write(Dafny.Sequence<char>.FromString("----------------------------\n"));
    }
    public static void @Main()
    {
    TAIL_CALL_START: ;
      uint @_284_n__args = 0;
      uint _out30;
      @DafnyIO.@HostConstants.@NumCommandLineArgs(out _out30);
      @_284_n__args = _out30;
      if ((@_284_n__args) < (2U))
      {
        return;
      }
      char[] @_285_dimacs__path = (char[])null;
      char[] _out31;
      @DafnyIO.@HostConstants.@GetCommandLineArg(1UL, out _out31);
      @_285_dimacs__path = _out31;
      bool @_286_path__exists = false;
      bool _out32;
      @DafnyIO.@FileStream.@FileExists(@_285_dimacs__path, out _out32);
      @_286_path__exists = _out32;
      if (!(@_286_path__exists))
      {
        return;
      }
      int[][] @_287_benchmark = (int[][])null;
      int[][] _out33;
      @DimacsUtils.@Dimacs.@FmlaFromFile(@_285_dimacs__path, out _out33);
      @_287_benchmark = _out33;
      if ((@_287_benchmark) == (object) ((object)null))
      {
        return;
      }
      Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> @_288_phi = Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>>.Empty;
      Dafny.Sequence<Dafny.Sequence<@_2_PropLogic_Compile.@Literal>> _out34;
      @DimacsUtils.@Dimacs.@convert__dimacs(@_287_benchmark, out _out34);
      @_288_phi = _out34;
      @_8_DPLL_Compile.@__default.@run__benchmark(@_288_phi, Dafny.Helpers.SeqFromArray(@_285_dimacs__path), new @_2_PropLogic_Compile.@Option<bool>(new _2_PropLogic_Compile.@Option_None<bool>()));
    }
  }
} // end of namespace _8_DPLL_Compile


public partial class @__default {
}



