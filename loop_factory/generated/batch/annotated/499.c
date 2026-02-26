int main1(int k,int m){
  int l, u, v, t;

  l=42;
  u=2;
  v=l;
  t=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 42;
  loop invariant v >= l;
  loop invariant t >= l;
  loop invariant t >= v;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v <= l;
  loop invariant 4*t == v*v + 2*v - 40*l;
  loop invariant v <= l + 1;
  loop assigns v, t;
*/
while (v<l) {
      if (v<l) {
          v = v+1;
      }
      v = v+1;
      t = t+v;
  }

}
