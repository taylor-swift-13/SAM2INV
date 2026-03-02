int main1(int k,int n){
  int p, l, w, v;

  p=n;
  l=p+6;
  w=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == k * v;
  loop invariant p == n;

  loop invariant v >= 0;
  loop invariant w == v * k;
  loop invariant 0 <= v;
  loop invariant v <= p || p < 0;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);

  loop invariant p == \at(n, Pre);

  loop assigns w, v;
*/
while (v<p) {
      w = w+k;
      v = v+1;
  }

}
