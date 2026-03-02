int main1(int k,int n){
  int p, l, w, v;

  p=n;
  l=p;
  w=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == v * k;
  loop invariant v >= 0;
  loop invariant p == \at(n, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v >= 0 && (v <= p || p < 0);
  loop invariant n == \at(n, Pre);

  loop invariant w == v * k && v >= 0 && k == \at(k, Pre);

  loop invariant k == \at(k, Pre) && n == \at(n, Pre) && p == \at(n, Pre);

  loop assigns w, v;
*/
while (v<p) {
      w = w+k;
      v = v+1;
  }

}
