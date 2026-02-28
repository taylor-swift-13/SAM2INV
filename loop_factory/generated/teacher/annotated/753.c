int main1(int a,int n,int p,int q){
  int o, k, v, h, u, d, x, r;

  o=15;
  k=o;
  v=p;
  h=k;
  u=k;
  d=-2;
  x=a;
  r=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v + k == p + o;
  loop invariant k >= 0;
  loop invariant k <= o;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v + k == p + 15;
  loop invariant (0 <= k && k <= 15) && ((k < 15) ==> (d == v + 29)) && ((k == 15) ==> (d == -2 && v == p));
  loop assigns d, v, k;
*/
while (k>0) {
      d = v+h+u;
      v = v+1;
      k = k-1;
  }

}
