int main1(int b,int k,int n,int q){
  int h, o, v, r;

  h=n+15;
  o=0;
  v=0;
  r=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(n,Pre) + 15;
  loop invariant v >= 0;
  loop invariant (v == 0) ==> (r == \at(q,Pre));
  loop invariant (v > 0) ==> (r + v == h + 1);
  loop invariant q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant h == n + 15;
  loop invariant (v == 0) ==> (r == q);
  loop invariant (v > 0) ==> (r == h - v + 1);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == 0 ==> r == q;
  loop invariant v >= 1 ==> r + v == h + 1;
  loop assigns r, v;
*/
while (1) {
      r = h-v;
      v = v+1;
  }

}
