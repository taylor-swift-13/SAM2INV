int main1(int p,int q){
  int n, x, i, r;

  n=q+19;
  x=3;
  i=p;
  r=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(q, Pre) + 19;
  loop invariant q == \at(q, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (i - \at(p, Pre)) % 3 == 0 && i >= \at(p, Pre);

  loop invariant (i - \at(p, Pre)) % 3 == 0;
  loop invariant i >= \at(p, Pre);
  loop invariant i >= \at(p,Pre);
  loop invariant (i - \at(p,Pre)) % 3 == 0;

  loop invariant n == \at(q,Pre) + 19;
  loop invariant p == \at(p,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant n == q + 19 && (i - p) % 3 == 0;

  loop invariant p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant i >= \at(p, Pre) && ((i - \at(p, Pre)) % 3) == 0;
  loop invariant (n == 0) <==> (r == 0);
  loop invariant n == q + 19;
  loop invariant i >= p;
  loop invariant (i - p) % 3 == 0;
  loop invariant i >= p && (i - p) % 3 == 0;
  loop assigns i, r;
*/
while (1) {
      i = i+3;
      r = r+r;
  }

}
