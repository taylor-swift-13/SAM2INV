int main1(int p,int q){
  int n, i, v;

  n=35;
  i=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant n == 35;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v >= \at(q, Pre);
  loop invariant (v - \at(q, Pre)) % 3 == 0;
  loop invariant i <= n;
  loop invariant i >= 0;
  loop invariant v >= q;
  loop invariant (v - q) % 3 == 0;
  loop invariant ((v - \at(q, Pre)) % 3) == 0;
  loop assigns v;
*/
while (i<n) {
      v = v+2;
      v = v+1;
  }

}
