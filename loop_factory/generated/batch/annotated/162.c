int main1(int q){
  int e, r, k, s;

  e=q+11;
  r=3;
  k=q;
  s=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == \at(q, Pre) + 11;
  loop invariant k <= e;
  loop invariant k >= \at(q, Pre);
  loop invariant r == 3;
  loop invariant q == \at(q, Pre);
  loop invariant e == q + 11;
  loop invariant q <= k;
  loop invariant ((k - q) % 2 == 0) || (k == e);
  loop invariant \at(q, Pre) <= k;
  loop invariant k >= q;
  loop assigns k;
*/
while (r+1<=e) {
      if (k+2<=e) {
          k = k+2;
      }
      else {
          k = e;
      }
  }

}
