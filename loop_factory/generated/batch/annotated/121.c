int main1(int a){
  int r, k, v;

  r=a;
  k=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant (k <= 2*r - 4) ==> (v == 0);
  loop invariant k >= 0;

  loop invariant v >= 0;
  loop invariant r == \at(a, Pre);
  loop invariant (r >= 4) ==> (v == 0);
  loop invariant r == a;
  loop invariant a == \at(a, Pre);
  loop invariant v <= r*(r-1)/2;

  loop invariant 0 <= k;
  loop invariant 0 <= v;
  loop invariant v <= k*(k-1)/2;
  loop assigns v, k;
*/
while (k<=r-1) {
      v = v+k;
      if (k+5<=r+r) {
          v = v-v;
      }
      k = k+1;
  }

}
