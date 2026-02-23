int main1(int m){
  int k, y, v, r;

  k=74;
  y=k;
  v=-8;
  r=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= k;
  loop invariant v >= -8;
  loop invariant k == 74;
  loop invariant m == \at(m, Pre);
  loop invariant v <= k && (v < k ==> v + 1 <= k) && v >= -8;
  loop invariant -8 <= v;
  loop assigns v;
*/
while (v<k) {
      if (v<k) {
          v = v+1;
      }
  }

}
