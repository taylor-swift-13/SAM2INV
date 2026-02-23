int main1(int k){
  int m, v, o, h;

  m=18;
  v=1;
  o=v;
  h=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (m - v) + v == m;
  loop invariant 1 <= v;
  loop invariant v <= m;
  loop invariant k == \at(k, Pre);
  loop invariant v >= 1;
  loop invariant m == 18;
  loop assigns v;
*/
while (v<m) {
      v = v+1;
  }

}
