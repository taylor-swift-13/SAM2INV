int main1(int v){
  int q, w2j;
  q=76;
  w2j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(v, Pre) + w2j*(w2j + 1)/2;
  loop invariant 0 <= w2j;
  loop invariant w2j <= q;
  loop invariant q == 76;
  loop assigns w2j, v;
*/
while (w2j<q) {
      w2j += 1;
      if (w2j<=w2j) {
          w2j = w2j;
      }
      v = v + w2j;
  }
}