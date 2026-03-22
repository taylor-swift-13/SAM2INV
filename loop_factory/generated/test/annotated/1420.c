int main1(){
  int b, k, ve, s1x;
  b=(1%8)+19;
  k=0;
  ve=k;
  s1x=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ve == 2 * k;
  loop invariant b == 20;
  loop invariant 0 <= k <= b;
  loop invariant ve == (s1x + 1) * k;
  loop assigns k, ve;
*/
while (k < b) {
      k += 1;
      ve = (s1x)+(ve);
      ve = ve + 1;
  }
}