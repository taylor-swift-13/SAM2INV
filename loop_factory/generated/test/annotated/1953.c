int main1(){
  int r1q, ynn, o, d;
  r1q=1+20;
  ynn=0;
  o=0;
  d=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == ynn;
  loop invariant 2 * d == - (ynn * (ynn + 1));
  loop invariant 0 <= ynn;
  loop invariant ynn <= r1q;
  loop invariant d == - (o * (o + 1)) / 2;
  loop invariant 0 <= o;
  loop invariant o <= r1q;
  loop invariant d == - ( (ynn*(ynn+1)) / 2 );
  loop invariant r1q == 1 + 20;
  loop assigns ynn, o, d;
*/
while (ynn < r1q) {
      ynn += 1;
      o = o + 1;
      d = d - o;
  }
}