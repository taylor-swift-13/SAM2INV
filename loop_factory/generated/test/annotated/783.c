int main1(){
  int t, k, mn5;
  t=1+15;
  k=1;
  mn5=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mn5 == t * k;
  loop invariant k <= t;
  loop invariant k >= 1;
  loop assigns k, mn5;
*/
for (; k*2<=t; k = k*2) {
      mn5 = mn5*2;
  }
}