int main1(int w){
  int bq5, ep, f098, ljt;
  bq5=40;
  ep=0;
  f098=1;
  ljt=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f098 == (ep + 1) * (ep + 1);
  loop invariant ljt == 1 + 2*ep;
  loop invariant ep >= 0;
  loop assigns ljt, ep, f098, w;
*/
while (f098<=bq5) {
      ljt += 2;
      ep = ep + 1;
      f098 += ljt;
      w = w + f098;
  }
}