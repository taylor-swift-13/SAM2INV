int main1(){
  int si3, gp, tp, llgq, ll;
  si3=64;
  gp=0;
  tp=1;
  llgq=0;
  ll=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant llgq == (tp - 1) * (tp - 1);
  loop invariant ll == -5 + (tp - 1) * gp;
  loop invariant 1 <= tp;
  loop invariant tp <= si3 + 1;
  loop assigns llgq, ll, tp;
*/
while (tp<=si3) {
      llgq = llgq+2*tp-1;
      ll = ll + gp;
      tp = tp + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= si3;
  loop invariant si3 <= 64;
  loop assigns si3;
*/
while (si3-1>=0) {
      si3 -= 1;
  }
}