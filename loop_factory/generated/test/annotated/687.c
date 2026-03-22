int main1(){
  int wc, q, ub7a, cwix;
  wc=1;
  q=(1%40)+2;
  ub7a=0;
  cwix=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wc == 1;
  loop invariant 0 <= cwix;
  loop invariant ((q == 1) || (q == 3)) && ((q == 3) ==> (ub7a == 0));
  loop assigns cwix, q, ub7a;
*/
while (q!=ub7a) {
      ub7a = q;
      q = (q+wc/q)/2;
      cwix = cwix + q;
  }
}