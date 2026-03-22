int main1(int k){
  int ga, rjt, q;
  ga=78;
  rjt=1;
  q=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q >= 0;
  loop invariant rjt >= 1;
  loop invariant k == \at(k, Pre) + 2*rjt - 2 + q;
  loop assigns k, q, rjt;
*/
while (rjt<ga) {
      rjt = 2*rjt;
      q = (1)+(q);
      k += rjt;
      k += 1;
  }
}