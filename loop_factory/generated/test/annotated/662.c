int main1(int j,int s){
  int xq, t6, ttr, x5, c7tm;
  xq=s;
  t6=0;
  ttr=0;
  x5=0;
  c7tm=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ttr == j * x5;
  loop invariant xq == s;
  loop assigns ttr, x5;
*/
while (x5<=xq-1) {
      ttr += j;
      x5 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (t6 == 0) ==> (c7tm == s);
  loop invariant (t6 == xq) ==> (c7tm == s + x5 * xq);
  loop invariant (t6 == 0) || (t6 == xq);
  loop assigns c7tm, t6;
*/
while (xq+1<=t6) {
      c7tm = c7tm+x5*xq;
      t6 = (xq+1)-1;
  }
}