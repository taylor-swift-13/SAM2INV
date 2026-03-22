int main1(int e,int p){
  int ea, dvp, u15;
  ea=8;
  dvp=0;
  u15=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (e - p) == (\at(e,Pre) - \at(p,Pre));
  loop invariant ea >= dvp + 3;
  loop invariant dvp == 0;
  loop invariant u15 <= 0;
  loop invariant u15 % 4 == 0;
  loop assigns e, p, ea, u15;
*/
while (dvp+4<=ea) {
      e = (ea-dvp)+(e);
      u15 -= 4;
      p = p+ea-dvp;
      ea = (dvp+4)-1;
  }
}