int main1(){
  int tka2, e, uc0, p, h5, u;
  tka2=1*3;
  e=(1%60)+60;
  uc0=(1%9)+2;
  p=0;
  h5=0;
  u=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 1 + tka2 * p;
  loop invariant 0 <= h5 <= uc0;
  loop invariant 0 <= p;
  loop invariant h5 == 0;
  loop assigns h5, p, u;
*/
while (e>uc0*p+h5) {
      if (!(!(h5==uc0-1))) {
          h5++;
      }
      else {
          h5 = 0;
          p++;
      }
      u += tka2;
  }
}