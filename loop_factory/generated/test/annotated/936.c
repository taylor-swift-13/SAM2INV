int main1(){
  int m70, oq2, owt, g, q8r;
  m70=(1%14)+8;
  oq2=0;
  owt=0;
  g=m70;
  q8r=oq2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q8r == (owt/2) * ((owt/2) + 1);
  loop invariant 0 <= owt <= m70 + 1;
  loop invariant 0 <= g;
  loop invariant g <= m70;
  loop invariant owt % 2 == 0;
  loop assigns owt, g, q8r;
*/
while (owt<m70) {
      owt += 2;
      if (!(!(q8r<=g))) {
          g = q8r;
      }
      q8r += owt;
  }
}