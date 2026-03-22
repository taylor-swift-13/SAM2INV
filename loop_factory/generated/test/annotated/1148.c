int main1(){
  int u, ob5, aba, p67, n2, rs9;
  u=1*4;
  ob5=0;
  aba=-6;
  p67=ob5;
  n2=u;
  rs9=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aba >= -6;
  loop invariant rs9 >= 0;
  loop invariant n2 == p67 + 4;
  loop invariant p67 >= 0;
  loop assigns n2, aba, p67, rs9;
*/
while (1) {
      if (!(rs9>0)) {
          break;
      }
      n2 = n2+rs9*rs9;
      aba = aba+p67*p67;
      p67 = p67+rs9*rs9;
      rs9 -= 1;
      aba = (p67)+(aba);
  }
}