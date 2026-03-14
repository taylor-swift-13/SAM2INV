int main1(){
  int f6, xre, sn, x5, i;
  f6=110;
  xre=f6;
  sn=4;
  x5=0;
  i=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f6 == 110;
  loop invariant xre >= 110;
  loop invariant x5 >= 0;
  loop invariant i == 6 + 110*(xre - 110) + ((xre - 110)*(xre - 111))/2;
  loop invariant sn - i >= -2;
  loop assigns i, x5, sn, xre;
*/
while (xre-5>=0) {
      i = i + xre;
      x5 = x5+sn*xre;
      sn = sn + i;
      xre += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xre == 111;
  loop invariant i >= 116;
  loop invariant sn >= xre + 4;
  loop invariant f6 == 110;
  loop invariant x5 == 0;
  loop assigns f6, x5, i, sn;
*/
while (xre+5<=sn) {
      f6 = f6 + x5;
      x5 = x5*2;
      i = i+(f6%8);
      sn = (xre+5)-1;
  }
}