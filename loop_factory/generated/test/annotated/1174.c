int main1(){
  int c9, pi9s, wx83, g, chd, j2, qlvt;
  c9=1+4;
  pi9s=c9+2;
  wx83=(1%60)+60;
  g=(1%9)+2;
  chd=0;
  j2=0;
  qlvt=c9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qlvt == c9 + (g*chd + j2) * pi9s;
  loop invariant (0 <= j2);
  loop invariant (j2 < g);
  loop invariant chd >= 0;
  loop assigns qlvt, j2, chd;
*/
while (wx83>g*chd+j2) {
      if (j2==g-1) {
          j2 = 0;
          chd = chd + 1;
      }
      else {
          j2 = j2 + 1;
      }
      qlvt = qlvt + pi9s;
  }
}