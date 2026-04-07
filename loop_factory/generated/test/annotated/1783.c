int main1(){
  int dat, md1g, x, cn;
  dat=(1%60)+60;
  md1g=(1%9)+2;
  x=0;
  cn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= cn < md1g;
  loop invariant x >= 0;
  loop invariant dat >= md1g * x + cn;
  loop assigns dat, x, cn;
*/
while (1) {
      if (dat<=md1g*x+cn) {
          break;
      }
      if (cn==md1g-1) {
          cn = 0;
          x = x + 1;
      }
      else {
          cn += 1;
      }
      dat = dat + cn;
  }
}