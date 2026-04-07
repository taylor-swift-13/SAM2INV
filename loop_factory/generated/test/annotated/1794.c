int main1(){
  int qf, k63, s, h, l5;
  qf=(1%20)+14;
  k63=3;
  s=-6;
  h=1+1;
  l5=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l5 == 3;
  loop invariant -12 * k63 == 7 * s + 6;
  loop invariant s <= -6;
  loop invariant qf == 15;
  loop invariant 0 <= h - 2 <= qf - 2;
  loop assigns h, k63, s;
*/
while (1) {
      if (h>=qf) {
          break;
      }
      h += 1;
      k63 = k63*l5+1;
      s = s*l5;
  }
}