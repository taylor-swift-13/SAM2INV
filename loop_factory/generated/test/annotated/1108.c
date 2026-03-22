int main1(){
  int s24, okcj, ieq, ra, wxz, vpc7, jr, h;
  s24=77;
  okcj=0;
  ieq=1;
  ra=0;
  wxz=0;
  vpc7=-3;
  jr=16;
  h=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ra == (ieq-1)*(ieq-1);
  loop invariant wxz == okcj*(ieq-1);
  loop invariant jr == 16 + ((ieq-1)*ieq*(2*ieq - 1))/6;
  loop invariant h <= wxz + vpc7 + jr;
  loop invariant 1 <= ieq <= s24 + 1;
  loop invariant wxz >= 0;
  loop assigns ra, wxz, ieq, jr, h;
*/
while (ieq<=s24) {
      ra = ra+2*ieq-1;
      wxz = wxz + okcj;
      ieq++;
      jr = jr + ra;
      h += 1;
      h = wxz+vpc7+jr;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vpc7 == -3 + okcj*(s24 - ra);
  loop invariant (okcj <= s24 + 1);
  loop invariant jr >= 16;
  loop invariant 0 <= okcj;
  loop assigns jr, h, okcj, vpc7;
*/
while (1) {
      if (!(okcj<=s24)) {
          break;
      }
      jr = jr+okcj*okcj;
      h += 1;
      okcj = okcj + 1;
      vpc7 = (vpc7+s24)+(-(ra));
      h = h + 5;
  }
}