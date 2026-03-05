int main1(){
  int sa, h, c2, s;
  sa=1+24;
  h=0;
  c2=0;
  s=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c2 == h + h/4;
  loop invariant s == h % 4;
  loop invariant 0 <= h;
  loop invariant h <= sa;
  loop invariant sa == 25;
  loop assigns c2, s, h;
*/
while (h<sa) {
      c2 += 1;
      s++;
      if (s>=4) {
          s -= 4;
          c2 += 1;
      }
      h += 1;
  }
}