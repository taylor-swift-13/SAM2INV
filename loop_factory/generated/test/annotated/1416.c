int main1(){
  int h, pw7, zdzt, ouzw;
  h=137;
  pw7=0;
  zdzt=0;
  ouzw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ouzw == pw7 * (pw7 + 1) / 2;
  loop invariant zdzt == pw7 * h;
  loop invariant h == 137;
  loop invariant 0 <= pw7;
  loop invariant pw7 <= h;
  loop assigns pw7, ouzw, zdzt;
*/
while (pw7 < h) {
      pw7++;
      ouzw += pw7;
      zdzt += h;
  }
}