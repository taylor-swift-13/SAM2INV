int main1(){
  int an, a6, w0;
  an=1;
  a6=0;
  w0=an;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (a6 <= an);
  loop invariant (w0 >= 1);
  loop invariant (an >= 1);
  loop invariant w0 >= (an - a6);
  loop invariant w0 <= (an - a6) + 2;
  loop assigns w0, a6;
*/
while (a6<an) {
      w0 = an-a6;
      a6++;
      if (w0+6<an) {
          w0 += 1;
      }
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (a6 >= 0);
  loop invariant a6 <= an;
  loop assigns an;
*/
while (1) {
      if (!(an<=a6-1)) {
          break;
      }
      an = an + 1;
  }
}