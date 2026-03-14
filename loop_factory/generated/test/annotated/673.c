int main1(){
  int wl, t3, lgl, popt, x, in4;
  wl=1;
  t3=wl;
  lgl=3;
  popt=-3;
  x=0;
  in4=t3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == t3 * (popt + 3);
  loop invariant lgl == popt + 6;
  loop invariant in4 == t3 + 2 * (popt + 3);
  loop invariant wl == 1;
  loop invariant popt <= wl;
  loop assigns x, popt, lgl, in4;
*/
while (popt<wl) {
      x = x + t3;
      popt++;
      lgl++;
      in4 += 2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wl >= 1;
  loop invariant lgl >= popt;
  loop invariant popt == 1;
  loop invariant x == 4 + ((wl - 1) * (wl + 2)) / 2;
  loop assigns x, wl, lgl;
*/
while (popt+1<=lgl) {
      if (popt%2==0) {
          x = x + wl;
      }
      else {
          x = x+wl+1;
      }
      wl = wl + popt;
      lgl = ((popt+1))+(-(1));
  }
}