int main1(){
  int i, khm, vt, xcb;
  i=1+13;
  khm=0;
  vt=i;
  xcb=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xcb == khm*(khm+1)/2;
  loop invariant (khm == 0) ==> (vt == i);
  loop invariant (0 <= khm);
  loop invariant (khm <= i);
  loop assigns vt, khm, xcb;
*/
while (1) {
      if (!(khm<=i-1)) {
          break;
      }
      vt = i-khm;
      khm += 1;
      xcb += khm;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xcb >= 0;
  loop invariant (0 <= khm);
  loop invariant (khm <= i);
  loop invariant (xcb < i) ==> ((i - xcb) % 2 == 0);
  loop assigns vt, xcb;
*/
while (xcb<i) {
      vt = i-xcb;
      xcb += 2;
      vt += khm;
  }
}