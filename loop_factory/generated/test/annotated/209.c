int main1(){
  int hwvc, mfo7, fr;
  hwvc=1+12;
  mfo7=hwvc;
  fr=mfo7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hwvc == 13;
  loop invariant fr == 0 || fr == hwvc;
  loop invariant mfo7 == hwvc;
  loop assigns fr;
*/
while (mfo7-4>=0) {
      fr += fr;
      fr -= fr;
  }
}