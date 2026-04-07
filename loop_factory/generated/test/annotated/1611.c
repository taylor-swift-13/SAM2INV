int main1(){
  int mx9, myo, bd, g;
  mx9=30;
  myo=1;
  bd=0;
  g=mx9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == mx9 * myo;
  loop invariant bd == (myo - 1) * (myo - 1);
  loop invariant 1 <= myo;
  loop invariant myo <= mx9 + 1;
  loop assigns bd, g, myo;
*/
while (myo<=mx9) {
      bd = (bd+2*myo)+(-(1));
      myo += 1;
      g += mx9;
  }
}