int main1(int t){
  int r44, b, mw, fyp, s;
  r44=(t%40)+5;
  b=r44;
  mw=1;
  fyp=0;
  s=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fyp == (mw-1)*(mw-1);
  loop invariant s == (mw-1)*(b+1) - 1;
  loop invariant b == r44;
  loop invariant 0 <= mw - 1;
  loop invariant r44 == ((\at(t, Pre) % 40) + 5);
  loop assigns fyp, s, mw;
*/
while (mw<=r44) {
      fyp = fyp+2*mw-1;
      s += b;
      mw = mw + 1;
      s++;
  }
}