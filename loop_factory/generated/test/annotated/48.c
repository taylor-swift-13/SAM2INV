int main1(int t,int i){
  int b, mow;
  b=(i%32)+13;
  mow=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(i, Pre) % 32 + 13;
  loop invariant mow % 4 == 0;
  loop invariant mow >= 0;
  loop invariant (b >= 0 ==> mow <= b + 3) && i == \at(i, Pre) && t == \at(t, Pre);
  loop assigns mow;
*/
while (mow<b) {
      mow += 4;
  }
}