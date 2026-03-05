int main1(int v){
  int wgy, s;
  wgy=40;
  s=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == \at(v, Pre);
  loop invariant wgy == 40;
  loop invariant s >= 0;
  loop invariant s % 2 == 0;
  loop invariant s <= 2*wgy + 2;
  loop assigns s;
*/
while (s<=wgy) {
      s++;
      s = s + s;
  }
}