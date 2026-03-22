int main1(int o){
  int jkg3, s, w14;
  jkg3=(o%9)+20;
  s=jkg3+6;
  w14=o;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jkg3 == ((\at(o,Pre)) % 9) + 20;
  loop invariant (s - jkg3) % 3 == 0;
  loop invariant s >= jkg3;
  loop invariant s <= jkg3 + 6;
  loop assigns w14, s;
*/
while (1) {
      if (!(s>=jkg3+1)) {
          break;
      }
      w14 = w14*3;
      s = s - 3;
  }
}