int main1(int s){
  int of, w6, kk5;
  of=s;
  w6=of+6;
  kk5=of;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (w6 - of) % 3 == 0;
  loop invariant 0 <= (w6 - of);
  loop invariant w6 <= of + 6;
  loop invariant ((w6 - (\at(s, Pre) + 6)) % 3 == 0);
  loop assigns w6;
*/
while (w6>=of+1) {
      w6 = w6 - 3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kk5 == of;
  loop invariant (\at(s, Pre) <= kk5 && kk5 <= of);
  loop assigns kk5;
*/
while (kk5<=of-1) {
      kk5 = kk5 + 1;
  }
}