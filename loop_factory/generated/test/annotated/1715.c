int main1(){
  int jf2x, e25, wq36, r0f8, zh;
  jf2x=10;
  e25=0;
  wq36=jf2x;
  r0f8=-6;
  zh=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zh == 8 + 3*e25;
  loop invariant r0f8 == -6;
  loop invariant wq36 >= 10;
  loop invariant 0 <= e25 <= jf2x + 1;
  loop invariant (e25 <= 9) ==> (wq36 == 10);
  loop invariant (jf2x == 10);
  loop assigns e25, wq36, r0f8, zh;
*/
while (e25 <= jf2x) {
      e25 = e25 + 1;
      wq36 = wq36 + (e25 >= jf2x);
      r0f8 = r0f8+wq36-wq36;
      zh = zh + 3;
  }
}