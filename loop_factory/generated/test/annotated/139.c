int main1(){
  int w4b, jrt3;
  w4b=46;
  jrt3=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= jrt3;
  loop invariant jrt3 <= w4b;
  loop invariant w4b == 46;
  loop assigns jrt3;
*/
while (jrt3<w4b) {
      jrt3 = jrt3 + 1;
  }
}