int main1(int t){
  int g, e, mh0, sw, a5;
  g=47;
  e=g;
  mh0=18;
  sw=1;
  a5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == a5 + 47;
  loop invariant sw == a5 + 1;
  loop invariant a5 >= 0;
  loop invariant a5 <= g;
  loop invariant mh0 <= 18;
  loop invariant e == g + a5;
  loop invariant -g <= mh0;
  loop assigns mh0, e, sw, a5;
*/
while (mh0>0&&sw<=g) {
      if (!(mh0<=sw)) {
          mh0 = 0;
      }
      else {
          mh0 -= sw;
      }
      e += 1;
      sw = sw + 1;
      a5 = a5 + 1;
  }
}