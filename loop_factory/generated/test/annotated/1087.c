int main1(int c){
  int i, ppm, w, ai, lv, s5o;
  i=c*4;
  ppm=i;
  w=0;
  ai=(c%28)+10;
  lv=i;
  s5o=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ai + w*(w-1)/2 == (\at(c, Pre) % 28) + 10;
  loop invariant s5o == \at(c, Pre) + w*(w+1)/2;
  loop invariant w >= 0;
  loop invariant c >= \at(c, Pre);
  loop invariant lv >= 4 * \at(c, Pre);
  loop assigns ai, w, s5o, c, lv;
*/
while (ai>w) {
      ai = ai - w;
      w += 1;
      s5o = s5o + w;
      c = c+(w%7);
      lv = ((w%3))+(lv);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop assigns lv;
*/
for (; lv+1<=ppm; lv++) {
  }
}