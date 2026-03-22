int main1(int w){
  int f2ul, v, p2a;
  f2ul=(w%27)+17;
  v=0;
  p2a=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f2ul - v == ((w % 27) + 17);
  loop invariant v >= 0;
  loop invariant f2ul - v == \at(w,Pre) % 27 + 17;
  loop invariant p2a >= 5;
  loop assigns f2ul, p2a, v;
*/
while (v > 0 && f2ul > 0) {
      v -= 1;
      f2ul = f2ul - 1;
      p2a += v;
  }
}