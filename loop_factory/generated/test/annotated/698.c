int main1(){
  int z9p, c, ck2, fn;
  z9p=0;
  c=0;
  ck2=0;
  fn=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == ck2;
  loop invariant fn == 6 - c;
  loop invariant 0 <= c <= 6;
  loop invariant z9p >= 0;
  loop assigns z9p, c, ck2, fn;
*/
while (fn>=1) {
      z9p = z9p+1*1;
      c = c+1*1;
      ck2 = ck2+1*1;
      fn = (fn)+(-(1));
      z9p = z9p*z9p+z9p;
  }
}