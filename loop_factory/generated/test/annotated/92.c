int main1(int c,int e){
  int a, s2, sl;
  a=c;
  s2=1;
  sl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(c,Pre);
  loop invariant c == \at(c,Pre) + sl;
  loop invariant e == \at(e,Pre) + sl * (sl + 1) / 2;
  loop invariant sl >= 0;
  loop invariant s2 >= 1;
  loop assigns s2, sl, c, e;
*/
while (s2<=a) {
      s2 = 2*s2;
      sl++;
      c = (1)+(c);
      e = e + sl;
  }
}