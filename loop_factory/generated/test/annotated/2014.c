int main1(){
  int kb0p, li, x, aw, s2, w2;
  kb0p=1;
  li=0;
  x=5;
  aw=li;
  s2=kb0p;
  w2=kb0p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s2 == kb0p + li * w2;
  loop invariant s2 == (1 + li * w2);
  loop invariant (0 <= li && li <= kb0p);
  loop invariant w2 == 1;
  loop invariant 0 <= kb0p;
  loop invariant w2 == kb0p;
  loop invariant (aw >= 0);
  loop invariant (x >= s2);
  loop assigns x, li, s2, aw;
*/
while (1) {
      if (!(li<kb0p)) {
          break;
      }
      x = aw+s2+w2;
      li = li + 1;
      s2 = s2 + w2;
      aw += x;
  }
}