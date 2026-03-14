int main1(int e){
  int c, jmln, r3, i, wl, s;
  c=e;
  jmln=0;
  r3=23;
  i=0;
  wl=1;
  s=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r3 + i == 23;
  loop invariant 0 <= r3;
  loop invariant 1 <= wl;
  loop invariant jmln >= 0;
  loop invariant wl == jmln + 1;
  loop invariant 0 <= i <= 23;
  loop assigns r3, wl, i, jmln, s;
*/
while (1) {
      if (!(r3>0&&jmln<c)) {
          break;
      }
      if (r3<=wl) {
          s = r3;
      }
      else {
          s = wl;
      }
      r3 = r3 - s;
      wl += 1;
      i = i + s;
      jmln++;
  }
}