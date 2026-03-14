int main1(){
  int c54, f, p, ewk;
  c54=1+6;
  f=0;
  p=0;
  ewk=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == p;
  loop invariant p <= c54;
  loop invariant 0 <= p;
  loop assigns f, p;
*/
while (1) {
      if (!(p<c54)) {
          break;
      }
      f = f + 1;
      p++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == p;
  loop invariant p >= 0;
  loop assigns f, p;
*/
while (p<ewk) {
      p++;
      f = f + 1;
  }
}