int main1(){
  int ob, f5, ib6k, i8hz;
  ob=57;
  f5=ob;
  ib6k=ob;
  i8hz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ib6k == 57;
  loop invariant i8hz == ib6k * ((57 - f5) / 57);
  loop invariant ob == 57;
  loop invariant f5 >= 0;
  loop invariant f5 <= 57;
  loop assigns i8hz, f5;
*/
while (f5>0) {
      i8hz += ib6k;
      f5 = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ib6k == 57;
  loop invariant i8hz == ob;
  loop invariant ob <= ib6k;
  loop invariant ob >= 57;
  loop assigns i8hz, ob;
*/
while (1) {
      if (!(ob<ib6k)) {
          break;
      }
      i8hz = i8hz + 1;
      ob += 1;
  }
}