int main1(int c){
  int ki, ry6, fwl, p6;
  ki=c-8;
  ry6=ki+3;
  fwl=c+3;
  p6=ki;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ki == \at(c,Pre) - 8;
  loop invariant ry6 >= ki;
  loop invariant (ry6 - ki) <= 3;
  loop assigns fwl, p6, c, ry6;
*/
while (ry6>ki) {
      fwl = fwl*3;
      p6 = p6/3;
      c = c+(p6%8);
      ry6 = ki;
  }
}