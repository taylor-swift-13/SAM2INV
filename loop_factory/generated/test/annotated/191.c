int main1(int h){
  int ds;
  ds=-16273;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h <= \at(h, Pre);
  loop invariant ds % 2 != 0;
  loop invariant ds <= -16273;
  loop assigns ds, h;
*/
while (ds+8<0) {
      ds = ds+ds+2;
      ds += 1;
      h = h + ds;
  }
}