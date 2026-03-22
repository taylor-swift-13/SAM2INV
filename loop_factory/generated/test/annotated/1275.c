int main1(){
  int fe8, p3, o, rxwd;
  fe8=(1%7)+15;
  p3=fe8;
  o=0;
  rxwd=fe8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == rxwd * (p3 - fe8);
  loop invariant p3 >= fe8/2;
  loop invariant p3 >= fe8;
  loop invariant o >= 0;
  loop assigns o, p3;
*/
while (p3-1>=0) {
      if (!(!(p3<fe8/2))) {
          o = o + 1;
      }
      else {
          o = o + rxwd;
      }
      p3++;
  }
}