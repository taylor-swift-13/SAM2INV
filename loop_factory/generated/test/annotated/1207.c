int main1(){
  int h9k, k, wnyx, y, o7, jfy, iw, ov8h;
  h9k=1*5;
  k=h9k+2;
  wnyx=(1%35)+15;
  y=(1%35)+15;
  o7=1;
  jfy=0;
  iw=0;
  ov8h=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wnyx >= 0;
  loop invariant y >= 0;
  loop invariant wnyx + y <= 32;
  loop invariant o7 >= 1;
  loop invariant ov8h >= 1;
  loop invariant iw <= 0;
  loop invariant jfy <= 0;
  loop assigns wnyx, o7, iw, y, jfy, ov8h;
*/
while (wnyx!=y) {
      if (wnyx>y) {
          wnyx = wnyx - y;
          o7 = o7 - jfy;
          iw = iw - ov8h;
      }
      else {
          y -= wnyx;
          jfy -= o7;
          ov8h -= iw;
      }
      o7 = o7 + k;
  }
}