int main1(){
  int pt, e1fd, wz, d;
  pt=1;
  e1fd=1;
  wz=pt;
  d=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pt == 1;
  loop invariant e1fd == (1 << (wz - 1));
  loop invariant e1fd >= 1;
  loop invariant wz >= 1;
  loop invariant d <= -4 * wz;
  loop assigns d, e1fd, wz;
*/
while (1) {
      if (!(e1fd < pt)) {
          break;
      }
      d = ((d%3)+1)+(d*4);
      e1fd = e1fd * 2;
      wz++;
  }
}