int main1(int d){
  int ip, sy;
  ip=d+25;
  sy=ip+3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ip == d + 25;
  loop invariant (sy == ip + 3) || (sy == ip);
  loop assigns sy;
*/
while (1) {
      if (!(sy>ip)) {
          break;
      }
      sy = sy - 3;
  }
}