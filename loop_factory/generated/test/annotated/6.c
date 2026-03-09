int main1(){
  int bvv, s, zn, sy;
  bvv=63;
  s=0;
  zn=0;
  sy=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 0;
  loop invariant bvv == 63;
  loop invariant sy == -8 + zn * s;
  loop invariant 0 <= zn;
  loop invariant zn <= bvv;
  loop assigns sy, zn;
*/
while (1) {
      if (!(zn<=bvv-1)) {
          break;
      }
      sy = sy + s;
      zn++;
  }
}