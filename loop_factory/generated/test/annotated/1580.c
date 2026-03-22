int main1(){
  int u0f, ah, c4q, lfd0, hivv, z, lzf, sq, yk, hz;
  u0f=1*3;
  ah=0;
  c4q=u0f;
  lfd0=0;
  hivv=ah;
  z=1;
  lzf=ah;
  sq=ah;
  yk=0;
  hz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c4q - hivv == 3;
  loop invariant hivv >= 0;
  loop invariant (hivv % 4) == 0;
  loop invariant z >= 1;
  loop invariant lzf >= 0;
  loop invariant sq >= 0;
  loop invariant ah <= u0f;
  loop invariant hivv + lfd0 == 0;
  loop invariant c4q >= 3;
  loop invariant hz <= 0;
  loop invariant ah == 0;
  loop invariant yk == 0;
  loop invariant u0f <= 3;
  loop invariant u0f >= 0;
  loop assigns lfd0, c4q, z, lzf, hz, hivv, sq, yk, u0f;
*/
while (ah+1<=u0f) {
      lfd0 -= 4;
      c4q += 4;
      if (c4q<yk+4) {
          z += 4;
      }
      if (lzf<hivv+3) {
          lzf += 1;
      }
      hz += lfd0;
      hivv += 4;
      z = z + hivv;
      lzf = (z)+(lzf);
      if (z+4<u0f) {
          sq = sq + hivv;
      }
      else {
          yk = yk + ah;
      }
      u0f = (ah+1)-1;
  }
}