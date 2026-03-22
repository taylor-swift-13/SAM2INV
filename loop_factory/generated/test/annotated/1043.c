int main1(int f,int d){
  int ijk, rx6, s, faa, m8;
  ijk=d-4;
  rx6=0;
  s=0;
  faa=d;
  m8=ijk;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == rx6*(rx6 - 1)/2;
  loop invariant faa == d + rx6*(rx6 - 1)*(rx6 + 1)/6;
  loop invariant rx6 >= 0;
  loop invariant ijk == d - 4;
  loop invariant s == (rx6 * (rx6 - 1)) / 2;
  loop invariant faa == d + ((rx6 - 1) * rx6 * (rx6 + 1)) / 6;
  loop invariant d == \at(d, Pre);
  loop invariant f == \at(f, Pre);
  loop invariant 2*s == rx6*(rx6-1);
  loop invariant 6*(faa - d) == rx6*(rx6+1)*(rx6-1);
  loop assigns s, faa, rx6;
*/
while (rx6<ijk) {
      s += rx6;
      faa = faa + s;
      rx6 = rx6 + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s >= 0;
  loop invariant m8 == ijk;
  loop invariant ijk == d - 4;
  loop invariant m8 == d - 4;
  loop invariant d == \at(d, Pre);
  loop invariant f == \at(f, Pre);
  loop assigns s;
*/
while (1) {
      if (!(s+1<=m8)) {
          break;
      }
      s++;
  }
}