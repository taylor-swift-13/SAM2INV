int main1(){
  int f, z, fs, qw, x6m;
  f=10;
  z=0;
  fs=f;
  qw=f;
  x6m=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z <= f;
  loop invariant qw == 10;
  loop invariant x6m == 0;
  loop invariant (z == 0 && fs == f) || (z > 0 && fs == z);
  loop invariant qw == f;
  loop assigns z, fs, qw, x6m;
*/
while (z < f) {
      z += 1;
      fs = z;
      qw = qw+0;
      x6m = x6m+0;
  }
}