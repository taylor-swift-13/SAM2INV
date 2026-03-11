int main1(int c,int j){
  int y9m, bcgz, d, ta4;
  y9m=j+19;
  bcgz=y9m;
  d=0;
  ta4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(c, Pre) + ta4*(ta4+1)/2;
  loop invariant d == ta4*c - ta4*(ta4+1)*(2*ta4+1)/6;
  loop assigns ta4, d, c;
*/
while (1) {
      if (!(ta4<y9m)) {
          break;
      }
      ta4++;
      d = d + c;
      c = c + ta4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(j, Pre) + (bcgz - y9m) * y9m + (bcgz - y9m) * (bcgz - y9m + 1) / 2;
  loop invariant bcgz >= y9m;
  loop invariant j == \at(j, Pre) +
                   (bcgz - y9m) * y9m +
                   ((bcgz - y9m) * ((bcgz - y9m) + 1)) / 2;
  loop assigns bcgz, d, j;
*/
while (1) {
      if (!(bcgz<y9m)) {
          break;
      }
      bcgz += 1;
      d = d + c;
      j += bcgz;
  }
}