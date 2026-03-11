int main1(int z,int g){
  int k4k, ado, a, fb, j6;
  k4k=g+8;
  ado=k4k;
  a=0;
  fb=0;
  j6=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ado == k4k;
  loop invariant (a == 0 && fb == 0) || (fb == k4k - a);
  loop invariant z == (\at(z, Pre) + a * ado);
  loop invariant 0 <= a;
  loop invariant k4k == g + 8;
  loop invariant 0 <= fb;
  loop assigns a, z, fb;
*/
while (a<k4k) {
      a++;
      z += ado;
      fb = k4k-a;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j6 + ado == g + k4k;
  loop invariant j6 >= g;
  loop assigns j6, z, ado;
*/
while (ado>0) {
      j6++;
      z += j6;
      ado = ado - 1;
  }
}