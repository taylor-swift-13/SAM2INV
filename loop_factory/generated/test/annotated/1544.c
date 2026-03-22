int main1(){
  int l, u, wqih, ey, it5, gl, z, u86, m;
  l=1*4;
  u=0;
  wqih=l;
  ey=-2;
  it5=u;
  gl=l;
  z=8;
  u86=0;
  m=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u;
  loop invariant u <= l;
  loop invariant ey   == -2 - (u / 2);
  loop invariant it5 == 2 * (u/2);
  loop invariant gl == l - 2 * (u/2);
  loop invariant m == 6;
  loop invariant u86 >= 0;
  loop invariant l == 4;
  loop invariant z >= 8 + u;
  loop invariant wqih == 4 + u/2;
  loop invariant 0 <= u && u <= l
                   && wqih == l + u/2
                   && ey == -2 - u/2
                   && gl == l - 2*(u/2)
                   && m == 6;
  loop assigns u, wqih, ey, it5, gl, u86, z;
*/
while (u < l) {
      u = u + 1;
      if ((u % 2) == 0) {
          wqih = wqih + 1;
          ey--;
      }
      if (!(!((u % 2) != 0))) {
          m = m;
      }
      else {
          it5 += 2;
          gl -= 2;
      }
      u86 += it5;
      z += 1;
      u86 += z;
      z = z + u;
      if ((u%7)==0) {
          z = z + u;
      }
  }
}