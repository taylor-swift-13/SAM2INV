int main1(){
  int d2, a, vf, kz, ffaf, kd0u, dj, l8, em;
  d2=77;
  a=0;
  vf=d2;
  kz=-8;
  ffaf=3;
  kd0u=25;
  dj=a;
  l8=0;
  em=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d2 == 77;
  loop invariant 0 <= a;
  loop invariant a <= d2;
  loop invariant em == 0;
  loop invariant l8 == 0;
  loop invariant kz == -8 + 2*a;
  loop invariant kd0u >= 25;
  loop invariant dj == 0;
  loop invariant ffaf >= 3 + a;
  loop invariant kd0u >= 25 + vf * a;
  loop invariant vf == d2;
  loop assigns a, kz, vf, em, ffaf, kd0u, l8;
*/
while (a < d2) {
      a++;
      if (!(em!=0)) {
          kz += 2;
      }
      else {
          vf++;
          em = 1;
      }
      if ((a%2)==0) {
          ffaf += kd0u;
      }
      kd0u += vf;
      ffaf++;
      kd0u = kd0u + ffaf;
      l8 += dj;
  }
}