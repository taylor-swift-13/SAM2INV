int main1(int f,int z){
  int q, l, e1, li, j9q, t821, xs3;
  q=f;
  l=0;
  e1=1;
  li=0;
  j9q=z;
  t821=-2;
  xs3=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xs3 - 3*z == -2 * \at(z, Pre);
  loop invariant q == \at(f, Pre);
  loop invariant 0 <= l;
  loop invariant l <= 3;
  loop invariant e1 >= 1;
  loop invariant 0 <= li;
  loop invariant li <= e1;
  loop invariant f >= q;
  loop invariant j9q >= \at(z,Pre);
  loop invariant t821 >= -2;
  loop invariant z >= \at(z,Pre);
  loop assigns l, j9q, li, e1, xs3, f, t821, z;
*/
while (1) {
      if (!(l>=0&&l<3)) {
          break;
      }
      if (!(!(l==0&&e1>=q))) {
          l = 3;
      }
      else {
          if (l==1&&li<e1) {
              j9q = j9q+e1-li;
              li = li + 1;
          }
          else {
              if (l==1&&li>=e1) {
                  l = 2;
              }
              else {
                  if (l==2) {
                      e1 = e1 + 1;
                      l = 0;
                  }
              }
          }
      }
      xs3 = xs3 + 3;
      f = f + li;
      t821 += e1;
      z += 1;
  }
}