int main1(int k,int f){
  int luv, qy6, g1, qoi, l, dx, pz;
  luv=53;
  qy6=0;
  g1=0;
  qoi=0;
  l=0;
  dx=4;
  pz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pz == qy6;
  loop invariant 0 <= qoi <= qy6;
  loop invariant 0 <= l <= qy6;
  loop invariant 0 <= qy6 <= luv;
  loop invariant g1 >= 0;
  loop invariant g1 <= dx;
  loop invariant g1 + l - qoi == 0;
  loop invariant 0 <= g1;
  loop assigns g1, l, qoi, pz, qy6;
*/
for (; qy6<=luv-1; qy6 = qy6 + 1) {
      if (qy6%3==0) {
          if (g1>0) {
              g1 = g1 - 1;
              l = l + 1;
          }
      }
      else {
          if (g1<dx) {
              g1 += 1;
              qoi += 1;
          }
      }
      pz = pz + 1;
  }
}