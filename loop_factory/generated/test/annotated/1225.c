int main1(int r,int l){
  int qs3, ar, krk, k8, a8, aj;
  qs3=r;
  ar=r;
  krk=0;
  k8=-4;
  a8=-3;
  aj=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k8 == 4*a8 + 8;
  loop invariant krk == 2*a8*a8 + 6*a8;
  loop invariant l == \at(l, Pre);
  loop invariant aj == -6 + 4*(a8 + 3)*(a8 + 2);
  loop invariant ar == \at(r, Pre) + (2 * (a8 + 3) * (a8 + 2) * (a8 - 2)) / 3;
  loop assigns ar, krk, a8, k8, r, aj;
*/
while (a8<=qs3) {
      ar += krk;
      krk = krk + k8;
      a8 = a8 + 1;
      k8 += 4;
      r = r+a8+ar;
      aj = aj+k8+k8;
  }
}