int main1(int t,int m){
  int kf, s8, k8, r, de2, q;
  kf=46;
  s8=kf;
  k8=0;
  r=1;
  de2=s8;
  q=kf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant de2 == kf + k8*(k8+1)/2;
  loop invariant r == 1 + k8*(k8-1)/2;
  loop invariant 0 <= k8 <= kf;
  loop assigns r, de2, k8;
*/
while (1) {
      if (!(k8<=kf-1)) {
          break;
      }
      r = r + k8;
      k8++;
      de2 = de2 + k8;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k8 >= 0;
  loop invariant de2 >= 0;
  loop invariant k8 <= q;
  loop assigns k8, de2, t;
*/
while (de2<q) {
      k8 = q-de2;
      de2 += 1;
      t = t + s8;
  }
}