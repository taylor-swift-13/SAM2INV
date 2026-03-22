int main1(int l){
  int kf, vr, i8, f;
  kf=0;
  vr=0;
  i8=0;
  f=(l%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i8 == vr;
  loop invariant kf == i8;
  loop invariant f <= ((\at(l, Pre) % 18) + 5);
  loop invariant vr >= 0;
  loop invariant l >= \at(l, Pre);
  loop assigns f, i8, vr, kf, l;
*/
while (f>0) {
      f--;
      kf = kf+l*l;
      i8 = i8+l*l;
      vr = vr+l*l;
      l = l + kf;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vr >= 0;
  loop invariant l >= \at(l, Pre);
  loop invariant i8 <= kf;
  loop invariant i8 >= 0;
  loop assigns f, i8, vr, l;
*/
while (i8>vr) {
      i8 -= vr;
      vr++;
      l += vr;
      f += l;
  }
}