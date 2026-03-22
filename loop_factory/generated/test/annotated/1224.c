int main1(){
  int mm, xt7v, qv, vgg, d0;
  mm=1;
  xt7v=mm;
  qv=0;
  vgg=mm;
  d0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vgg == 1 + 4*d0;
  loop invariant xt7v >= 1;
  loop invariant qv >= 0;
  loop invariant 0 <= d0;
  loop invariant d0 <= mm + 1;
  loop assigns xt7v, qv, d0, vgg;
*/
while (d0<=mm) {
      xt7v = xt7v + qv;
      qv += vgg;
      xt7v = xt7v*3;
      d0++;
      qv = qv/3;
      vgg += 4;
  }
}