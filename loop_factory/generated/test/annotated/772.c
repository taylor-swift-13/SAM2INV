int main1(){
  int zn, k5g, l1, xwi, qz, bm, k8;
  zn=1*3;
  k5g=zn;
  l1=(1%28)+8;
  xwi=(1%22)+5;
  qz=0;
  bm=k5g;
  k8=zn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l1 % 9 == 0;
  loop invariant qz >= 0;
  loop invariant zn == 3;
  loop invariant l1 > 0;
  loop invariant k8 >= zn;
  loop invariant 0 <= xwi <= 6;
  loop invariant bm >= 3;
  loop assigns qz, xwi, l1, k8, bm;
*/
while (xwi!=0) {
      if (xwi%2==1) {
          qz = qz + l1;
          xwi = xwi - 1;
      }
      l1 = 2*l1;
      xwi = xwi/2;
      k8++;
      bm = bm*3+(l1%6)+1;
  }
}