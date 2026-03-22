int main1(int e){
  int p, yq, ymv, kd, xbm;
  p=69;
  yq=-5;
  ymv=0;
  kd=p;
  xbm=yq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 69;
  loop invariant kd == p;
  loop invariant yq <= p;
  loop invariant (kd - p) == ymv;
  loop invariant xbm == -5 || xbm == -1;
  loop assigns yq, ymv, kd, xbm;
*/
for (; yq+1<=p; yq = yq + 1) {
      ymv = ymv*2;
      kd += ymv;
      xbm = xbm%2;
  }
}