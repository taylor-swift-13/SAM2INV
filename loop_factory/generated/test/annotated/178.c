int main1(int t,int k){
  int qo8, me, q, kdxc, l6, mo;
  qo8=k*5;
  me=qo8;
  q=15;
  kdxc=0;
  l6=1;
  mo=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qo8 == \at(k, Pre) * 5;
  loop invariant kdxc + q == 15;
  loop invariant me - qo8 == l6 - 1;
  loop invariant l6 >= 1;
  loop invariant l6 <= 16;
  loop invariant 0 <= mo;
  loop invariant me <= qo8;
  loop invariant mo <= 15;
  loop invariant 0 <= q <= 15;
  loop assigns kdxc, l6, q, me, mo;
*/
while (1) {
      if (!(q>0&&me<qo8)) {
          break;
      }
      if (q<=l6) {
          mo = q;
      }
      else {
          mo = l6;
      }
      kdxc += mo;
      l6 = l6 + 1;
      q -= mo;
      me = me + 1;
  }
}