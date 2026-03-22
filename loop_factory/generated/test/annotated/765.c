int main1(){
  int m, tj, k, f6hh, t, sea;
  m=39;
  tj=(1%28)+8;
  k=(1%22)+5;
  f6hh=0;
  t=13;
  sea=m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 39;
  loop invariant tj % 9 == 0;
  loop invariant 0 <= k <= 6;
  loop invariant sea >= 39;
  loop invariant t >= 13;
  loop invariant tj >= 9;
  loop invariant f6hh >= 0;
  loop assigns f6hh, k, tj, t, sea;
*/
while (1) {
      if (!(k!=0)) {
          break;
      }
      if (k%2==1) {
          f6hh += tj;
          k = k - 1;
      }
      tj = 2*tj;
      k = k/2;
      t = t*4;
      sea = sea*4+(k%6)+2;
  }
}