int main1(){
  int jsza, c8, ksu, q3m, p, k;
  jsza=1;
  c8=0;
  ksu=1+2;
  q3m=jsza;
  p=0;
  k=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 0;
  loop invariant k == -6;
  loop invariant q3m == jsza;
  loop invariant ksu == 3 + (c8*(c8+1))/2 + 2*q3m*c8;
  loop invariant 0 <= c8 <= jsza;
  loop assigns c8, p, ksu;
*/
while (1) {
      if (!(k != 0 && c8 < jsza)) {
          break;
      }
      c8 += 1;
      p = p % k;
      ksu = ksu + c8;
      ksu = ksu+q3m+q3m;
  }
}