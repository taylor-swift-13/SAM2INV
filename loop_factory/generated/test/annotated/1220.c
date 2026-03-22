int main1(){
  int q, b, id, zq, pd;
  q=76;
  b=0;
  id=1;
  zq=6;
  pd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zq == 6 + 4*pd;
  loop invariant b % 2 == 0;
  loop invariant id >= 0;
  loop invariant 0 <= pd <= q + 1;
  loop invariant id <= zq;
  loop invariant q == 76;
  loop assigns b, pd, id, zq;
*/
while (1) {
      if (!(pd<=q)) {
          break;
      }
      b = b + id;
      pd += 1;
      id = id + zq;
      b = b*2;
      zq += 4;
      id = id/2;
  }
}