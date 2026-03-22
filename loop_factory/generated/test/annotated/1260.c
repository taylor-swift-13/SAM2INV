int main1(){
  int aiao, b9q, or, b2, qb, pk, c6;
  aiao=1+3;
  b9q=0;
  or=aiao;
  b2=2;
  qb=b9q;
  pk=(1%6)+2;
  c6=b9q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (pk > 0);
  loop invariant (aiao >= 0);
  loop invariant qb <= aiao;
  loop invariant b2 > 0;
  loop invariant or > 0;
  loop invariant c6 == 0;
  loop invariant b9q == 0;
  loop invariant 0 <= qb;
  loop invariant (pk == 3) || (pk % 4 == 0);
  loop assigns qb, or, b2, pk, c6;
*/
while (1) {
      if (qb>=aiao) {
          break;
      }
      qb++;
      or = or*pk+1;
      b2 = b2*pk;
      pk += b9q;
      pk = pk*4;
      c6 = c6/4;
  }
}