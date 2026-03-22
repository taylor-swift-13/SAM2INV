int main1(){
  int iogf, a, pk, l9bs, zg, u;
  iogf=1*5;
  a=0;
  pk=0;
  l9bs=0;
  zg=6;
  u=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l9bs == pk * (13 - pk) / 2;
  loop invariant zg == 6 - pk;
  loop invariant 0 <= pk <= iogf;
  loop invariant u == pk*(pk + 1)*(19 - pk)/6;
  loop invariant 0 <= l9bs;
  loop invariant 0 <= u;
  loop invariant zg >= 0;
  loop assigns l9bs, pk, zg, u;
*/
while (pk<iogf&&zg>0) {
      l9bs = l9bs + zg;
      pk = pk + 1;
      zg--;
      u += l9bs;
  }
}